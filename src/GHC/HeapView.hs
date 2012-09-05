{-# LANGUAGE CPP #-}
{-|
Module      :  GHC.HeapView
Copyright   :  (c) 2012 Joachim Breitner
License     :  BSD3
Maintainer  :  Joachim Breitner <mail@joachim-breitner.de>

With this module, you can investigate the heap representation of Haskell
values, i.e. to investigate sharing and lazy evaluation.
-}

{-# LANGUAGE MagicHash, UnboxedTuples, CPP, ForeignFunctionInterface, GHCForeignImportPrim, UnliftedFFITypes, BangPatterns, RecordWildCards #-}

module GHC.HeapView (
    -- * Heap data types
    Closure(..),
    allPtrs,
    ClosureType(..),
    StgInfoTable(..),
    HalfWord,
    -- * Reading from the heap
    getClosureData,
    getBoxedClosureData,
    getClosureRaw,
    -- * Boxes
    Box(..),
    asBox,
    )
    where

import GHC.Exts
import GHC.Arr (Array(..))

import GHC.Constants ( wORD_SIZE, tAG_MASK, wORD_SIZE_IN_BITS )

import Foreign
import Numeric          ( showHex )
import Data.Char
import Data.List        ( intersperse )

#include "ghcautoconf.h"

-- | An arbitrarily Haskell value in a safe Box. The point is that even
-- unevaluated thunks can safely be moved around inside the Box, and when
-- required, e.g. in 'getBoxedClosureData', the function knows how far it has
-- to evalue the argument.
data Box = Box Any

#if SIZEOF_VOID_P == 8
type HalfWord = Word32
#else
type HalfWord = Word16
#endif

instance Show Box where
-- From libraries/base/GHC/Ptr.lhs
   showsPrec _ (Box a) rs =
    -- unsafePerformIO (print "↓" >> pClosure a) `seq`    
    pad_out (showHex addr "") ++ (if tag>0 then "/" ++ show tag else "") ++ rs
     where
       ptr  = W# (aToWord# a)
       tag  = ptr .&. fromIntegral tAG_MASK -- ((1 `shiftL` TAG_BITS) -1)
       addr = ptr - tag
        -- want 0s prefixed to pad it out to a fixed length.
       pad_out ls = 
          '0':'x':(replicate (2*wORD_SIZE - length ls) '0') ++ ls

instance Eq Box where
  Box a == Box b = case reallyUnsafePtrEquality# a b of
    1# -> True
    _  -> False

{-|
  This takes an arbitrary value and puts it into a box. Note that calls like

  > asBox (head list) 

  will put the thunk \"head list\" into the box, /not/ the element at the head
  of the list. For that, use careful case expressions:

  > case list of x:_ -> asBox x
-}
asBox :: a -> Box
asBox x = Box (unsafeCoerce# x)

{-
   StgInfoTable parsing derived from ByteCodeItbls.lhs
   Removed the code parameter for now
   Replaced Type by an enumeration
   Remove stuff dependent on GHCI_TABLES_NEXT_TO_CODE
 -}

{-| This is a somewhat faithful representation of an info table. See
   <http://hackage.haskell.org/trac/ghc/browser/includes/rts/storage/InfoTables.h>
   for more details on this data structure. Note that the 'Storable' instance
   provided here does _not_ support writing.
 -}
data StgInfoTable = StgInfoTable {
   ptrs   :: HalfWord,
   nptrs  :: HalfWord,
   tipe   :: ClosureType,
   srtlen :: HalfWord
  }
  deriving (Show)

instance Storable StgInfoTable where

   sizeOf itbl 
      = sum
        [
         fieldSz ptrs itbl,
         fieldSz nptrs itbl,
         sizeOf (undefined :: HalfWord),
         fieldSz srtlen itbl
        ]

   alignment _ 
      = wORD_SIZE

   poke _a0 _itbl
      = error "Storable StgInfoTable is read-only"

   peek a0
      = runState (castPtr a0)
      $ do
           ptrs'   <- load
           nptrs'  <- load
           tipe'   <- load
           srtlen' <- load
           return 
              StgInfoTable { 
                 ptrs   = ptrs',
                 nptrs  = nptrs',
                 tipe   = toEnum (fromIntegral (tipe'::HalfWord)),
                 srtlen = srtlen'
              }

fieldSz :: (Storable a, Storable b) => (a -> b) -> a -> Int
fieldSz sel x = sizeOf (sel x)

load :: Storable a => PtrIO a
load = do addr <- advance
          lift (peek addr)

type PtrIO = State (Ptr Word8) IO

advance :: Storable a => PtrIO (Ptr a)
advance = State adv where
    adv addr = case castPtr addr of { addrCast -> return
        (addr `plusPtr` sizeOfPointee addrCast, addrCast) }

sizeOfPointee :: (Storable a) => Ptr a -> Int
sizeOfPointee addr = sizeOf (typeHack addr)
    where typeHack = undefined :: Ptr a -> a

{-
   Embedded StateT, also from ByteCodeItbls
 -}

newtype State s m a = State (s -> m (s, a))

instance Monad m => Monad (State s m) where
  return a      = State (\s -> return (s, a))
  State m >>= k = State (\s -> m s >>= \(s', a) -> case k a of State n -> n s')
  fail str      = State (\_ -> fail str)

lift :: Monad m => m a -> State s m a
lift m = State (\s -> m >>= \a -> return (s, a))

runState :: (Monad m) => s -> State s m a -> m a
runState s (State m) = m s >>= return . snd

{-
   Data Type representing Closures
 -}


{-| A closure type enumeration, in order matching the actual value on the heap.
   Needs to be synchronized with
   <http://hackage.haskell.org/trac/ghc/browser/includes/rts/storage/ClosureTypes.h>
 -}
data ClosureType =
	  INVALID_OBJECT
	| CONSTR
	| CONSTR_1_0
	| CONSTR_0_1
	| CONSTR_2_0
	| CONSTR_1_1
	| CONSTR_0_2
	| CONSTR_STATIC
	| CONSTR_NOCAF_STATIC
	| FUN
	| FUN_1_0
	| FUN_0_1
	| FUN_2_0
	| FUN_1_1
	| FUN_0_2
	| FUN_STATIC
	| THUNK
	| THUNK_1_0
	| THUNK_0_1
	| THUNK_2_0
	| THUNK_1_1
	| THUNK_0_2
	| THUNK_STATIC
	| THUNK_SELECTOR
	| BCO
	| AP
	| PAP
	| AP_STACK
	| IND
	| IND_PERM
	| IND_STATIC
	| RET_BCO
	| RET_SMALL
	| RET_BIG
	| RET_DYN
	| RET_FUN
	| UPDATE_FRAME
	| CATCH_FRAME
	| UNDERFLOW_FRAME
	| STOP_FRAME
	| BLOCKING_QUEUE
	| BLACKHOLE
	| MVAR_CLEAN
	| MVAR_DIRTY
	| ARR_WORDS
	| MUT_ARR_PTRS_CLEAN
	| MUT_ARR_PTRS_DIRTY
	| MUT_ARR_PTRS_FROZEN0
	| MUT_ARR_PTRS_FROZEN
	| MUT_VAR_CLEAN
	| MUT_VAR_DIRTY
	| WEAK
	| PRIM
	| MUT_PRIM
	| TSO
	| STACK
	| TREC_CHUNK
	| ATOMICALLY_FRAME
	| CATCH_RETRY_FRAME
	| CATCH_STM_FRAME
	| WHITEHOLE
 deriving (Show, Eq, Enum, Ord)

{-| This is the main data type of this module, representing a Haskell value on
  the heap. This reflects
  <http://hackage.haskell.org/trac/ghc/browser/includes/rts/storage/Closures.h>
 -}
data Closure =
    ConsClosure {
        info         :: StgInfoTable 
        , ptrArgs    :: [Box]
        , dataArgs   :: [Word]
        , pkg        :: String
        , modl       :: String
        , name       :: String
    } |
    ThunkClosure {
        info         :: StgInfoTable 
        , ptrArgs    :: [Box]
        , dataArgs   :: [Word]
    } |
    SelectorClosure {
        info         :: StgInfoTable 
        , selectee   :: Box
    } |
    IndClosure {
        info         :: StgInfoTable 
        , indirectee   :: Box
    } |
    BlackholeClosure {
        info         :: StgInfoTable 
        , indirectee   :: Box
    } |
    APClosure {
        info         :: StgInfoTable 
        , arity      :: HalfWord
        , n_args     :: HalfWord
        , fun        :: Box
        , payload    :: [Box]
    } |
    PAPClosure {
        info         :: StgInfoTable 
        , arity      :: HalfWord
        , n_args     :: HalfWord
        , fun        :: Box
        , payload    :: [Box]
    } |
    BCOClosure {
        info         :: StgInfoTable 
        , instrs     :: Box
        , literals   :: Box
        , bcoptrs    :: Box
        , arity      :: HalfWord
        , size       :: HalfWord
        , bitmap     :: Word
    } |
    ArrWordsClosure {
        info         :: StgInfoTable 
        , bytes      :: Word
        , arrWords   :: [Word]
    } |
    MutArrClosure {
        info         :: StgInfoTable 
        , mccPtrs    :: Word
        , mccSize    :: Word
        , mccPayload :: [Box]
        -- Card table ignored
    } |
    MutVarClosure {
        info         :: StgInfoTable 
        , var        :: Box
    } |
    MVarClosure {
        info         :: StgInfoTable 
        , queueHead  :: Box
        , queueTail  :: Box
        , value      :: Box
    } |
    FunClosure {
        info         :: StgInfoTable 
        , ptrArgs    :: [Box]
        , dataArgs   :: [Word]
    } |
    BlockingQueueClosure {
        info         :: StgInfoTable 
        , link       :: Box
        , blackHole  :: Box
        , owner      :: Box
        , queue      :: Box
    } |
    OtherClosure {
        info         :: StgInfoTable 
        , hvalues    :: [Box]
        , rawWords   :: [Word]
    } |
    UnsupportedClosure {
        info         :: StgInfoTable 
    }
 deriving (Show)

-- | For generic code, this function returns all referenced closures. 
allPtrs :: Closure -> [Box]
allPtrs (ConsClosure {..}) = ptrArgs
allPtrs (ThunkClosure {..}) = ptrArgs
allPtrs (SelectorClosure {..}) = [selectee]
allPtrs (IndClosure {..}) = [indirectee]
allPtrs (BlackholeClosure {..}) = [indirectee]
allPtrs (APClosure {..}) = fun:payload
allPtrs (PAPClosure {..}) = fun:payload
allPtrs (BCOClosure {..}) = [instrs,literals,bcoptrs]
allPtrs (ArrWordsClosure {..}) = []
allPtrs (MutArrClosure {..}) = mccPayload
allPtrs (MutVarClosure {..}) = [var]
allPtrs (MVarClosure {..}) = [queueHead,queueTail,value]
allPtrs (FunClosure {..}) = ptrArgs
allPtrs (BlockingQueueClosure {..}) = [link, blackHole, owner, queue]
allPtrs (OtherClosure {..}) = hvalues
allPtrs (UnsupportedClosure {..}) = []



#ifdef PRIM_SUPPORTS_ANY
foreign import prim "aToWordzh" aToWord# :: Any -> Word#
foreign import prim "slurpClosurezh" slurpClosure# :: Any -> (# Addr#, ByteArray#, Array# b #)
#else
-- Workd-around code until http://hackage.haskell.org/trac/ghc/ticket/5931 was
-- accepted

-- foreign import prim "aToWordzh" aToWord'# :: Addr# -> Word#
foreign import prim "slurpClosurezh" slurpClosure'# :: Word#  -> (# Addr#, ByteArray#, Array# b #)

-- This is a datatype that has the same layout as Ptr, so that by
-- unsafeCoerce'ing, we obtain the Addr of the wrapped value
data Ptr' a = Ptr' a

aToWord# :: Any -> Word#
aToWord# a = case Ptr' a of mb@(Ptr' _) -> case unsafeCoerce# mb :: Word of W# addr -> addr

slurpClosure# :: Any -> (# Addr#, ByteArray#, Array# b #)
slurpClosure# a = slurpClosure'# (aToWord# a)
#endif

--pClosure x = do
--    getClosure x >>= print

-- | This returns the raw representation of the given argument. The second
-- component of the triple are the words on the heap, and the third component
-- are those words that are actually pointers. Once back in Haskell word, the
-- 'Word'  may be outdated after a garbage collector run, but the corresponding
-- 'Box' will still point to the correct value.
getClosureRaw :: a -> IO (Ptr StgInfoTable, [Word], [Box])
getClosureRaw x =
    case slurpClosure# (unsafeCoerce# x) of
        (# iptr, dat, ptrs #) -> do
            let nelems = (I# (sizeofByteArray# dat)) `div` wORD_SIZE
                rawWords = [W# (indexWordArray# dat i) | I# i <- [0.. fromIntegral nelems -1] ]
                pelems = I# (sizeofArray# ptrs) 
                ptrList = amap' Box $ Array 0 (pelems - 1) pelems ptrs
            ptrList `seq` rawWords `seq` return (Ptr iptr, rawWords, ptrList)

-- From compiler/ghci/RtClosureInspect.hs
amap' :: (t -> b) -> Array Int t -> [b]
amap' f (Array i0 i _ arr#) = map g [0 .. i - i0]
    where g (I# i#) = case indexArray# arr# i# of
                          (# e #) -> f e

-- derived from vacuum-1.0.0.2/src/GHC/Vacuum/Internal.hs, which got it from
-- compiler/ghci/DebuggerUtils.hs
dataConInfoPtrToNames :: Ptr StgInfoTable -> IO (String, String, String)
dataConInfoPtrToNames ptr = do
    conDescAddress <- getConDescAddress ptr
    wl <- peekArray0 0 conDescAddress
    let (pkg, modl, name) = parse wl
    return (b2s pkg, b2s modl, b2s name)
  where
    b2s :: [Word8] -> String
    b2s = fmap (chr . fromIntegral)

    getConDescAddress :: Ptr StgInfoTable -> IO (Ptr Word8)
    getConDescAddress ptr'
      | True = do
          offsetToString <- peek (ptr' `plusPtr` (negate wORD_SIZE))
          return $ (ptr' `plusPtr` stdInfoTableSizeB)
                    `plusPtr` (fromIntegral (offsetToString :: Word))
    -- This is code for !ghciTablesNextToCode: 
    {-
      | otherwise = peek . intPtrToPtr
                      . (+ fromIntegral
                            stdInfoTableSizeB)
                        . ptrToIntPtr $ ptr
    -}

    -- hmmmmmm. Is there any way to tell this?
    opt_SccProfilingOn = False

    stdInfoTableSizeW :: Int
    -- The size of a standard info table varies with profiling/ticky etc,
    -- so we can't get it from Constants
    -- It must vary in sync with mkStdInfoTable
    stdInfoTableSizeW
      = size_fixed + size_prof
      where
        size_fixed = 2  -- layout, type
        size_prof | opt_SccProfilingOn = 2
                  | otherwise    = 0

    stdInfoTableSizeB :: Int
    stdInfoTableSizeB = stdInfoTableSizeW * wORD_SIZE

-- From vacuum-1.0.0.2/src/GHC/Vacuum/Internal.hs
parse :: [Word8] -> ([Word8], [Word8], [Word8])
parse input = if not . all (>0) . fmap length $ [pkg,modl,occ]
                --then (error . concat)
                --        ["getConDescAddress:parse:"
                --        ,"(not . all (>0) . fmap le"
                --        ,"ngth $ [pkg,modl,occ]"]
                then ([], [], input) -- Not in the pkg.modl.occ format, for example END_TSO_QUEUE
                else (pkg, modl, occ)
--   = ASSERT (all (>0) (map length [pkg, modl, occ])) (pkg, modl, occ)   -- XXXXXXXXXXXXXXXX
  where
        (pkg, rest1) = break (== fromIntegral (ord ':')) input
        (modl, occ)
            = (concat $ intersperse [dot] $ reverse modWords, occWord)
            where
            (modWords, occWord) = if (length rest1 < 1) --  XXXXXXXXx YUKX
                                    --then error "getConDescAddress:parse:length rest1 < 1"
                                    then parseModOcc [] []
                                    else parseModOcc [] (tail rest1)
        -- ASSERT (length rest1 > 0) (parseModOcc [] (tail rest1))
        dot = fromIntegral (ord '.')
        parseModOcc :: [[Word8]] -> [Word8] -> ([[Word8]], [Word8])
        parseModOcc acc str
            = case break (== dot) str of
                (top, []) -> (acc, top)
                (top, _:bot) -> parseModOcc (top : acc) bot


-- | This function returns parsed heap representation of the argument _at this
-- moment_, even if it is unevaluated or an indirection or other exotic stuff.
-- Beware when passing something to this function, the same caveats as for
-- 'asBox' apply.
getClosureData :: a -> IO Closure
getClosureData x = do
    (iptr, wds, ptrs) <- getClosureRaw x
    itbl <- peek iptr
    case tipe itbl of 
        t | t >= CONSTR && t <= CONSTR_NOCAF_STATIC -> do
            (pkg, modl, name) <- dataConInfoPtrToNames iptr
            return $ ConsClosure itbl ptrs (drop (length ptrs + 1) wds) pkg modl name

        t | t >= THUNK && t <= THUNK_STATIC -> do
            return $ ThunkClosure itbl ptrs (drop (length ptrs + 2) wds)

        t | t >= FUN && t <= FUN_STATIC -> do
            return $ FunClosure itbl ptrs (drop (length ptrs + 1) wds)

        AP ->
            return $ APClosure itbl 
                (fromIntegral $ wds !! 2)
                (fromIntegral $ shiftR (wds !! 2) (wORD_SIZE_IN_BITS `div` 2))
                (head ptrs) (tail ptrs)

        PAP ->
            return $ PAPClosure itbl 
                (fromIntegral $ wds !! 2)
                (fromIntegral $ shiftR (wds !! 2) (wORD_SIZE_IN_BITS `div` 2))
                (head ptrs) (tail ptrs)

        THUNK_SELECTOR ->
            return $ SelectorClosure itbl (head ptrs)

        IND ->
            return $ IndClosure itbl (head ptrs)
        IND_STATIC ->
            return $ IndClosure itbl (head ptrs)
        BLACKHOLE ->
            return $ BlackholeClosure itbl (head ptrs)

        BCO ->
            return $ BCOClosure itbl (ptrs !! 0) (ptrs !! 1) (ptrs !! 2)
                (fromIntegral $ wds !! 4)
                (fromIntegral $ shiftR (wds !! 4) (wORD_SIZE_IN_BITS `div` 2))
                (wds !! 5)

        ARR_WORDS ->
            return $ ArrWordsClosure itbl (wds !! 1) (drop 2 wds)

        t | t == MUT_ARR_PTRS_FROZEN || t == MUT_ARR_PTRS_FROZEN0 ->
            return $ MutArrClosure itbl (wds !! 1) (wds !! 2) ptrs

        t | t == MUT_VAR_CLEAN || t == MUT_VAR_DIRTY ->
            return $ MutVarClosure itbl (head ptrs)

        t | t == MVAR_CLEAN || t == MVAR_DIRTY ->
            return $ MVarClosure itbl (ptrs !! 0) (ptrs !! 1) (ptrs !! 2)

        BLOCKING_QUEUE ->
            return $ OtherClosure itbl ptrs wds
        --    return $ BlockingQueueClosure itbl
        --        (ptrs !! 0) (ptrs !! 1) (ptrs !! 2) (ptrs !! 3)

        --  return $ OtherClosure itbl ptrs wds
        --
        _ ->
            return $ UnsupportedClosure itbl

-- | Like 'getClosureData', but taking a 'Box', so it is easier to work with.
getBoxedClosureData :: Box -> IO Closure
getBoxedClosureData (Box a) = getClosureData a

