{-# LANGUAGE MagicHash, UnboxedTuples, CPP, ForeignFunctionInterface, GHCForeignImportPrim, UnliftedFFITypes, BangPatterns, RecordWildCards #-}

module GHC.HeapView where

import System.IO.Unsafe
import GHC.Exts
import GHC.Prim 
import System.Environment
import GHC.Arr ((!), Array(..), elems)

import GHC.Constants ( wORD_SIZE, tAG_MASK, wORD_SIZE_IN_BITS )

import System.Mem
import System.Mem.StableName
import Foreign
import Foreign.C
import Foreign.Ptr 
import Foreign.Storable 
import Foreign.Marshal.Array
import Numeric          ( showHex )
import Data.Word
import Data.Bits
import Data.Char
import GHC.Integer (wordToInteger)
import Control.Monad

newtype HValue = HValue Any

-- A Safegard of HValues
data Box = Box HValue

type HalfWord = Word32

instance Show Box where
-- From libraries/base/GHC/Ptr.lhs
   showsPrec _ (Box (HValue any)) rs =
    -- unsafePerformIO (print "↓" >> pClosure any) `seq`    
    pad_out (showHex addr "") ++ (if tag>0 then "/" ++ show tag else "") ++ rs
     where
       ptr  = wordToInteger(int2Word#(aToInt# any))
       tag  = ptr .&. fromIntegral tAG_MASK -- ((1 `shiftL` TAG_BITS) -1)
       addr = ptr - tag
        -- want 0s prefixed to pad it out to a fixed length.
       pad_out ls = 
          '0':'x':(replicate (2*wORD_SIZE - length ls) '0') ++ ls

asBox :: a -> Box
asBox x = Box (unsafeCoerce# x)

{-
 - StgInfoTable parsing derived from ByteCodeItbls.lhs
 - Removed the code parameter for now
 - Replaced Type by an enumeration
 - Remove stuff dependent on GHCI_TABLES_NEXT_TO_CODE
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

   poke a0 itbl
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

store :: Storable a => a -> PtrIO ()
store x = do addr <- advance
             lift (poke addr x)

{-
 - Embedded StateT, also from ByteCodeItbls
 -}

newtype State s m a = State (s -> m (s, a))

instance Monad m => Monad (State s m) where
  return a      = State (\s -> return (s, a))
  State m >>= k = State (\s -> m s >>= \(s', a) -> case k a of State n -> n s')
  fail str      = State (\_ -> fail str)

lift m = State (\s -> m >>= \a -> return (s, a))

runState :: (Monad m) => s -> State s m a -> m a
runState s (State m) = m s >>= return . snd

{-
 - Data Type representing Closures
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

data Closure =
    ConsClosure {
        info         :: StgInfoTable 
        , ptrArgs    :: [Box]
        , dataArgs   :: [Word]
        , descr      :: String
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
        , words      :: [Word]
    } |
    MutArrClosure {
        info         :: StgInfoTable 
        , mccPtrs    :: Word
        , mccSize    :: Word
        , mccPayload :: [Box]
        -- Card table ignored
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
        , words      :: [Word]
    }
 deriving (Show)

allPtrs (ConsClosure {..}) = ptrArgs
allPtrs (ThunkClosure {..}) = ptrArgs
allPtrs (SelectorClosure {..}) = [selectee]
allPtrs (IndClosure {..}) = [indirectee]
allPtrs (APClosure {..}) = fun:payload
allPtrs (PAPClosure {..}) = fun:payload
allPtrs (BCOClosure {..}) = [instrs,literals,bcoptrs]
allPtrs (ArrWordsClosure {..}) = []
allPtrs (MutArrClosure {..}) = mccPayload
allPtrs (FunClosure {..}) = ptrArgs
allPtrs (OtherClosure {..}) = hvalues

#ifdef PRIM_SUPPORTS_ANY
foreign import prim "aToInt" aToInt# :: Any -> Int#
foreign import prim "slurpClosurezh" slurpClosure# :: Any -> (# Addr#, ByteArray#, Array# b #)
#else
-- Workd-around code until http://hackage.haskell.org/trac/ghc/ticket/5931 was
-- accepted

foreign import prim "aToInt" aToInt'# :: Addr# -> Int#
foreign import prim "slurpClosurezh" slurpClosure'# :: Addr#  -> (# Addr#, ByteArray#, Array# b #)

-- This is a datatype that has the same layout as Ptr, so that by
-- unsafeCoerce'ing, we obtain the Addr of the wrapped value
data Ptr' a = Ptr' a

aToInt# :: Any -> Int#
aToInt# a = case Ptr' a of mb@(Ptr' _) -> case unsafeCoerce# mb :: Ptr () of Ptr addr -> aToInt'# addr
slurpClosure# :: Any -> (# Addr#, ByteArray#, Array# b #)
slurpClosure# a = case Ptr' a of mb@(Ptr' _) -> case unsafeCoerce# mb :: Ptr () of Ptr addr -> slurpClosure'# addr
#endif

--pClosure x = do
--    getClosure x >>= print

getClosureRaw :: a -> IO (Ptr StgInfoTable, [Word], [Box])
getClosureRaw x =
    case slurpClosure# (unsafeCoerce# x) of
        (# iptr, dat, ptrs #) -> do
            let nelems = (I# (sizeofByteArray# dat)) `div` wORD_SIZE
                words = [W# (indexWordArray# dat i) | I# i <- [0.. fromIntegral nelems -1] ]
                pelems = I# (sizeofArray# ptrs) 
                ptrList = amap' Box $ Array 0 (pelems - 1) pelems ptrs
            ptrList `seq` words `seq` return (Ptr iptr, words, ptrList)

-- From compiler/ghci/RtClosureInspect.hs
amap' :: (t -> b) -> Array Int t -> [b]
amap' f (Array i0 i _ arr#) = map g [0 .. i - i0]
    where g (I# i#) = case indexArray# arr# i# of
                          (# e #) -> f e



-- #include "../includes/rts/storage/ClosureTypes.h"

getHValueClosureData :: Box -> IO Closure
getHValueClosureData b@(Box a) = getClosureData a

-- derived from vacuum-1.0.0.2/src/GHC/Vacuum/Internal.hs, which got it from
-- compiler/ghci/DebuggerUtils.hs
dataConInfoPtrToNames :: Ptr StgInfoTable -> IO String
dataConInfoPtrToNames ptr = do
    conDescAddress <- getConDescAddress ptr
    wl <- peekArray0 0 conDescAddress
    return $ fmap (chr . fromIntegral) wl
  where
    getConDescAddress :: Ptr StgInfoTable -> IO (Ptr Word8)
    getConDescAddress ptr
      | True = do
          offsetToString <- peek (ptr `plusPtr` (negate wORD_SIZE))
          return $ (ptr `plusPtr` stdInfoTableSizeB)
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
    

getClosureData :: a -> IO Closure
getClosureData x = do
    (iptr, words, ptrs) <- getClosureRaw x
    itbl <- peek iptr
    case tipe itbl of 
        t | t >= CONSTR && t <= CONSTR_NOCAF_STATIC -> do
            name <- dataConInfoPtrToNames iptr
            return $ ConsClosure itbl ptrs (drop (length ptrs + 1) words) name

        t | t >= THUNK && t <= THUNK_STATIC -> do
            return $ ThunkClosure itbl ptrs (drop (length ptrs + 2) words)

        t | t >= FUN && t <= FUN_STATIC -> do
            return $ FunClosure itbl ptrs (drop (length ptrs + 1) words)

        AP ->
            return $ APClosure itbl 
                (fromIntegral $ words !! 2)
                (fromIntegral $ shiftR (words !! 2) (wORD_SIZE_IN_BITS `div` 2))
                (head ptrs) (tail ptrs)

        PAP ->
            return $ PAPClosure itbl 
                (fromIntegral $ words !! 2)
                (fromIntegral $ shiftR (words !! 2) (wORD_SIZE_IN_BITS `div` 2))
                (head ptrs) (tail ptrs)

        THUNK_SELECTOR ->
            return $ SelectorClosure itbl (head ptrs)

        IND ->
            return $ IndClosure itbl (head ptrs)
        IND_STATIC ->
            return $ IndClosure itbl (head ptrs)
        BLACKHOLE ->
            return $ IndClosure itbl (head ptrs)

        BCO ->
            return $ BCOClosure itbl (ptrs !! 0) (ptrs !! 1) (ptrs !! 2)
                (fromIntegral $ words !! 4)
                (fromIntegral $ shiftR (words !! 4) (wORD_SIZE_IN_BITS `div` 2))
                (words !! 5)

        ARR_WORDS ->
            return $ ArrWordsClosure itbl (words !! 1) (drop 2 words)
        MUT_ARR_PTRS_FROZEN ->
            return $ MutArrClosure itbl (words !! 2) (words !! 3) ptrs

        BLOCKING_QUEUE ->
          return $ OtherClosure itbl ptrs words
        --    return $ BlockingQueueClosure itbl
        --        (ptrs !! 0) (ptrs !! 1) (ptrs !! 2) (ptrs !! 3)

        --  return $ OtherClosure itbl ptrs words
        x -> error $ "getClosureData: Cannot handle closure type " ++ show x
