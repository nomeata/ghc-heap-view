{-# LANGUAGE MagicHash, UnboxedTuples, CPP, ForeignFunctionInterface, GHCForeignImportPrim, UnliftedFFITypes, BangPatterns, RecordWildCards, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-|
Module      :  GHC.HeapView
Copyright   :  (c) 2012 Joachim Breitner
License     :  BSD3
Maintainer  :  Joachim Breitner <mail@joachim-breitner.de>

With this module, you can investigate the heap representation of Haskell
values, i.e. to investigate sharing and lazy evaluation.
-}


module GHC.HeapView (
    -- * Heap data types
    GenClosure(..),
    Closure,
    allPtrs,
    ClosureType(..),
    StgInfoTable(..),
    HalfWord,
    -- * Reading from the heap
    getClosureData,
    getBoxedClosureData,
    getClosureRaw,
    -- * Pretty printing
    ppClosure,
    -- * Heap maps
    -- $heapmap
    HeapTree(..),
    buildHeapTree,
    ppHeapTree,
    HeapGraphEntry(..),
    HeapGraphIndex,
    HeapGraph(..),
    lookupHeapGraph,
    heapGraphRoot,
    buildHeapGraph,
    ppHeapGraph,
    -- * Boxes
    Box(..),
    asBox,
    -- * Weak boxes
    WeakBox,
    weakBox,
    isAlive,
    derefWeakBox,
    WeakClosure,
    weakenClosure,
    )
    where

import GHC.Exts         ( Any,
                          Ptr(..), Addr#, Int(..), Word(..), Word#, Int#,
                          ByteArray#, Array#, sizeofByteArray#, sizeofArray#, indexArray#, indexWordArray#,
                          unsafeCoerce# )

import GHC.Arr          (Array(..))

import GHC.Constants    ( wORD_SIZE, tAG_MASK, wORD_SIZE_IN_BITS )

import System.IO.Unsafe ( unsafePerformIO )

import Foreign          hiding ( unsafePerformIO )
import Numeric          ( showHex )
import Data.Char
import Data.List
import Data.Maybe       ( isJust, catMaybes )
import System.Mem.Weak
import Data.Functor
import Data.Function
import Data.Foldable    ( Foldable )
import Data.Traversable ( Traversable )
import qualified Data.Traversable as T
import qualified Data.IntMap as M
import Control.Monad
import Control.Monad.Trans.State
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Control.Monad.Trans.Writer.Strict
import Control.Arrow    ( first, second )

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
  Box a == Box b = case reallyUnsafePtrEqualityUpToTag# a b of
    0# -> False
    _  -> True

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
      = flip (evalStateT) (castPtr a0)
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

type PtrIO = StateT (Ptr Word8) IO

advance :: Storable a => PtrIO (Ptr a)
advance = StateT adv where
    adv addr = case castPtr addr of { addrCast -> return
        (addrCast, addr `plusPtr` sizeOfPointee addrCast) }

sizeOfPointee :: (Storable a) => Ptr a -> Int
sizeOfPointee addr = sizeOf (typeHack addr)
    where typeHack = undefined :: Ptr a -> a

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

  The data type is parametrized by the type to store references in, which
  should be either 'Box' or 'WeakBox', with appropriate type synonyms 'Closure'
  and 'WeakClosure'.
 -}
data GenClosure b =
    ConsClosure {
        info         :: StgInfoTable 
        , ptrArgs    :: [b]
        , dataArgs   :: [Word]
        , pkg        :: String
        , modl       :: String
        , name       :: String
    } |
    ThunkClosure {
        info         :: StgInfoTable 
        , ptrArgs    :: [b]
        , dataArgs   :: [Word]
    } |
    SelectorClosure {
        info         :: StgInfoTable 
        , selectee   :: b
    } |
    IndClosure {
        info         :: StgInfoTable 
        , indirectee   :: b
    } |
    BlackholeClosure {
        info         :: StgInfoTable 
        , indirectee   :: b
    } |
    -- In GHCi, if Linker.h would allow a reverse looup, we could for exported
    -- functions fun actually find the name here.
    -- At least the other direction works via "lookupSymbol
    -- base_GHCziBase_zpzp_closure" and yields the same address (up to tags)
    APClosure {
        info         :: StgInfoTable 
        , arity      :: HalfWord
        , n_args     :: HalfWord
        , fun        :: b
        , payload    :: [b]
    } |
    PAPClosure {
        info         :: StgInfoTable 
        , arity      :: HalfWord
        , n_args     :: HalfWord
        , fun        :: b
        , payload    :: [b]
    } |
    APStackClosure {
        info         :: StgInfoTable 
        , fun        :: b
        , payload    :: [b]
    } |
    BCOClosure {
        info         :: StgInfoTable 
        , instrs     :: b
        , literals   :: b
        , bcoptrs    :: b
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
        , mccPayload :: [b]
        -- Card table ignored
    } |
    MutVarClosure {
        info         :: StgInfoTable 
        , var        :: b
    } |
    MVarClosure {
        info         :: StgInfoTable 
        , queueHead  :: b
        , queueTail  :: b
        , value      :: b
    } |
    FunClosure {
        info         :: StgInfoTable 
        , ptrArgs    :: [b]
        , dataArgs   :: [Word]
    } |
    BlockingQueueClosure {
        info         :: StgInfoTable 
        , link       :: b
        , blackHole  :: b
        , owner      :: b
        , queue      :: b
    } |
    OtherClosure {
        info         :: StgInfoTable 
        , hvalues    :: [b]
        , rawWords   :: [Word]
    } |
    UnsupportedClosure {
        info         :: StgInfoTable 
    }
 deriving (Show, Functor, Foldable, Traversable)


type Closure = GenClosure Box

-- | For generic code, this function returns all referenced closures. 
allPtrs :: GenClosure b -> [b]
allPtrs (ConsClosure {..}) = ptrArgs
allPtrs (ThunkClosure {..}) = ptrArgs
allPtrs (SelectorClosure {..}) = [selectee]
allPtrs (IndClosure {..}) = [indirectee]
allPtrs (BlackholeClosure {..}) = [indirectee]
allPtrs (APClosure {..}) = fun:payload
allPtrs (PAPClosure {..}) = fun:payload
allPtrs (APStackClosure {..}) = fun:payload
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
foreign import prim "reallyUnsafePtrEqualityUpToTag" reallyUnsafePtrEqualityUpToTag# :: Any -> Any -> Int#
#else
-- Workd-around code until http://hackage.haskell.org/trac/ghc/ticket/5931 was
-- accepted

-- foreign import prim "aToWordzh" aToWord'# :: Addr# -> Word#
foreign import prim "slurpClosurezh" slurpClosure'# :: Word#  -> (# Addr#, ByteArray#, Array# b #)

foreign import prim "reallyUnsafePtrEqualityUpToTag" reallyUnsafePtrEqualityUpToTag'# :: Word# -> Word# -> Int#

-- This is a datatype that has the same layout as Ptr, so that by
-- unsafeCoerce'ing, we obtain the Addr of the wrapped value
data Ptr' a = Ptr' a

aToWord# :: Any -> Word#
aToWord# a = case Ptr' a of mb@(Ptr' _) -> case unsafeCoerce# mb :: Word of W# addr -> addr

slurpClosure# :: Any -> (# Addr#, ByteArray#, Array# b #)
slurpClosure# a = slurpClosure'# (aToWord# a)

reallyUnsafePtrEqualityUpToTag# :: Any -> Any -> Int#
reallyUnsafePtrEqualityUpToTag# a b = reallyUnsafePtrEqualityUpToTag'# (aToWord# a) (aToWord# b)
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

        AP_STACK ->
            return $ APStackClosure itbl (head ptrs) (tail ptrs)

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


isChar :: GenClosure b -> Maybe Char
isChar (ConsClosure { name = "C#", dataArgs = [ch], ptrArgs = []}) = Just (chr (fromIntegral ch))
isChar _ = Nothing

isCons :: GenClosure b -> Maybe (b, b)
isCons (ConsClosure { name = ":", dataArgs = [], ptrArgs = [h,t]}) = Just (h,t)
isCons _ = Nothing

isTup :: GenClosure b -> Maybe [b]
isTup (ConsClosure { dataArgs = [], ..}) =
    if length name >= 3 &&
       head name == '(' && last name == ')' &&
       all (==',') (tail (init name))
    then Just ptrArgs else Nothing
isTup _ = Nothing


isNil :: GenClosure b -> Bool
isNil (ConsClosure { name = "[]", dataArgs = [], ptrArgs = []}) = True
isNil _ = False

-- | A pretty-printer that tries to generate valid Haskell for evalutated data.
-- It assumes that for the included boxes, you already replaced them by Strings
-- using 'Data.Foldable.map' or, if you need to do IO, 'Data.Foldable.mapM'.
--
-- The parameter gives the precedendence, to avoid avoidable parenthesises.
ppClosure :: (Int -> b -> String) -> Int -> GenClosure b -> String
ppClosure showBox prec c = case c of
    _ | Just ch <- isChar c -> app $
        ["C#", show ch]
    _ | Just (h,t) <- isCons c -> addBraces (5 <= prec) $
        showBox 5 h ++ " : " ++ showBox 4 t
    _ | Just vs <- isTup c ->
        "(" ++ intercalate "," (map (showBox 0) vs) ++ ")"
    ConsClosure {..} -> app $
        name : map (showBox 10) ptrArgs ++ map show dataArgs
    ThunkClosure {..} -> app $
        "_thunk" : map (showBox 10) ptrArgs ++ map show dataArgs
    SelectorClosure {..} -> app
        ["_sel", showBox 10 selectee]
    IndClosure {..} -> app
        ["_ind", showBox 10 indirectee]
    BlackholeClosure {..} -> app
        ["_bh",  showBox 10 indirectee]
    APClosure {..} -> app $ map (showBox 10) $
        fun : payload
    PAPClosure {..} -> app $ map (showBox 10) $
        fun : payload
    APStackClosure {..} -> app $ map (showBox 10) $
        fun : payload
    BCOClosure {..} -> app
        ["_bco"]
    ArrWordsClosure {..} -> app
        ["toArray", intercalate "," (map show arrWords) ]
    MutArrClosure {..} -> app
        ["toMutArray", intercalate "," (map (showBox 10) mccPayload)]
    MutVarClosure {..} -> app $
        ["_mutVar", (showBox 10) var]
    MVarClosure {..} -> app $
        ["MVar", (showBox 10) value]
    FunClosure {..} -> 
        "_fun" ++ braceize (map (showBox 0) ptrArgs ++ map show dataArgs)
    BlockingQueueClosure {..} -> 
        "_blockingQueue"
    OtherClosure {..} ->
        "_other"
    UnsupportedClosure {..} ->
        "_unsupported"
  where
    addBraces True t = "(" ++ t ++ ")"
    addBraces False t = t
    app [] = "()"
    app [a] = a 
    app xs = addBraces (10 <= prec) (intercalate " " xs)
    braceize [] = ""
    braceize xs = "{" ++ intercalate "," xs ++ "}"
    
-- $heapmap
-- For more global views of the heap, you can use heap maps. These come in
-- variations, either a trees or as graphs, depending on
-- whether you want to detect cycles and sharing or not.

-- | Heap maps as tree, i.e. no sharing, no cycles.
data HeapTree = HeapTree WeakBox (GenClosure HeapTree) | EndOfHeapTree

heapTreeClosure :: HeapTree -> Maybe (GenClosure HeapTree)
heapTreeClosure (HeapTree _ c) = Just c
heapTreeClosure EndOfHeapTree = Nothing

-- | Constructing an 'HeapTree' from a boxed value. It takes a depth parameter
-- that prevents it from running ad infinitum for cyclic or infinite
-- structures.
buildHeapTree :: Int -> Box -> IO HeapTree
buildHeapTree 0 _ = do
    return $ EndOfHeapTree
buildHeapTree n b = do
    w <- weakBox b
    c <- getBoxedClosureData b
    c' <- T.mapM (buildHeapTree (n-1)) c
    return $ HeapTree w c'

-- | Pretty-Printing a heap Tree
-- 
-- Example output for @[Just 4, Nothing, *something*]@, where *something* is an
-- unevaluated expression depending on the command line argument.
--
-- >[Just (I# 4),Nothing,Just (_thunk ["arg1","arg2"])]
ppHeapTree :: HeapTree -> String
ppHeapTree = go 0
  where
    go _ EndOfHeapTree = "..."
    go prec t@(HeapTree _ c')
        | Just s <- isHeapTreeString t = show s
        | Just l <- isHeapTreeList t   = "[" ++ intercalate "," (map ppHeapTree l) ++ "]"
        | otherwise                    =  ppClosure go prec c'

isHeapTreeList :: HeapTree -> Maybe ([HeapTree])
isHeapTreeList tree = do
    c <- heapTreeClosure tree
    if isNil c
      then return []
      else do
        (h,t) <- isCons c
        t' <- isHeapTreeList t
        return $ (:) h t'

isHeapTreeString :: HeapTree -> Maybe String
isHeapTreeString t = do
    list <- isHeapTreeList t
    -- We do not want to print empty lists as "" as we do not know that they
    -- are really strings.
    if (null list)
        then Nothing
        else mapM (isChar <=< heapTreeClosure) list

-- | For heap graphs, i.e. data structures that also represent sharing and
-- cyclic structures, these are the entries. If the referenced value is
-- @Nothing@, then we do not have that value in the map, most likely due to
-- exceeding the recursion bound passed to 'buildHeapGraph'.
data HeapGraphEntry = HeapGraphEntry WeakBox (GenClosure (Maybe HeapGraphIndex))
    deriving (Show)
type HeapGraphIndex = Int

-- | The whole graph. The suggested interface is to only use 'lookupHeapGraph',
-- as the internal representation may change. Nevertheless, we export it here:
-- Sometimes the user knows better what he needs than we do.
newtype HeapGraph = HeapGraph (M.IntMap HeapGraphEntry)
    deriving (Show)

lookupHeapGraph :: HeapGraphIndex -> HeapGraph -> Maybe HeapGraphEntry
lookupHeapGraph i (HeapGraph m) = M.lookup i m

heapGraphRoot :: HeapGraphIndex
heapGraphRoot = 0

-- | Creates a 'HeapGraph' for the value in the box, but not recursing further
-- than the given limit. The initial value has index 'heapGraphRoot'.
buildHeapGraph :: Int -> Box -> IO HeapGraph
buildHeapGraph limit _ | limit <= 0 = error "buildHeapGraph: First argument has to be positive"
buildHeapGraph limit initialBox = do
    let initialState = ([], [0..])
    HeapGraph <$> execWriterT (runStateT (add limit initialBox) initialState)
  where
    add 0 _ = return Nothing
    add n b = do
        -- If the box is in the map, return the index
        (existing,_) <- get
        case lookup b existing of
            Just i -> return $ Just i
            Nothing -> do
                -- Otherwise, allocate a new index
                i <- nextI
                -- And register it
                modify (first ((b,i):))
                c <- liftIO $ getBoxedClosureData b
                -- Find indicies for all boxes contained in the map
                c' <- T.mapM (add (n-1)) c
                w <- liftIO $ weakBox b
                -- Add add the resulting closure to the map
                lift $ tell (M.singleton i (HeapGraphEntry w c'))
                return $ Just i
    nextI = do
        i <- gets (head . snd)
        modify (second tail)
        return i

-- | Pretty-prints a HeapGraph. The resulting string contains newlines. Example
-- for @let s = "Ki" in (s, s, cycle "Ho")@:
--
-- >let x1 = "Ki"
-- >    x6 = C# 'H' : C# 'o' : x6
-- >in (x1,x1,x6)
ppHeapGraph :: HeapGraph -> String
ppHeapGraph (HeapGraph m) = letWrapper ++ ppRef 0 (Just heapGraphRoot)
  where
    -- All variables occuring more than once
    bindings = boundMultipleTimes (HeapGraph m) [heapGraphRoot] 

    letWrapper =
        if null bindings
        then ""
        else "let " ++ intercalate "\n    " (map ppBinding bindings) ++ "\nin "

    bindingLetter i = case iToE i of
        HeapGraphEntry _ c -> case c of 
            ThunkClosure {..} -> 't'
            SelectorClosure {..} -> 't'
            APClosure {..} -> 't'
            PAPClosure {..} -> 'f'
            BCOClosure {..} -> 't'
            FunClosure {..} -> 'f'
            _ -> 'x'

    ppBindingMap = M.fromList $
        concat $
        map (zipWith (\j (i,c) -> (i, [c] ++ show j)) [(1::Int)..]) $
        groupBy ((==) `on` snd) $ 
        sortBy (compare `on` snd)
        [ (i, bindingLetter i) | i <- bindings ]

    ppVar i = ppBindingMap M.! i
    ppBinding i = ppVar i ++ " = " ++ ppEntry 0 (iToE i)

    ppEntry prec e@(HeapGraphEntry _ c)
        | Just s <- isString e = show s
        | Just l <- isList e = "[" ++ intercalate "," (map (ppRef 0) l) ++ "]"
        | otherwise = ppClosure ppRef prec c

    ppRef _ Nothing = "..."
    ppRef prec (Just i) | i `elem` bindings = ppVar i
                        | otherwise = ppEntry prec (iToE i) 
    iToE i = m M.! i

    iToUnboundE i = if i `elem` bindings then Nothing else M.lookup i m

    isList :: HeapGraphEntry -> Maybe ([Maybe HeapGraphIndex])
    isList (HeapGraphEntry _ c) = 
        if isNil c
          then return []
          else do
            (h,t) <- isCons c
            ti <- t
            e <- iToUnboundE ti
            t' <- isList e
            return $ (:) h t'

    isString :: HeapGraphEntry -> Maybe String
    isString e = do
        list <- isList e
        -- We do not want to print empty lists as "" as we do not know that they
        -- are really strings.
        if (null list)
            then Nothing
            else mapM (isChar . (\(HeapGraphEntry _ c) -> c) <=< iToUnboundE <=< id) list


-- | In the given HeapMap, list all indices that are used more than once. The
-- second parameter adds external references, commonly @[heapGraphRoot]@.
boundMultipleTimes :: HeapGraph -> [HeapGraphIndex] -> [HeapGraphIndex]
boundMultipleTimes (HeapGraph m) roots = map head $ filter (not.null) $ map tail $ group $ sort $
     roots ++ concatMap (\(HeapGraphEntry _ c) -> catMaybes (allPtrs c)) (M.elems m)

-- | An a variant of 'Box' that does not keep the value alive.
-- 
-- Like 'Box', its 'Show' instance is highly unsafe.
newtype WeakBox = WeakBox (Weak Box)


type WeakClosure = GenClosure WeakBox

instance Show WeakBox where
    showsPrec p (WeakBox w) rs = case unsafePerformIO (deRefWeak w) of
        Nothing -> let txt = "(freed)" in
                   replicate (2*wORD_SIZE - length txt) ' ' ++ txt ++ rs
        Just b -> showsPrec p b rs

{-|
  Turns a 'Box' into a 'WeakBox', allowing the referenced value to be garbage
  collected.
-}
weakBox :: Box -> IO WeakBox
weakBox b@(Box a) = WeakBox `fmap` mkWeak a b Nothing

{-|
  Checks whether the value referenced by a weak box is still alive
-}
isAlive :: WeakBox -> IO Bool
isAlive (WeakBox w) = isJust `fmap` deRefWeak w

{-|
  Dereferences the weak box
-}
derefWeakBox :: WeakBox -> IO (Maybe Box)
derefWeakBox (WeakBox w) = deRefWeak w

weakenClosure :: Closure -> IO WeakClosure
weakenClosure = T.mapM weakBox
