{-# LANGUAGE MagicHash, UnboxedTuples, CPP, ForeignFunctionInterface, GHCForeignImportPrim, UnliftedFFITypes, BangPatterns, RecordWildCards, DeriveFunctor, DeriveFoldable, DeriveTraversable, PatternGuards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-|
Module      :  GHC.HeapView
Copyright   :  (c) 2012-2019 Joachim Breitner
License     :  BSD3
Maintainer  :  Joachim Breitner <mail@joachim-breitner.de>

With this module, you can investigate the heap representation of Haskell
values, i.e. to investigate sharing and lazy evaluation.
-}


module GHC.HeapView (
    -- * Heap data types
    GenClosure(..),
    Closure,
    allClosures,                            -- was allPtrs
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
    multiBuildHeapGraph,
    addHeapGraph,
    annotateHeapGraph,
    updateHeapGraph,
    ppHeapGraph,
    -- * Boxes
    Box(..),
    asBox,
    areBoxesEqual,
    -- * Disassembler
    disassembleBCO,
    )
    where

import GHC.Exts         ( Any,
                          Ptr(..), Addr#, Int(..), Word(..),
                          ByteArray#, Array#, sizeofByteArray#, sizeofArray#, indexArray#, indexWordArray#,
                          unsafeCoerce# )

import GHC.Exts.Heap
import GHC.Exts.Heap.Constants

import GHC.Arr          (Array(..))

import Foreign          hiding ( void )
import Data.Char
import Data.List
import Data.Maybe       ( catMaybes )
import Data.Functor
import Data.Function
import qualified Data.Foldable as F
import qualified Data.Traversable as T
import qualified Data.IntMap as M
import Control.Monad
import Control.Monad.Trans.State
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Control.Monad.Trans.Writer.Strict
import Control.Exception.Base (evaluate)

import GHC.Disassembler

#include "ghcautoconf.h"

#if __GLASGOW_HASKELL__ == 806
-- Deriving for Functor, Foldable and Traversable is missing in  GHC 8.6
-- will be available in GHC 8.8
deriving instance Functor GenClosure
deriving instance Foldable GenClosure
deriving instance Traversable GenClosure
#endif

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
                 entry  = Nothing,            -- Storable instance needed for EntryFunPtr!!
                 ptrs   = ptrs',
                 nptrs  = nptrs',
                 tipe   = toEnum (fromIntegral (tipe'::HalfWord)),
                 srtlen = srtlen',
                 code   = Nothing              -- Storable instance needed for ItblCodes
              }

fieldSz :: Storable b => (a -> b) -> a -> Int
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


foreign import prim "stg_unpackClosurezh" unpackClosurezh# :: Any -> (# Addr#, ByteArray#, Array# b #)

-- | This returns the raw representation of the given argument. The second
-- component of the triple are the words on the heap, and the third component
-- are those words that are actually pointers. Once back in Haskell word, the
-- 'Word'  may be outdated after a garbage collector run, but the corresponding
-- 'Box' will still point to the correct value.
getClosureRaw :: a -> IO (Ptr StgInfoTable, [Word], [Box])
getClosureRaw x =
    case unpackClosurezh# (unsafeCoerce# x) of
        (# iptr, dat, ptrs #) -> do
            let nelems = (I# (sizeofByteArray# dat)) `div` wORD_SIZE
                rawWords = [W# (indexWordArray# dat i) | I# i <- [0.. fromIntegral nelems -1] ]
                pelems = I# (sizeofArray# ptrs)
                ptrList = amap' Box $ Array 0 (pelems - 1) pelems ptrs
            -- This is just for good measure, and seems to be not important.
            mapM_ evaluate ptrList
            -- This seems to be required to avoid crashes as well
            void $ evaluate nelems
            -- The following deep evaluation is crucial to avoid crashes (but why)?
            mapM_ evaluate rawWords
            return (Ptr iptr, rawWords, ptrList)

-- From compiler/ghci/RtClosureInspect.hs
amap' :: (t -> b) -> Array Int t -> [b]
amap' f (Array i0 i _ arr#) = map g [0 .. i - i0]
    where g (I# i#) = case indexArray# arr# i# of
                          (# e #) -> f e

isChar :: GenClosure b -> Maybe Char
isChar (ConstrClosure { name = "C#", dataArgs = [ch], ptrArgs = []}) = Just (chr (fromIntegral ch))
isChar _ = Nothing

isCons :: GenClosure b -> Maybe (b, b)
isCons (ConstrClosure { name = ":", dataArgs = [], ptrArgs = [h,t]}) = Just (h,t)
isCons _ = Nothing

isTup :: GenClosure b -> Maybe [b]
isTup (ConstrClosure { dataArgs = [], ..}) =
    if length name >= 3 &&
       head name == '(' && last name == ')' &&
       all (==',') (tail (init name))
    then Just ptrArgs else Nothing
isTup _ = Nothing


isNil :: GenClosure b -> Bool
isNil (ConstrClosure { name = "[]", dataArgs = [], ptrArgs = []}) = True
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
    ConstrClosure {..} -> app $
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
        ["_bco", showBox 10 bcoptrs]
    ArrWordsClosure {..} -> app
        ["toArray", "("++show (length arrWords) ++ " words)", intercalate "," (shorten (map show arrWords)) ]
    MutArrClosure {..} -> app
        --["toMutArray", "("++show (length mccPayload) ++ " ptrs)",  intercalate "," (shorten (map (showBox 10) mccPayload))]
        ["[", intercalate ", " (shorten (map (showBox 10) mccPayload)),"]"]
    MutVarClosure {..} -> app $
        ["_mutVar", (showBox 10) var]
    MVarClosure {..} -> app $
        ["MVar", (showBox 10) value]
    FunClosure {..} ->
        "_fun" ++ braceize (map (showBox 0) ptrArgs ++ map show dataArgs)
    BlockingQueueClosure {..} ->
        "_blockingQueue"
    IntClosure {..} -> app
        ["Int", show intVal]
    WordClosure {..} -> app
        ["Word", show wordVal]
    Int64Closure {..} -> app
        ["Int64", show int64Val]
    Word64Closure {..} -> app
        ["Word64", show word64Val]
    AddrClosure {..} -> app
        ["Addr", show addrVal]
    FloatClosure {..} -> app
        ["Float", show floatVal]
    DoubleClosure {..} -> app
        ["Double", show doubleVal]
    OtherClosure {..} ->
        "_other"
    UnsupportedClosure {..} ->
        "_unsupported"
  where
    app [a] = a  ++ "()"
    app xs = addBraces (10 <= prec) (intercalate " " xs)

    shorten xs = if length xs > 20 then take 20 xs ++ ["(and more)"] else xs

{- $heapmap

   For more global views of the heap, you can use heap maps. These come in
   variations, either a trees or as graphs, depending on
   whether you want to detect cycles and sharing or not.

   The entries of a 'HeapGraph' can be annotated with arbitrary values. Most
   operations expect this to be in the 'Monoid' class: They use 'mempty' to
   annotate closures added because the passed values reference them, and they
   use 'mappend' to combine the annotations when two values conincide, e.g.
   during 'updateHeapGraph'.
-}

-- | Heap maps as tree, i.e. no sharing, no cycles.
data HeapTree = HeapTree Box (GenClosure HeapTree) | EndOfHeapTree

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
    c <- getBoxedClosureData b
    c' <- T.mapM (buildHeapTree (n-1)) c
    return $ HeapTree b c'

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
        | Just bc <- disassembleBCO heapTreeClosure c'
                                       = app ("_bco" : map (go 10) (concatMap F.toList bc))
        | otherwise                    = ppClosure go prec c'
      where
        app [a] = a ++ "()"
        app xs = addBraces (10 <= prec) (intercalate " " xs)

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
--
-- Besides a pointer to the stored value and the closure representation we
-- also keep track of whether the value was still alive at the last update of the
-- heap graph. In addition we have a slot for arbitrary data, for the user's convenience.
data HeapGraphEntry a = HeapGraphEntry {
        hgeBox :: Box,
        hgeClosure :: GenClosure (Maybe HeapGraphIndex),
        hgeLive :: Bool,
        hgeData :: a}
    deriving (Show, Functor)
type HeapGraphIndex = Int

-- | The whole graph. The suggested interface is to only use 'lookupHeapGraph',
-- as the internal representation may change. Nevertheless, we export it here:
-- Sometimes the user knows better what he needs than we do.
newtype HeapGraph a = HeapGraph (M.IntMap (HeapGraphEntry a))
    deriving (Show)

lookupHeapGraph :: HeapGraphIndex -> (HeapGraph a) -> Maybe (HeapGraphEntry a)
lookupHeapGraph i (HeapGraph m) = M.lookup i m

heapGraphRoot :: HeapGraphIndex
heapGraphRoot = 0

-- | Creates a 'HeapGraph' for the value in the box, but not recursing further
-- than the given limit. The initial value has index 'heapGraphRoot'.
buildHeapGraph
   :: Monoid a
   => Int -- ^ Search limit
   -> a -- ^ Data value for the root
   -> Box -- ^ The value to start with
   -> IO (HeapGraph a)
buildHeapGraph limit rootD initialBox =
    fst <$> multiBuildHeapGraph limit [(rootD, initialBox)]

-- | Creates a 'HeapGraph' for the values in multiple boxes, but not recursing
--   further than the given limit.
--
--   Returns the 'HeapGraph' and the indices of initial values. The arbitrary
--   type @a@ can be used to make the connection between the input and the
--   resulting list of indices, and to store additional data.
multiBuildHeapGraph
    :: Monoid a
    => Int -- ^ Search limit
    -> [(a, Box)] -- ^ Starting values with associated data entry
    -> IO (HeapGraph a, [(a, HeapGraphIndex)])
multiBuildHeapGraph limit = generalBuildHeapGraph limit (HeapGraph M.empty)

-- | Adds an entry to an existing 'HeapGraph'.
--
--   Returns the updated 'HeapGraph' and the index of the added value.
addHeapGraph
    :: Monoid a
    => Int -- ^ Search limit
    -> a -- ^ Data to be stored with the added value
    -> Box -- ^ Value to add to the graph
    -> HeapGraph a -- ^ Graph to extend
    -> IO (HeapGraphIndex, HeapGraph a)
addHeapGraph limit d box hg = do
    (hg', [(_,i)]) <- generalBuildHeapGraph limit hg [(d,box)]
    return (i, hg')

-- | Adds the given annotation to the entry at the given index, using the
-- 'mappend' operation of its 'Monoid' instance.
annotateHeapGraph :: Monoid a => a -> HeapGraphIndex -> HeapGraph a -> HeapGraph a
annotateHeapGraph d i (HeapGraph hg) = HeapGraph $ M.update go i hg
  where
    go hge = Just $ hge { hgeData = hgeData hge <> d }

generalBuildHeapGraph
    :: Monoid a
    => Int
    -> HeapGraph a
    -> [(a,Box)]
    -> IO (HeapGraph a, [(a, HeapGraphIndex)])
generalBuildHeapGraph limit _ _ | limit <= 0 = error "buildHeapGraph: limit has to be positive"
generalBuildHeapGraph limit (HeapGraph hg) addBoxes = do
    -- First collect all boxes from the existing heap graph
    let boxList = [ (hgeBox hge, i) | (i, hge) <- M.toList hg ]
        indices | M.null hg = [0..]
                | otherwise = [1 + fst (M.findMax hg)..]

        initialState = (boxList, indices, [])
    -- It is ok to use the Monoid (IntMap a) instance here, because
    -- we will, besides the first time, use 'tell' only to add singletons not
    -- already there
    (is, hg') <- runWriterT (evalStateT run initialState)
    -- Now add the annotations of the root values
    let hg'' = foldl' (flip (uncurry annotateHeapGraph)) (HeapGraph hg') is
    return (hg'', is)
  where
    run = do
        lift $ tell hg -- Start with the initial map
        forM addBoxes $ \(d, b) -> do
            -- Cannot fail, as limit is not zero here
            Just i <- add limit b
            return (d, i)

    add 0  _ = return Nothing
    add n b = do
        -- If the box is in the map, return the index
        (existing,_,_) <- get
        mbI <- liftIO $ findM (areBoxesEqual b . fst) existing
        case mbI of
            Just (_,i) -> return $ Just i
            Nothing -> do
                -- Otherwise, allocate a new index
                i <- nextI
                -- And register it
                modify (\(x,y,z) -> ((b,i):x, y, z))
                -- Look up the closure
                c <- liftIO $ getBoxedClosureData b
                -- Find indicies for all boxes contained in the map
                c' <- T.mapM (add (n-1)) c
                -- Add add the resulting closure to the map
                lift $ tell (M.singleton i (HeapGraphEntry b c' True mempty))
                return $ Just i
    nextI = do
        i <- gets (head . (\(_,b,_) -> b))
        modify (\(a,b,c) -> (a, tail b, c))
        return i

-- | This function updates a heap graph to reflect the current state of
-- closures on the heap, conforming to the following specification.
--
--  * Every entry whose value has been garbage collected by now is marked as
--    dead by setting 'hgeLive' to @False@
--  * Every entry whose value is still live gets the 'hgeClosure' field updated
--    and newly referenced closures are, up to the given depth, added to the graph.
--  * A map mapping previous indicies to the corresponding new indicies is returned as well.
--  * The closure at 'heapGraphRoot' stays at 'heapGraphRoot'
updateHeapGraph :: Monoid a => Int -> HeapGraph a -> IO (HeapGraph a, HeapGraphIndex -> HeapGraphIndex)
updateHeapGraph limit (HeapGraph startHG) = do
    (hg', indexMap) <- runWriterT $ foldM go (HeapGraph M.empty) (M.toList startHG)
    return (hg', (M.!) indexMap)
  where
    go hg (i, hge) = do
        (j, hg') <- liftIO $ addHeapGraph limit (hgeData hge) (hgeBox hge) hg
        tell (M.singleton i j)
        return hg'

-- | Pretty-prints a HeapGraph. The resulting string contains newlines. Example
-- for @let s = \"Ki\" in (s, s, cycle \"Ho\")@:
--
-- >let x1 = "Ki"
-- >    x6 = C# 'H' : C# 'o' : x6
-- >in (x1,x1,x6)
ppHeapGraph :: HeapGraph a -> String
ppHeapGraph (HeapGraph m) = letWrapper ++ ppRef 0 (Just heapGraphRoot)
  where
    -- All variables occuring more than once
    bindings = boundMultipleTimes (HeapGraph m) [heapGraphRoot]

    letWrapper =
        if null bindings
        then ""
        else "let " ++ intercalate "\n    " (map ppBinding bindings) ++ "\nin "

    bindingLetter i = case hgeClosure (iToE i) of
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

    ppEntry prec hge
        | Just s <- isString hge = show s
        | Just l <- isList hge   = "[" ++ intercalate "," (map (ppRef 0) l) ++ "]"
        | Just bc <- disassembleBCO (fmap (hgeClosure . iToE)) (hgeClosure hge)
                                       = app ("_bco" : map (ppRef 10) (concatMap F.toList bc))
        | otherwise = ppClosure ppRef prec (hgeClosure hge)
      where
        app [a] = a  ++ "()"
        app xs = addBraces (10 <= prec) (intercalate " " xs)

    ppRef _ Nothing = "..."
    ppRef prec (Just i) | i `elem` bindings = ppVar i
                        | otherwise = ppEntry prec (iToE i)
    iToE i = m M.! i

    iToUnboundE i = if i `elem` bindings then Nothing else M.lookup i m

    isList :: HeapGraphEntry a -> Maybe ([Maybe HeapGraphIndex])
    isList hge =
        if isNil (hgeClosure hge)
          then return []
          else do
            (h,t) <- isCons (hgeClosure hge)
            ti <- t
            e <- iToUnboundE ti
            t' <- isList e
            return $ (:) h t'

    isString :: HeapGraphEntry a -> Maybe String
    isString e = do
        list <- isList e
        -- We do not want to print empty lists as "" as we do not know that they
        -- are really strings.
        if (null list)
            then Nothing
            else mapM (isChar . hgeClosure <=< iToUnboundE <=< id) list


-- | In the given HeapMap, list all indices that are used more than once. The
-- second parameter adds external references, commonly @[heapGraphRoot]@.
boundMultipleTimes :: HeapGraph a -> [HeapGraphIndex] -> [HeapGraphIndex]
boundMultipleTimes (HeapGraph m) roots = map head $ filter (not.null) $ map tail $ group $ sort $
     roots ++ concatMap (catMaybes . allClosures . hgeClosure) (M.elems m)

-- | This function integrates the disassembler in "GHC.Disassembler". The first
-- argument should a function that dereferences the pointer in the closure to a
-- closure.
--
-- If any of these return 'Nothing', then 'disassembleBCO' returns Nothing
disassembleBCO :: (a -> Maybe (GenClosure b)) -> GenClosure a -> Maybe [BCI b]
-- Disable the assembler
disassembleBCO _ _ | id True = Nothing
disassembleBCO deref (BCOClosure {..}) = do
    opsC <- deref instrs
    litsC <- deref literals
    ptrsC  <- deref bcoptrs
    return $ disassemble (mccPayload ptrsC) (arrWords litsC) (toBytes (bytes opsC) (arrWords opsC))
disassembleBCO _ _ = Nothing

-- Utilities

findM :: (a -> IO Bool) -> [a] -> IO (Maybe a)
findM _p [] = return Nothing
findM p (x:xs) = do
    b <- p x
    if b then return (Just x) else findM p xs

addBraces :: Bool -> String -> String
addBraces True t = "(" ++ t ++ ")"
addBraces False t = t

braceize :: [String] -> String
braceize [] = ""
braceize xs = "{" ++ intercalate "," xs ++ "}"
