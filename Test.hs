{-# LANGUAGE MagicHash, BangPatterns, CPP #-}

import GHC.Exts
import GHC.HeapView

import Control.DeepSeq
import Control.Monad
import Control.Applicative (pure)

import System.Environment
import System.Mem


main :: IO ()
main = do
    args <- map length `fmap` getArgs
    let list2 = 4:list
    (list ++ list2 ++ args) `deepseq` pure ()

    let x = list ++ list2 ++ args
    performGC
    getClosureAssert list >>= \ cl ->
        unless (name cl == ":") $ fail "Wrong name"

    getClosureAssert list2 >>= \ cl -> do
        eq <- areBoxesEqual (ptrArgs cl !! 1) (asBox list)
        unless eq $ fail "Doesn't reference list"

    getClosureData args >>= \ cl ->
#if MIN_VERSION_GLASGOW_HASKELL(8,1,0,0)
        assertClosureType CONSTR_0_1 (info cl)
#else
        assertClosureType CONSTR_NOCAF_STATIC (info cl)
#endif

    getClosureData x >>= \ cl ->
        assertClosureType THUNK_2_0 (info cl)

    let !(I# m) = length args + 42
    let !(I# m') = length args + 23
    let f = \ y n -> take (I# m + I# y) n ++ args
    performGC

    getClosureData f >>= \ cl -> do
        assertClosureType FUN_1_1 (info cl)
        unless (dataArgs cl == [42]) $ do
            fail "Wrong data arg"

    let t = f m' list2
    getClosureData t >>= \ cl -> do
        assertClosureType THUNK (info cl)
        unless (dataArgs cl == [23]) $ do
            fail "Wrong data arg"

        eq <- areBoxesEqual (ptrArgs cl !! 1) (asBox f)
        unless eq $ fail "t doesnt reference f"

    let z = id (:) () z
    z `seq` pure ()
    performGC
    getClosureAssert z >>= \ cl -> do
        eq <- areBoxesEqual (ptrArgs cl !! 1) (asBox z)
        unless eq $
            fail "z doesnt reference itself"

    putStrLn "Done. No errors."


list :: [Int]
list = [1,2,3]


getClosureAssert :: a -> IO Closure
getClosureAssert x = do
    cl <- getClosureData x
    case cl of
        ConsClosure {} -> pure cl
        _ -> fail "Expected ConsClosure"


assertClosureType :: ClosureType -> StgInfoTable -> IO ()
assertClosureType expected itable = do
    let actual = tipe itable
    unless (actual == expected) $
        fail $ "Expected " ++ show expected ++ " but got " ++ show actual
