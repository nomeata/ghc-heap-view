{-# LANGUAGE MagicHash, BangPatterns #-}

import GHC.Exts
import GHC.HeapView
import Control.DeepSeq

import System.Environment
import System.Mem

import Control.Monad

l = [1,2,3]

main = do
    args <- map length `fmap` getArgs
    let l2 = 4:l
    (l ++ l2 ++ args) `deepseq` return ()

    let x = l ++ l2 ++ args
    performGC
    cl <- getClosureData l
    case cl of ConsClosure {} -> return ()
    unless (name cl == ":") $ do
        fail "Wrong name"

    cl <- getClosureData l2
    case cl of ConsClosure {} -> return ()
    eq <- areBoxesEqual (ptrArgs cl !! 1) (asBox l)
    unless eq $ do
        fail "Doesnt reference l"

    cl <- getClosureData args
    unless (tipe (info cl) == CONSTR_NOCAF_STATIC) $ do
        fail "Not a CONSTR_NOCAF_STATIC"

    cl <- getClosureData x
    unless (tipe (info cl) == THUNK_2_0) $ do
        fail "Not a THUNK_2_0"


    let !(I# m) = length args + 42
    let !(I# m') = length args + 23
    let f = \x n -> take (I# m + I# x) n ++ args
        t = f m' l2

    cl <- getClosureData f
    unless (tipe (info cl) == FUN_1_1) $ do
        fail "Not a FUN_1_1"
    unless (dataArgs cl == [42]) $ do
        fail "Wrong data arg"
    cl <- getClosureData t
    unless (tipe (info cl) == THUNK) $ do
        fail "Not a THUNK"
    unless (dataArgs cl == [23]) $ do
        fail "Wrong data arg"
    eq <- areBoxesEqual (ptrArgs cl !! 1) (asBox f)
    unless eq $ do
        fail "t doesnt reference f"

    let x = id (:) () x
    x `seq` return ()
    performGC
    cl <- getClosureData x
    case cl of ConsClosure {} -> return ()
    eq <- areBoxesEqual (ptrArgs cl !! 1) (asBox x)
    unless eq $ do
        fail "x doesnt reference itself"
