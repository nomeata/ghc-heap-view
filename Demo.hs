{-# LANGUAGE MagicHash, BangPatterns #-}

import GHC.Exts
import GHC.HeapView
import Control.DeepSeq

import System.Environment
import System.Mem

l = [1,2,3]

main = do
    args <- map length `fmap` getArgs
    let l2 = 4:l
    (l ++ l2 ++ args) `deepseq` return ()

    let x = l ++ l2 ++ args
    performGC
    putStrLn "ghc-heap-view-demo"
    putStrLn ""
    putStrLn "Here are a four different lists, where the first three are already evaluated."
    putStrLn "The first one, l, was defined as a top level constant as "
    putStrLn "> l = [1,2,3]"
    putStrLn $ "and is now found at " ++ show (asBox l) ++ " (where the /2 is the pointer tag information) and fully evaluated:"
    getClosureData l >>= printInd
    putStrLn $ "The second one, l2, is locally defined"
    putStrLn "> let l2 = 4:l" 
    putStrLn $ "and now found at " ++ show (asBox l2) ++ ". See how the cons-cell references l!"
    getClosureData l2 >>= printInd
    putStrLn "And the binding"
    putStrLn "> args <- map length `fmap` getArgs"
    putStrLn $ "gives us at " ++ show (asBox args) ++ " a static, but at compile time unknown list:"
    getClosureData args >>= printInd
    putStrLn $ "And now we have, at " ++ show (asBox x) ++ ", the concatenation of them, but unevaluated:"
    putStrLn "> let x = l ++ l2 ++ args"
    putStrLn "The thunk keeps a reference to l2 and args, but not l, as that is at a static address, unless you are running this in GHCi:"
    getClosureData x >>= printInd

    putStrLn ""
    putStrLn "Now to some more closure types. m and m' locally bound of type the unboxed type Int#, with values 42 resp. 23."
    putStrLn "> let f = \\x n -> take (I# m + I# x) n ++ args"
    putStrLn "      t = f m' l2"
    let !(I# m) = length args + 42
    let !(I# m') = length args + 23
    let f = \x n -> take (I# m + I# x) n ++ args
        t = f m' l2
    putStrLn $ "So here is (" ++ show (asBox f) ++ "), referencing its free variables args and 42:"
    getClosureData f >>= printInd
    putStrLn "And t is a thunk that applies f (also referenced here) to an unboxed value (23) and l2:"
    getClosureData t >>= printInd

    putStrLn ""
    putStrLn "Lastly, here is the standard example for self reference:"
    putStrLn "> let x = id (:) () x"
    let x = id (:) () x
    putStrLn $ "This is what x (" ++ show (asBox x) ++ ") looks like, at least without -O:"
    getClosureData x >>= printInd
    x `seq` return ()
    putStrLn $ "So it is unevaluated. Let us evaluate it using seq. Now we have, still at " ++ show (asBox x) ++ ":"
    getClosureData x >>= printInd
    target <- indirectee `fmap` getClosureData x
    putStrLn $ "The thunk was replaced by an indirection. If we look at the target, " ++ show target ++ ", we see that it is a newly created cons-cell referencing the original location of x:"
    getBoxedClosureData target >>= printInd
    performGC
    putStrLn $ "After running the garbage collector (performGC), we find that the address of x is now " ++ show (asBox x) ++ " and that the self-reference is without indirections:"
    getClosureData x >>= printInd

printInd :: Show a => a -> IO ()
printInd x = putStrLn $ "    " ++ show x

recurse :: Int -> Box -> IO ()
recurse m = go 0
  where go i b = if i >= m then return () else do
            putStrLn $ ind ++ show b
            c <- getBoxedClosureData b
            putStrLn $ ind ++ show c
            mapM_ (go (succ i)) (allPtrs c)
          where
            ind = concat $ replicate i "  "
