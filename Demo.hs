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
    putStrLn "Here are a few different lists."
    putStrLn $ "The first one, l, found at " ++ show (asBox l) ++ " is a module-level constant, and fully evaluated:"
    getClosureData l >>= print
    putStrLn $ "The second one, l2, found at " ++ show (asBox l2) ++ " is locally defined as l2 = 4:l. See how the cons-cell references l!"
    getClosureData l2 >>= print
    putStrLn $ "And here is the list args (" ++ show (asBox args) ++ ") that is static, but not known at compiletime, as it depends on the command line arguments:"
    getClosureData args >>= print
    putStrLn $ "And now we have, at " ++ show (asBox x) ++ ", the concatenation of them, but unevaluated. The thunk keeps a reference to l2 and args, but not l, as that is at a static address, unless you are running this in GHCi:"
    getClosureData x >>= print

    putStrLn ""
    putStrLn "Now to some more closure types:"
    let !(I# m) = length args + 42
    let !(I# m') = length args + 23
    let f = \x n -> take (I# m + I# x) n ++ args
        t = f m' l2
    putStrLn $ "The following value f (" ++ show (asBox f) ++ ") is a locally defined function that has args as a free variable, as well as an unboxed integer (42):"
    getClosureData f >>= print
    putStrLn "And the following is a thunk that applies f (also references here) to an unboxed value (23) and l2:"
    getClosureData t >>= print

    putStrLn ""
    putStrLn "Here is the standard example for self reference:"
    putStrLn "> let x = id (:) () x"
    let x = id (:) () x
    putStrLn $ "This is what x (" ++ show (asBox x) ++ ") looks like, at least without -O:"
    getClosureData x >>= print
    x `seq` return ()
    putStrLn $ "So it is unevaluated. Let us evaluate it using seq. Now we have, still at " ++ show (asBox x) ++ ":"
    getClosureData x >>= print
    IndClosure {indirectee = target} <- getClosureData x
    putStrLn $ "The thunk was replaced by an indirection. If we look at the target, " ++ show target ++ ", we see that it is a newly created cons-cell referencing the original location of x:"
    getBoxedClosureData target >>= print
    performGC
    putStrLn $ "After running the garbage collector (performGC), we find that the address of x is now " ++ show (asBox x) ++ " and that the self-reference is without indirections:"
    getClosureData x >>= print


recurse :: Int -> Box -> IO ()
recurse m = go 0
  where go i b = if i >= m then return () else do
            putStrLn $ ind ++ show b
            c <- getBoxedClosureData b
            putStrLn $ ind ++ show c
            mapM_ (go (succ i)) (allPtrs c)
          where
            ind = concat $ replicate i "  "
