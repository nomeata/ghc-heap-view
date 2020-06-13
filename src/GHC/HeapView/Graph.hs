{-# LANGUAGE CPP, LambdaCase, RecordWildCards #-}
{- | Conversions between 'HeapGraph' and 'Graph'.

You may also be interested in the @graphviz@ package which has conversions
between 'Graph' and the DOT format, which can be visualised by other tools.

>>> import GHC.HeapView
>>> import GHC.HeapView.Graph
>>> import qualified Data.GraphViz as GV
>>> import qualified Data.GraphViz.Printing as GV
>>> import Data.Text.Lazy (unpack)
>>> hg <- buildHeapGraph 50 ["root"] $ asBox yourRoot
>>> putStrLn $ ppHeapGraph hg
>>> let dg = GV.graphToDot GV.quickParams $ asStrGraph hg
>>> putStrLn $ unpack $ GV.renderDot $ GV.toDot dg
-}
module GHC.HeapView.Graph where

import GHC.HeapView
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree (Gr)

import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
#if MIN_VERSION_transformers(0,5,6)
import Control.Monad.Trans.Writer.CPS
#else
import Control.Monad.Trans.Writer.Strict
#endif
import qualified Data.IntMap as M
import qualified Data.Foldable as F
import Data.List

{- | Convert a 'HeapGraph' to a 'Graph', most general form.

The first parameter creates a node label and is called for each node. It takes
the 'HeapGraph' user data, the 'HeapGraphEntry' of that node, a string name for
the node, and a string description of the node's contents.

The second parameter creates an edge label and is called for each edge. It
takes the source node label, the 'HeapGraphEntry' of the target node, and a
string name for the target node.
-}
asGraph
  :: DynGraph gr
  => (a -> HeapGraphEntry a -> String -> String -> v)
  -> (v -> HeapGraphEntry a -> String -> e)
  -> HeapGraph a
  -> gr v e
asGraph mkNodeLabel mkEdgeLabel (HeapGraph m) = M.foldrWithKey build empty m
  where
    build k e g =
      let (r, kk) = runWriter $ ppEntry e
          v  = mkNodeLabel (hgeData e) e (ppVar k) r
          g1 = insNode (k, v) g
          g2 = foldr (\k' g' -> insEdge (k, k', mkEdgeLabel v (m M.! k') (ppVar k')) g') g1 kk
      in g2

    bindings = allBindings (HeapGraph m) [heapGraphRoot]
    ppBindingMap' = ppBindingMap m bindings
    ppVar i = ppBindingMap' M.! i

    ppEntry hge = do
      runMaybeT (isString hge) >>= \case
        Just s -> pure $ show s
        Nothing -> runMaybeT (isList hge) >>= \case
          Just l -> (\x -> "[" ++ intercalate "," x ++ "]") <$> traverse ppRef l
          Nothing -> case disassembleBCO (fmap (hgeClosure . (m M.!))) (hgeClosure hge) of
            Just bc -> app <$> ("_bco" :) <$> traverse ppRef (concatMap F.toList bc)
            Nothing -> ppClosureF (const ppRef) 0 (hgeClosure hge)
      where
        app [a] = a  ++ "()"
        app xs = intercalate " " xs

    ppRef Nothing = pure "..."
    ppRef (Just i) = do
      tell [i]
      pure (ppVar i)

    iToUnboundEF i = if i `elem` bindings
      then MaybeT . pure $ Nothing
      else do
        lift $ tell [i]
        MaybeT . pure $ M.lookup i m

    isList hge = isListF iToUnboundEF hge

    isString e = isStringF iToUnboundEF e

-- | 'asGraph' specialised to 'Gr' a concrete graph.
-- For convenience for people unfamiliar with @fgl@.
asAGraph
  :: (a -> HeapGraphEntry a -> String -> String -> b)
  -> (b -> HeapGraphEntry a -> String -> e)
  -> HeapGraph a
  -> Gr b e
asAGraph = asGraph

-- | 'asGraph' with default values for @mkNodeLabel@ and @mkEdgeLabel@
asStrGraph :: Show a => HeapGraph [a] -> Gr String String
asStrGraph = asGraph mkNode mkEdge
  where
    mkNode d _ k v = maybeShow d <> k <> " =\n" <> fmap trSp v
    mkEdge _ _ k' = k'
    maybeShow d = if null d then "" else show d <> " // "
    trSp ' ' = '\n'
    trSp c = c
