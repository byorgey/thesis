{-# LANGUAGE NoMonomorphismRestriction #-}
module Diagrams where

import           Control.Arrow             (first, second)
import           Data.List.Split
import qualified Data.Map                  as M
import           Data.Maybe
import           Data.Tree
import           Diagrams.Prelude
import           Diagrams.TwoD.Layout.Tree


import           Diagrams.Backend.Cairo

locColor = blend 0.5 white lightblue
eltColor = blend 0.5 white lightgreen

loc m = text (show m) <> circle 0.8 # fc locColor
elt x = text (show x) <> square 1.6 # fc eltColor

arm m n r = ( loc m # rotateBy (-r)
          ||| hrule 1.5
          ||| loc n # rotateBy (-r)
            )
            # translateX 3
            # rotateBy r

arms elts = zipWith (\[e1,e2] r -> arm e1 e2 r) (chunksOf 2 elts) [1/8 + 0.001, 1/8+0.001 +1/4 .. 1]

octo elts = (mconcat (arms elts) <> circle 3) # lw 0.03

t = Node 3 [Node 4 (map lf [2,1,6]), Node 5 [], Node 0 [lf 7]]
lf x = Node x []

tree :: Diagram Cairo R2
tree = renderTree
         loc
         (~~)
         (symmLayout' with { slHSep = 4, slVSep = 4 } t)
       # lw 0.03

drawBinTree :: SymmLayoutOpts (Maybe (Diagram Cairo R2))
            -> BTree (Diagram Cairo R2) -> Diagram Cairo R2
drawBinTree slOpts = drawRTree . symmLayout' slOpts . b2r

b2r Empty                 = Node Nothing []
b2r (BNode a Empty Empty) = Node (Just a) []
b2r (BNode a l r)         = Node (Just a) (map b2r [l,r])
drawRTree = renderTree' drawNode drawEdge
drawNode Nothing  = mempty
drawNode (Just d) = d
drawEdge _ (Nothing,_)   = mempty
drawEdge (_,pt1) (_,pt2) = pt1 ~~ pt2

select :: [a] -> [(a,[a])]
select [] = []
select (a:as) = (a,as) : (map . second) (a:) (select as)

subsets :: [a] -> [([a],[a])]
subsets [] = [([],[])]
subsets (a:as) = (map . first) (a:) s ++ (map . second) (a:) s
  where s = subsets as

type Edge = (Int,Int)
type Graph = (M.Map Int P2, [Edge])

drawGraph drawLoc (locs, edges) = drawLocs <> drawEdges
  where
    drawLocs  = mconcat . map (\(n,p) -> drawLoc n # moveTo p) . M.assocs $ locs
    drawEdges = mconcat . map drawEdge $ edges
    drawEdge (i1,i2) = lkup i1 ~~ lkup i2
    lkup i = fromMaybe origin $ M.lookup i locs

gr  = drawGraph loc
        ( M.fromList
          [ (0, 3 & (-1))
          , (1, 8 & 0)
          , (2, origin)
          , (3, 8 & 2)
          , (4, 4 & 2)
          , (5, 3 & (-3))
          ] # scale 1.5
        , [(2,0), (2,4), (0,4), (4,3), (3,1), (0,1), (0,5)]
        )
