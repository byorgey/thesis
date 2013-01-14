module Diagrams where

import Diagrams.Prelude
import Diagrams.TwoD.Layout.Tree
import Data.Tree
import Data.List.Split

import Diagrams.Backend.Cairo

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
