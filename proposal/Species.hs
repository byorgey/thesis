{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
module Species where

import Data.List (intersperse)
import Data.Tree
import Diagrams.Backend.Cairo.CmdLine
import Diagrams.Core.Points
import Diagrams.Prelude hiding ((&))
import Diagrams.TwoD.Layout.Tree

import Control.Lens (_head, _last, (%~), (&))

colors = [red, orange, green, blue, purple, brown, grey, black]

labR     = 0.3
arrowGap = 0.2

labT :: Int -> Diagram Cairo R2
labT n = text (show n) # scale labR <> lab n

lab :: Int -> Diagram Cairo R2
lab n = lab' (colors !! n)

lab' c = circle labR
       # fc white
       # lc c
       # lw (labR / 5)

cyc :: [Int] -> Double -> Diagram Cairo R2
cyc labs r = cyc' (map lab labs) r

cyc' labs r
  = mconcat
  . zipWith (\l (p,a) -> l # moveTo p <> a) labs
  $ zipWith rotateBy
      [1/4, 1/4 + 1/(fromIntegral n) .. ]
      (map mkLink labs)
 where
  n = length labs
  mkLink l = ( origin # translateX r
             ,
               ( arc startAngle endAngle
                 # scale r
                 <>
                 eqTriangle 0.1
                 # translateX r
                 # rotate endAngle
                 # fc black
               )
               # lw (labR / 10)
             )
  startAngle = Rad $ (labR + arrowGap)/r
  endAngle   = Rad (tau/(fromIntegral n)) - startAngle

newtype Cyc a = Cyc {getCyc :: [a]}
  deriving Functor

data Pointed a = Plain a | Pointed a

class Drawable d where
  draw :: d -> Diagram Cairo R2

instance Drawable (Diagram Cairo R2) where
  draw = id

instance Drawable a => Drawable (Cyc a) where
  draw (Cyc ls) = cyc' (map draw ls # sized (Width (labR*2))) 1

instance Drawable a => Drawable [a] where
  draw ls = centerX . hcat' with {sep = 0.1}
          $ intersperse (arrow 0.5 mempty) (map draw ls)

instance Drawable a => Drawable (Pointed a) where
  draw (Plain a) = draw a
  draw (Pointed a) = point (draw a)

point d = d <> drawSpN Hole # sizedAs (d # scale 5)

down :: Cyc (Diagram Cairo R2) -> Cyc (Cyc (Pointed (Diagram Cairo R2)))
down (Cyc ls) = Cyc (map Cyc (pointings ls))

pointings []     = []
pointings (x:xs) = (Pointed x : map Plain xs) : map (Plain x :) (pointings xs)

elimArrow :: Diagram Cairo R2
elimArrow = (hrule 2 # lw 0.03)
        ||| eqTriangle 0.2 # rotateBy (-1/4) # fc black

arrow len l =
  ( l
    ===
    hrule len # lw 0.03
  )
  # alignB
  |||
  eqTriangle 0.2 # rotateBy (-1/4) # fc black

x |-| y = x ||| strutX 1 ||| y

data SpN = Lab Int | Leaf | Hole | Point | Sp (Diagram Cairo R2) CircleFrac | Bag

type SpT = Tree SpN

drawSpT' tr slopts
  = transform tr
  . renderTree' (drawSpN' (inv tr)) drawSpE
  . symmLayout' slopts

drawSpT = drawSpT' (rotation (1/4 :: CircleFrac))
                   with {slHSep = 0.5, slVSep = 2}

drawSpN' :: Transformation R2 -> SpN -> Diagram Cairo R2
drawSpN' tr (Lab n)  = lab n # scale 0.5
drawSpN' tr Leaf     = circle (labR/2) # fc black
drawSpN' tr Hole     = circle (labR/2) # lw (labR / 10) # fc white
drawSpN' tr Point    = drawSpN' tr Leaf <> drawSpN' tr Hole # scale 1.7
drawSpN' tr (Sp s f) = ( arc (3/4 - f/2) (3/4 + f/2)
                       |||
                       strutX 0.2
                       |||
                       s # transform tr
                       )
                       # scale 0.3
drawSpN' tr Bag     =
                ( (text "{" <> square 1 # lw 0) # scale 0.5 ||| strutX (labR/4)
                  ||| circle (labR/2) # fc black
                  ||| strutX (labR/4) ||| (text "}" <> square 1 # lw 0) # scale 0.5
                ) # centerX

drawSpN = drawSpN' mempty

drawSpE (_,p) (Hole,q) = (p ~~ q) # dashing [0.05,0.05] 0
drawSpE (_,p) (_,q)    = p ~~ q

nd x = Node (Sp x (1/2))
lf x = Node x []

main = -- defaultMain (arrow 1 ((text "f" <> strutY 1) # scale 0.5))

 defaultMain (draw (down (Cyc [lab 0, lab 1, lab 2])))

-- defaultMain (draw (Cyc [Cyc [lab 0, lab 4], Cyc [lab 1, lab 2, lab 3]]))
-- (cyc' (replicate 5 (square 0.2 :: Diagram Cairo R2)) 1)

-- defaultMain (drawSpT (nd 'F' [lf Leaf, lf Hole, Node Bag (map lf [Leaf, Leaf, Hole, Leaf])]))

struct n x = drawSpT (struct' n x)
           # centerXY

struct' n x = nd (text x <> rect 2 1 # lw 0) (replicate n (lf Leaf))

txt s = text s <> square 1 # lw 0

linOrd ls =
    connect
  . hcat' with {sep = 0.5}
  $ map labT ls & _head %~ named "head" & _last %~ named "last"
  where
    connect =
      withNames ["head", "last"] $ \[h,l] ->
        beneath (location h ~~ location l)