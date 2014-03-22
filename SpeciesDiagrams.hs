{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeSynonymInstances      #-}

module SpeciesDiagrams where

import           Data.List                           (intersperse)
import           Data.Tree
import           Diagrams.Backend.Postscript.CmdLine
import           Diagrams.Core.Points
import           Diagrams.Prelude
import           Diagrams.TwoD.Layout.Tree
import           Graphics.SVGFonts.ReadFont

import           Control.Lens                        (_head, _last)

colors :: [Colour Double]
colors = [red, orange, green, blue, purple, brown, grey, black]

labR, arrowGap :: Double
labR     = 0.3
arrowGap = 0.2

aLabels :: [Diagram B R2]
aLabels = map (sized (Dims (4*labR) (4*labR)))
  [ circle 1
  , triangle 1
  , square 1
  , pentagon 1
  , rect 1 1.618
  , rect 1.618 1
  , circle 1 # scaleX 1.618
  , circle 1 # scaleY 1.618
  ]

type EdgeLabel = P2 -> P2 -> Diagram B R2

sLabels :: [EdgeLabel]
sLabels =
  [ connStyle mempty
  , connStyle $ (mempty # lw 0.05)
  , connStyle $ (mempty # dashing [0.1,0.1] 0)
  , connStyle $ (mempty # dashing [0.05,0.15] 0)
  , connStyle $ (mempty # dashing [0.05,0.05,0.1,0.05] 0)
  , \p q -> let v = 0.03 *^ normalized (perp (q .-. p))
            in ((p .+^ v) ~~ (q .+^ v)) <> ((p .-^ v) ~~ (q .-^ v))
  ]
  where
    connStyle sty p q = (p ~~ q) # applyStyle sty
    perp = rotateBy (1/4)

labSty :: Int -> Maybe EdgeLabel
labSty i = Just (sLabels !! i)

leafData :: Int -> Diagram B R2
leafData i = (aLabels !! i) # sized (Dims labR labR) # fc black <> square (labR*1.5) # fc white

text' :: Double -> String -> Diagram B R2
text' d s = (stroke $ textSVG' (TextOpts s lin INSIDE_H KERN False d d)) # fc black # lw 0

labT :: Int -> Diagram B R2
labT n = text' 1 (show n) # scale labR <> lab n

lab :: Int -> Diagram B R2
lab n = lab' (colors !! n)

lab' :: (TrailLike b, Transformable b, HasStyle b, V b ~ R2) => Colour Double -> b
lab' c = circle labR
       # fc white
       # lc c
       # lw (labR / 5)

cyc :: [Int] -> Double -> Diagram B R2
cyc labs r = cyc' (map lab labs) r

cyc' :: (Monoid' a, TrailLike a, Transformable a, HasStyle a, HasOrigin a, V a ~ R2) => [a] -> Double -> a
cyc' labs r
  = mconcat
  . zipWith (\l (p,a) -> l # moveTo p <> a) labs
  $ zipWith rotateBy
      [1/4, 1/4 + 1/(fromIntegral n) .. ]
      (map mkLink labs)
 where
  n = length labs
  mkLink _ = ( origin # translateX r
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
  startAngle = (labR + arrowGap)/r @@ rad
  endAngle   = (tau/fromIntegral n @@ rad) ^-^ startAngle


newtype Cyc a = Cyc {getCyc :: [a]}
  deriving Functor

data Pointed a = Plain a | Pointed a

class Drawable d where
  draw :: d -> Diagram B R2

instance Drawable (Diagram B R2) where
  draw = id

instance Drawable a => Drawable (Cyc a) where
  draw (Cyc ls) = cyc' (map draw ls # sized (Width (labR*2))) 1

instance Drawable a => Drawable [a] where
  draw ls = centerX . hcat' (with & sep .~ 0.1)
          $ intersperse (mkArrow 0.5 mempty) (map draw ls)

instance Drawable a => Drawable (Pointed a) where
  draw (Plain a) = draw a
  draw (Pointed a) = point (draw a)

point :: Diagram B R2 -> Diagram B R2
point d = d <> drawSpN Hole # sizedAs (d # scale 5)

down :: Cyc (Diagram B R2) -> Cyc (Cyc (Pointed (Diagram B R2)))

down (Cyc ls) = Cyc (map Cyc (pointings ls))

pointings :: [a] -> [[Pointed a]]
pointings []     = []
pointings (x:xs) = (Pointed x : map Plain xs) : map (Plain x :) (pointings xs)

elimArrow :: Diagram B R2
elimArrow = (hrule 2 # lw 0.03)
        ||| eqTriangle 0.2 # rotateBy (-1/4) # fc black

mkArrow :: Double -> Diagram B R2 -> Diagram B R2
mkArrow len l =
  ( l
    ===
    arrow len # lw 0.03
  )
  # alignB

(|-|) :: Diagram B R2 -> Diagram B R2 -> Diagram B R2
x |-| y = x ||| strutX 1 ||| y

data SpN = Lab (Either Int String)
         | Leaf (Maybe (Diagram B R2))
         | Hole
         | Point
         | Sp (Diagram B R2) Angle
         | Bag

type SpT = Tree (Maybe EdgeLabel, SpN)

drawSpT' :: T2 -> SymmLayoutOpts (Maybe EdgeLabel, SpN) -> SpT -> Diagram B R2
drawSpT' tr slopts
  = transform tr
  . renderTree' (drawSpN' (inv tr) . snd) drawSpE
  . symmLayout' slopts

drawSpT :: SpT -> Diagram B R2
drawSpT = drawSpT' (rotation (1/4 @@ turn))
                   (with & slHSep .~ 0.5 & slVSep .~ 2 & slWidth .~ slw)
  where
    slw (_, Leaf (Just d)) = (-width d/2, width d/2)
    slw (_, sp@(Sp _ _)) = let w = width (drawSpN' (rotation (1/4 @@ turn)) sp)
                           in  (-w/2, w/2)
    slw _ = (0,0)

drawSpN' :: Transformation R2 -> SpN -> Diagram B R2
drawSpN' _  (Lab (Left n))    = lab n # scale 0.5
drawSpN' tr (Lab (Right t))   = (drawSpN' tr (Leaf Nothing) ||| strutX (labR/2) ||| text' 0.3 t) # transform tr
drawSpN' _  (Leaf Nothing)  = circle (labR/2) # fc black
drawSpN' _  (Leaf (Just d)) = d
drawSpN' _  Hole              = circle (labR/2) # lw (labR / 10) # fc white
drawSpN' tr Point             = drawSpN' tr (Leaf Nothing) <> drawSpN' tr Hole # scale 1.7
drawSpN' tr (Sp s f) = ( arc ((3/4 @@ turn) ^-^ f^/2) ((3/4 @@ turn) ^+^ f^/2) # scale 0.3
                       |||
                       strutX 0.1
                       |||
                       s # transform tr
                       )
drawSpN' _  Bag     =
                ( text' 1 "{" # scale 0.5 ||| strutX (labR/4)
                  ||| circle (labR/2) # fc black
                  ||| strutX (labR/4) ||| text' 1 "}" # scale 0.5
                ) # centerX

drawSpN :: SpN -> Diagram B R2
drawSpN = drawSpN' mempty

drawSpE :: (t, P2) -> ((Maybe EdgeLabel, SpN), P2) -> Diagram B R2
drawSpE (_,p) ((_,Hole),q) = (p ~~ q) # dashing [0.05,0.05] 0
drawSpE (_,p) ((Just f,_), q) = f p q
drawSpE (_,p) (_,q) = p ~~ q

nd :: Diagram B R2 -> Forest (Maybe EdgeLabel, SpN) -> SpT
nd x = Node (Nothing, Sp x (1/3 @@ turn))

nd' :: EdgeLabel -> Diagram B R2 -> Forest (Maybe EdgeLabel, SpN) -> SpT
nd' l x = Node (Just l, Sp x (1/3 @@ turn))

lf :: a -> Tree (Maybe EdgeLabel, a)
lf x = Node (Nothing, x) []

lf' :: EdgeLabel -> a -> Tree (Maybe EdgeLabel, a)
lf' l x = Node (Just l, x) []

struct :: Int -> String -> Diagram B R2
struct n x = drawSpT (struct' n x)
           # centerXY

struct' :: Int -> String -> SpT
struct' n x = struct'' n (text' 1 x <> rect 2 1 # lw 0)

struct'' :: Int -> Diagram B R2 -> SpT
struct'' n d = nd d (replicate n (lf (Leaf Nothing)))

linOrd :: [Int] -> Diagram B R2
linOrd ls =
    connect' (with & arrowHead .~ noHead) "head" "last"
  . hcat' (with & sep .~ 0.5)
  $ map labT ls & _head %~ named "head" & _last %~ named "last"

unord :: (Monoid' b, Semigroup b, TrailLike b, Alignable b, Transformable b, HasStyle b, Juxtaposable b, HasOrigin b, Enveloped b, V b ~ R2) => [b] -> b
unord [] = circle 1 # lw 0.1 # lc gray
unord ds = elts # centerXY
           <> roundedRect w (mh + s*2) ((mh + s*2) / 5)
  where
    elts  = hcat' (with & sep .~ s) ds
    mw    = maximum' 0 . map width  $ ds
    s     = mw * 0.5
    mh    = maximum' 0 . map height $ ds
    w     = ((fromIntegral (length ds + 1) * s) +) . sum . map width $ ds
    maximum' d [] = d
    maximum' _ xs = maximum xs

enRect :: (Semigroup a, TrailLike a, Alignable a, Enveloped a, HasOrigin a, V a ~ R2) => a -> a
enRect d = roundedRect (w+0.5) (h+0.5) 0.5 <> d # centerXY
  where (w,h) = size2D d

txt x = text x <> square 1 # lw 0
