{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE TypeSynonymInstances      #-}

module Bijections where

import           Control.Arrow          ((&&&))
import           Control.Lens           (makeLenses, mapped, (^.), _2)
import           Control.Monad          (msum)
import           Data.Default.Class
import           Data.List              (findIndex, isSuffixOf, partition)
import qualified Data.Map               as M
import           Data.Maybe             (catMaybes, fromMaybe)
import           Data.Typeable

import           Diagrams.Backend.Cairo
import           Diagrams.Core.Names
import           Diagrams.Prelude       hiding (end, r2, start)
import           Graphics.SVGFonts

------------------------------------------------------------
-- Diagram utilities

type Dia = Diagram Cairo R2

dot :: Dia
dot = circle 0.3 # fc black # lw none

text' :: Double -> String -> Dia
text' d t = stroke (textSVG' $ TextOpts t lin INSIDE_H KERN False d d) # fc black

------------------------------------------------------------
-- Name utilities

disjointly :: Qualifiable q => ([q] -> q) -> [q] -> q
disjointly f = f . zipWith (|>) ['a'..]

(|@) :: Char -> Int -> Name
c |@ i = c |> toName i

(|@@) :: Char -> [Int] -> [Name]
c |@@ is = map (c |@) is

------------------------------------------------------------
-- Parallel composition

-- Parallel composition is not necessarily associative, nor is empty
-- an identity.
class Par p where
  empty :: p
  par   :: p -> p -> p
  par x y = pars [x,y]
  pars  :: [p] -> p
  pars = foldr par empty

------------------------------------------------------------
-- Sets

data ASet =
  ASet
  { _eltNames :: [Name]
  , _setColor :: Colour Double
  }

$(makeLenses ''ASet)

instance Qualifiable ASet where
  n |> s = s & eltNames %~ (n|>)

type Set = [ASet]

instance Par Set where
  empty = []
  pars  = disjointly concat

nset :: Int -> Colour Double -> ASet
nset n c = ASet (map toName [0::Int .. (n-1)]) c

set :: IsName n => [n] -> Colour Double -> ASet
set ns c = ASet (map toName ns) c

drawSet :: Set -> Dia
drawSet = centerY . vcat . zipWithMult (|>) ['a'..] . map drawAtomic . annot . annot
  where
    zipWithMult _ _ [x] = [x]
    zipWithMult f xs ys = zipWith f xs ys
    annot = reverse . zip (False : repeat True)
    drawAtomic (bot, (top, ASet nms c))
      = mconcat
        [ vcat' (with & sep .~ 1 & catMethod .~ Distrib)
          (zipWith named nms (replicate (length nms) dot))
          # centerY
        , roundedRect' 1 (fromIntegral (length nms))
          (with & radiusTL .~ (if top then 0 else (1/2))
                & radiusTR .~ (if top then 0 else (1/2))
                & radiusBL .~ (if bot then 0 else (1/2))
                & radiusBR .~ (if bot then 0 else (1/2))
          )
          # fcA (c `withOpacity` 0.5)
        ]

------------------------------------------------------------
-- Bijections

data ABij
  = ABij
    { _bijDomain :: [Name]
    , _bijData   :: Name -> Maybe Name
    , _bijStyle  :: Name -> Style R2
    , _bijSep    :: Double
    , _bijLabel  :: Maybe Dia
    }

$(makeLenses ''ABij)

instance Qualifiable ABij where
  n |> bij = bij & bijData %~ prefixF n & bijDomain %~ (n |>)
    where
      prefixF :: IsName a => a -> (Name -> Maybe Name) -> (Name -> Maybe Name)
      prefixF _ _ (Name [])     = Just $ Name []
      prefixF i f (Name (AName a : as)) =
        case cast a of
          Nothing -> Nothing
          Just a' -> if a' == i then (i |>) <$> f (Name as) else Nothing

bijFun :: [Int] -> (Int -> Maybe Int) -> ABij
bijFun is f = def & bijDomain .~ toNamesI is & bijData .~ fmap toName . f . extractInt 0
  where
    extractInt :: Int -> Name -> Int
    extractInt i (Name []) = i
    extractInt i (Name ns) = case last ns of
                               AName a -> case cast a of
                                 Nothing -> i
                                 Just i' -> i'

bijTable :: [(Name, Name)] -> ABij
bijTable tab = def & bijDomain .~ map fst tab & bijData .~ tableToFun tab

mkABij :: ASet -> ASet -> (Int -> Int) -> ABij
mkABij s1 s2 f = def & bijDomain .~ (s1 ^. eltNames)
                     & bijData   .~ \n -> findIndex (==n) (s1 ^. eltNames) >>= ((s2^.eltNames) !!!) . f

-- mkBij :: Set -> Set -> (Int -> Int) -> Bij
-- mkBij ss1 ss2 f = undefined

(!!!) :: [a] -> Int -> Maybe a
[] !!! _     = Nothing
(x:_) !!! 0  = Just x
(_:xs) !!! n = xs !!! (n-1)

tableToFun :: Eq a => [(a, b)] -> a -> Maybe b
tableToFun = flip lookup

instance Default ABij where
  def = ABij
    { _bijDomain = []
    , _bijData   = const Nothing
    , _bijStyle  = const $ mempty # dashingG [0.03,0.02] 0 # lineCap LineCapButt
    , _bijSep    = 3
    , _bijLabel  = Nothing
    }

type Bij = [ABij]

emptyBij :: Bij
emptyBij = [with & bijData .~ const Nothing]

parBij :: Bij -> Bij -> Bij
parBij x y = parBijs [x,y]

parBijs :: [Bij] -> Bij
parBijs = disjointly concat

labelBij :: String -> Bij -> Bij
labelBij s = (mapped . bijLabel) .~ Just (text' 2 s)

------------------------------------------------------------
-- Alternating lists

data AltList a b
  = Single a
  | Cons a b (AltList a b)

infixr 5 .-, -., -..

(.-) :: a -> (b, AltList a b) -> AltList a b
a .- (b,l) = Cons a b l

(-.) :: b -> AltList a b -> (b, AltList a b)
(-.) = (,)

(-..) :: b -> a -> (b,AltList a b)
b -.. a = (b, Single a)

zipWithA :: (a1 -> a2 -> a3) -> (b1 -> b2 -> b3) -> AltList a1 b1 -> AltList a2 b2 -> AltList a3 b3
zipWithA f _ (Single x1) (Single x2)         = Single (f x1 x2)
zipWithA f _ (Single x1) (Cons x2 _ _)       = Single (f x1 x2)
zipWithA f _ (Cons x1 _ _) (Single x2)       = Single (f x1 x2)
zipWithA f g (Cons x1 y1 l1) (Cons x2 y2 l2) = Cons (f x1 x2) (g y1 y2) (zipWithA f g l1 l2)

concatA :: AltList a b -> b -> AltList a b -> AltList a b
concatA (Single a) b l     = Cons a b l
concatA (Cons a b l) b' l' = Cons a b (concatA l b' l')

flattenA :: AltList (AltList a b) b -> AltList a b
flattenA (Single l) = l
flattenA (Cons l b l') = concatA l b (flattenA l')

map1 :: (a -> b) -> AltList a c -> AltList b c
map1 f (Single a) = Single (f a)
map1 f (Cons a b l) = Cons (f a) b (map1 f l)

map2 :: (b -> c) -> AltList a b -> AltList a c
map2 _ (Single a) = Single a
map2 g (Cons a b l) = Cons a (g b) (map2 g l)

iterateA :: (a -> b) -> (b -> a) -> a -> AltList a b
iterateA f g a = Cons a b (iterateA f g (g b))
  where b = f a

takeWhileA :: (b -> Bool) -> AltList a b -> AltList a b
takeWhileA _ (Single a) = Single a
takeWhileA p (Cons a b l)
  | p b = Cons a b (takeWhileA p l)
  | otherwise = Single a

foldA :: (a -> r) -> (a -> b -> r -> r) -> AltList a b -> r
foldA f _ (Single a)   = f a
foldA f g (Cons a b l) = g a b (foldA f g l)

------------------------------------------------------------
-- Bijection complexes

type BComplex = AltList Set Bij

labelBC :: String -> BComplex -> BComplex
labelBC = map2 . labelBij

seqC :: BComplex -> Bij -> BComplex -> BComplex
seqC = concatA

parC :: BComplex -> BComplex -> BComplex
parC = zipWithA (++) parBij

drawBComplex :: BComplex -> Dia
drawBComplex = centerX . drawBComplexR 0
  where
    drawBComplexR :: Int -> BComplex -> Dia
    drawBComplexR i (Single s) = i |> drawSet s
    drawBComplexR i (Cons ss bs c) =
        hcat
        [ i |> s1
        , strutX thisSep <> label
        , drawBComplexR (succ i) c
        ]
        # applyAll (map (drawABij i (map fst $ names s1)) bs)
      where
        s1 = drawSet ss
        thisSep = case bs of
          [] -> 0
          _  -> maximum . map (^. bijSep) $ bs
        label = (fromMaybe mempty . msum . reverse . map (^. bijLabel) $ bs)
                # (\d -> d # withEnvelope (strutY (height d) :: D R2))
                # (\d -> translateY (-(height s1 + thisSep - height d)/2) d)

drawABij :: Int -> [Name] -> ABij -> Dia -> Dia
drawABij i ns b = applyAll (map conn . catMaybes . map (_2 id . (id &&& (b ^. bijData))) $ ns)
  where
    conn :: (Name,Name) -> Dia -> Dia
    conn (n1,n2) = withNames [i |> n1, (i+1) |> n2] $ \[s1,s2] -> atop (drawLine s1 s2 # applyStyle (sty n1))
    sty = b ^. bijStyle
    drawLine sub1 sub2 = boundaryFrom sub1 v ~~ boundaryFrom sub2 (negateV v)
      where
        v = location sub2 .-. location sub1

toNameI :: Int -> Name
toNameI = toName

toNamesI :: [Int] -> [Name]
toNamesI = map toName

plus, minus, equals :: Dia
plus = hrule 1 <> vrule 1
minus = hrule 1
equals = hrule 1 === strutY 0.5 === hrule 1

mapAName :: (Typeable a, Typeable b, Ord b, Show b) => (a -> b) -> AName -> AName
mapAName f an@(AName x) = case cast x of
                            Nothing -> an
                            Just a  -> AName (f a)

mapName :: (Typeable a, Typeable b, Ord b, Show b) => (a -> b) -> Name -> Name
mapName f (Name ns) = Name (map (mapAName f) ns)

------------------------------------------------------------
-- Computing orbits/coloration

type Edge a = (a,a)

type Relator a = (a,[a],a)

mkRelator :: Edge a -> Relator a
mkRelator (n1,n2) = (n1,[],n2)

start :: Relator a -> a
start (n,_,_) = n

end :: Relator a -> a
end (_,_,n) = n

relatorToList :: Relator a -> [a]
relatorToList (a,bs,c) = a : bs ++ [c]

isTailOf :: Eq a => Relator a -> Relator a -> Bool
isTailOf r1 r2 = relatorToList r1 `isSuffixOf` relatorToList r2 && r1 /= r2

composeRelators :: Eq a => Relator a -> Relator a -> Maybe (Relator a)
composeRelators (s1,ns1,e1) (s2,ns2,e2)
  | e1 == s2  = Just (s1,ns1++[e1]++ns2,e2)
  | otherwise = Nothing

type Relation a = [Relator a]

mkRelation :: [Edge a] -> Relation a
mkRelation = map mkRelator

emptyR :: Relation a
emptyR = []

unionR :: Relation a -> Relation a -> Relation a
unionR = (++)

composeR :: Eq a => Relation a -> Relation a -> Relation a
composeR rs1 rs2 = [ rel | rel1 <- rs1, rel2 <- rs2, Just rel <- [composeRelators rel1 rel2] ]

orbits :: Eq a => Relation a -> Relation a -> Relation a
orbits r1 r2 = removeTails $ orbits' r2 r1 r1
  where
    orbits' _  _  [] = []
    orbits' r1 r2 r  = done `unionR` orbits' r2 r1 (r' `composeR` r1)
      where
        (done, r') = partition finished r
        finished rel = (start rel == end rel) || all ((/= end rel) . start) r1
    removeTails rs = filter (\r -> not (any (r `isTailOf`) rs)) rs

bijToRel :: Bij -> Relation Name
bijToRel = foldr unionR emptyR . map bijToRel1
  where
    bijToRel1 bij = mkRelation . catMaybes . map (_2 id . (id &&& (bij^.bijData))) $ bij^.bijDomain

orbitsToColorMap :: Ord a => [Colour Double] -> Relation a -> M.Map a (Colour Double)
orbitsToColorMap colors orbs = M.fromList (concat $ zipWith (\rel c -> map (,c) rel) (map relatorToList orbs) (cycle colors))

colorBij :: M.Map Name (Colour Double) -> Bij -> Bij
colorBij colors = map colorBij'
  where
    colorBij' bij = bij & bijStyle .~ \n -> maybe id lc (M.lookup n colors) ((bij ^. bijStyle) n)

------------------------------------------------------------
-- Example sets and bijections

a0, b0, a1, b1 :: ASet
a0 = nset 3 yellow
b0 = nset 3 blue

a1 = nset 2 green
b1 = nset 2 red

bc0, bc1, bc01 :: BComplex
bc0 = [a0] .- bij0 -.. [b0]
bc1 = [a1] .- bij1 -.. [b1]
bc01 = [a0,a1] .- bij01 -.. [b0,b1]

bij0, bij1 :: Bij
bij0 = [mkABij a0 b0 ((`mod` 3) . succ . succ)]
bij1 = [mkABij a1 b1 id]

names01, names02 :: [Name]
names01 = 'X' |> disjointly concat [head bij0^.bijDomain, head bij1^.bijDomain]
names02 = 'Y' |> (('a' |@@ [1,2]) ++ ('b' |@@ [0,1]) ++ ('a' |@@ [0]))

bij01 :: Bij
bij01 = []

