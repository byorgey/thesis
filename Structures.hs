{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TemplateHaskell           #-}

module Structures where

import           Diagrams.Backend.Cairo
import           Diagrams.Prelude
import           Diagrams.TwoD.Layout.Tree
import           Graphics.SVGFonts

import           Control.Applicative       ((<|>))
import           Control.Arrow             (second)
import           Control.Lens              (makeLenses, (^.))
import           Data.Default.Class
import           Data.List                 (genericLength, mapAccumL, nub)
import qualified Data.Map                  as M
import           Data.Tree
import           Physics.ForceLayout
import           Text.Parsec               (between, char, many, runParser)
import           Text.Parsec.String        (Parser)

type DC = Diagram Cairo R2

nil :: DC
nil = square 1 # fc black

dot :: DC
dot = circle 0.8 # fc (blend 0.5 white lightblue)

list :: Int -> DC
list 0 = square 1 # fc black
list n = dots <> rule
  where
    dots = hcat' (with & sep .~ 2) (replicate n dot)
    rule = hrule (width dots) # translateXTo dots

translateXTo ref mv = alignL mv # maybe id translateX (fst <$> extentX ref)

tree :: Tree () -> DC
tree =
  renderTree (const dot) (~~) . symmLayout' (with & slHSep .~ 4 & slVSep .~ 4)

treeParser :: Parser (Tree ())
treeParser = Node () <$> between (char '(') (char ')') (many treeParser)

bTreeParser :: Parser (BTree ())
bTreeParser = char '(' *>
  (     BNode () <$> bTreeParser <*> bTreeParser
    <|> pure Empty
  )
  <* char ')'

parseTree :: String -> Tree ()
parseTree s = case runParser treeParser () "" s of
                Left _ -> error "parse error"
                Right t -> t

parseBTree :: String -> BTree ()
parseBTree s = case runParser bTreeParser () "" s of
                 Left _ -> error "parse error"
                 Right t -> t

graph :: [(Int,Int)] -> DC
graph es = drawEnsemble es $
           forceLayout (with & damping     .~ 0.8
                             & energyLimit .~ Just 0.001
                             & stepLimit   .~ Nothing
                       )
           ens

  where
    ens :: Ensemble R2
    ens = Ensemble [ (es,  hookeForce 0.05 4)
                   , (allPairs, coulombForce 1)
                   ]
                   particleMap
    vs = nub (map fst es ++ map snd es)
    allPairs = [(x,y) | x <- vs, y <- vs, x < y ]
    particleMap :: M.Map Int (Particle R2)
    particleMap = M.fromList $ zip vs (map initParticle (regPoly (length vs) 4))

drawEnsemble :: [(Int,Int)] -> Ensemble R2 -> DC
drawEnsemble es = applyAll (map drawEdge es) . mconcat . map drawPt . (map . second) (^.pos) . M.assocs . (^.particles)
  where
    drawPt (pid, p) = dot # named pid # moveTo p
    drawEdge (v1,v2) = withNames [v1,v2] $ \[s1,s2] -> beneath (location s1 ~~ location s2)

cyc :: Int -> DC
cyc 0 = mempty
cyc 1 = dot
cyc n
  = mconcat
    [ position (zip (polygon (with & polyType .~ PolyRegular n r)) (repeat dot))
    , circle r
    ]
  where
    r = 4* fromIntegral n / tau

decorateLeaves :: BTree a -> Tree (Maybe a)
decorateLeaves Empty = Node Nothing []
decorateLeaves (BNode a l r) = Node (Just a) [decorateLeaves l, decorateLeaves r]

binTreeN :: BTree () -> DC
binTreeN Empty = square 1 # fc black
binTreeN t
  = renderTree (maybe nil (const dot)) (~~)
  . symmLayout' (with & slHSep .~ 5 & slVSep .~ 4)
  . decorateLeaves
  $ t

binTree :: BTree () -> DC
binTree Empty = mempty
binTree t
  = renderTree' (maybe mempty (const dot)) (drawEdge)
  . symmLayout' (with & slHSep .~ 5 & slVSep .~ 4)
  . decorateLeaves
  $ t
  where
    drawEdge _ (Nothing,_) = mempty
    drawEdge (_,p) (_,q) = p ~~ q

pair :: DC -> DC -> DC
pair d1 d2 =
  hcat
  [ d1 # centerXY <> halfBox (w1 + padding) (h + padding)
  , d2 # centerXY <> halfBox (w2 + padding) (h + padding) # reflectX
  ]
  where
    w1 = width d1
    w2 = width d2
    h  = max (height d1) (height d2)
    padding = maximum [w1 * padFactor, w2 * padFactor, h * padFactor]
    padFactor = 0.2
    halfBox w h = roundedRect' w h (with & radiusTL .~ min w h / 8 & radiusBL .~ min w h / 8)

allBinTrees :: [[BTree ()]]
allBinTrees = map binTreesK [0..]
  where
    binTreesK 0 = [Empty]
    binTreesK n = [ BNode () t1 t2 | k <- [(n-1), (n-2) .. 0], t1 <- binTreesK k, t2 <- binTreesK (n - 1 - k)]

allTrees :: [[Tree ()]]
allTrees = map treesK [0..]
  where
    treesK 0 = []
    treesK n = [ Node () ts
               | part <- oPartitions (n-1)
               , ts <- mapM treesK part
               ]

oPartitions 0 = [[]]
oPartitions n | n < 0 = []
oPartitions n = concat [ map (k:) (oPartitions (n-k)) | k <- [n, n-1 .. 1] ]

------------------------------------------------------------
-- Bucketing
------------------------------------------------------------

-- XXX make bucket lines thicker

data BucketOpts
  = BucketOpts
  { _numBuckets    :: Int
  , _showEllipses  :: Bool
  , _showIndices   :: Bool
  , _bucketSize    :: Double
  , _expandBuckets :: Bool
  }

$(makeLenses ''BucketOpts)

instance Default BucketOpts where
  def = BucketOpts
    { _numBuckets        = 6
    , _showEllipses      = True
    , _showIndices       = True
    , _bucketSize        = 10
    , _expandBuckets     = False
    }

bucketed' :: BucketOpts -> [[DC]] -> DC
bucketed' opts buckets
  = (if opts ^. showEllipses then (||| ellipses) else id)
  . hcat' (with & sep .~ 1)
  . take (opts ^. numBuckets)
  . zipWith (makeBucket opts) [0..]
  $ buckets
  where
    ellipses = strutX 1 ||| hcat' (with & sep .~ 1) (replicate 3 (circle 0.5 # fc black))

makeBucket :: BucketOpts -> Int -> [DC] -> DC
makeBucket opts n elts
    = (if (opts ^. showIndices) then (=== (strutY 1 === text' 5 (show n))) else id)
      (bucketDia <> wrapLayout s s elts)
  where
    bucketDia :: DC
    bucketDia = roundedRect s s (s / 8)
    s = opts ^. bucketSize

wrapLayout :: Double -> Double -> [DC] -> DC
wrapLayout w h = layoutGrid w h . wrap w h

wrap :: Double -> Double -> [DC] -> [[DC]]
wrap w h [] = []
wrap w h es = map snd this : wrap w h (map snd rest)
  where
    (this, rest) = span ((<w) . fst) esWeighted
    esWeighted :: [(Double, DC)]
    esWeighted = snd $ mapAccumL (\w e -> let w' = w + width e in (w', (w', e))) 0 es

layoutGrid :: Double -> Double -> [[DC]] -> DC
layoutGrid w h es = centerY . spread unit_Y h $ map (centerX . spread unitX w) es
  where
    spread :: R2 -> Double -> [DC] -> DC
    spread v total es = cat' v (with & sep .~ (total - sum (map (extent v) es)) / (genericLength es + 1)) es
    extent v d
      = maybe 0 (negate . uncurry (-))
      $ (\f -> (-f (negateV v), f v)) <$> (appEnvelope . getEnvelope $ d)

bucketed :: [[DC]] -> DC
bucketed = bucketed' def

------------------------------------------------------------

listBuckets opts = bucketed' opts (map (:[]) . zipWith scale ([1,1,1,0.6] ++ repeat 0.4) . map list $ [0..])

binTreeBuckets opts
  = bucketed' opts
      ( map (map (pad 1.3 . centerXY . binTree)) allBinTrees
      # zipWith scale [1,1,0.5, 0.2, 0.2, 0.08]
      )

------------------------------------------------------------

theTree = tree (parseTree "((())()((()()())()(()())))") # centerXY

theGraph = graph [(0,1), (0,2), (1,3), (2,3), (2,4), (2,5), (3,5), (3,6), (6,7), (6,8)] # centerXY

theList = list 5 # centerXY

theCycles = hcat' (with & sep .~ 2) [cyc 5, cyc 7] # centerXY # rotateBy (1/20)

------------------------------------------------------------
-- misc

text' d t = stroke (textSVG' $ TextOpts t lin INSIDE_H KERN False d d ) # fc black # lw none
