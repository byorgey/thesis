{-# LANGUAGE NoMonomorphismRestriction #-}

import           Diagrams.Backend.Cairo.CmdLine
import           Diagrams.Prelude

import           Data.List                      (zip4)
import           SpeciesDiagrams

dot = circle 0.8 # fc black

enc = fc white . enclose 1 1

newCyc :: Double -> [Diagram B R2] -> Diagram B R2
newCyc r ds = position (zip posns (zipWith named [0 :: Int ..] ds)) # markBorders
  where
    n = length ds
    triples = zip4 ([1 :: Int .. n-1] ++ [0])
                posns (tail (cycle posns)) ((tail . tail) (cycle posns))
    markBorders = withNames [0 :: Int .. n-1] $ \ss ->
      applyAll (map (mark2Borders ss) triples)
    mark2Borders ss (i,prev,cur,next) = id
      -- where
      --   pb = binarySearch
    posns :: [P2]
    posns
      | n == 1 = [0 ^& r]
      | otherwise = polygon (with & polyType .~ PolyRegular (length ds) r
                                  & polyOrient .~ NoOrient
                            )
                    # rotateBy (1/4)

cls = map (newCyc 2.5) ((map . map) (enc . drawList' (const dot) . flip replicate ()) [[1,1,1],[2,1],[3]])

lcs = map (drawList' id) ((map . map) (enc . newCyc 2 . flip replicate dot) [[1,1,1],[2,1],[1,2],[3]])

dia =
  vcat' (with & sep .~ 2)
  [ hcat' (with & sep .~ 3) cls
  , hcat' (with & sep .~ 3) lcs
  ]
  # frame 0.5
  # lwO 0.7

main :: IO ()
main = defaultMain dia
