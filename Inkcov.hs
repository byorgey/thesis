-- First, generate inkcov.txt using
--
--   gs -o - -sDEVICE=inkcov Yorgey-thesis-final-2014-11-14.pdf > inkcov.txt
--
-- which I got here:
--
--   http://tex.stackexchange.com/a/61216
--
-- This script then processes the generated data into a more useful format.
--
-- To split out just the pages with color or with B&W, take one of the
-- generated lists of page numbers, e.g. save it in a file
-- colorpages.txt, and then do something like
--
--   pdftk thesis.pdf cat `cat colorpages.txt` output thesis-COLOR.pdf

import           Data.List
import           Data.List.Split

data Ink = Color | Gray
  deriving (Show)

data Page = Page { pageNum :: Int, pageColor :: Ink }

printPage :: Page -> String
printPage (Page n ink) = show n ++ ": " ++ show ink

isColor (Page _ Color) = True
isColor _ = False

main :: IO ()
main = do
  inkcov <- readFile "inkcov.txt"
  let pages = map (head . tail) . chunksOf 2 . drop 4 . lines $ inkcov
      pages' = zipWith processPage [1..] pages
  putStr . unlines . map printPage $ pages'
  let (colors, grays) = partition isColor pages'
  putStrLn "Gray pages:"
  putStrLn . unwords . map (show . pageNum) $ grays
  putStrLn "Color pages:"
  putStrLn . unwords . map (show . pageNum) $ colors

processPage :: Int -> String -> Page
processPage n dat
  | " 0.00000  0.00000  0.00000" `isPrefixOf` dat = Page n Gray
  | otherwise = Page n Color
