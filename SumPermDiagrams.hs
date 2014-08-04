{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SumPermDiagrams where

import           Diagrams.Prelude

import           Control.Lens                 (partsOf, traverse)
import           Data.Bits
import           Data.List                    (find)
import           Data.Maybe                   (fromJust)
import           Data.Typeable
import           Data.Universe.Instances.Base

newtype Index = Index Int
  deriving (Eq, Ord, Show, Read, Real, Num, Integral, Bits, Enum, Typeable)

instance IsName Index

instance Universe Index where
  universe = map Index [0..]

column cs
  = vcat' (with & sep .~ 1)
  . zipWith (|>) ['a' ..]
  . map vcat
  . (partsOf (traverse.traverse) %~ zipWith fc cs)
  . map (\n -> zipWith named [0 :: Index ..] (replicate n (square 1)))

permL :: (Index -> Index) -> [a] -> [a]
permL s l = [ l !! (fromEnum (inverse s i)) | i <- [0 .. toEnum (length l) - 1] ]

either2Name :: Either Index Index -> Name
either2Name (Left i) = 'a' .> i
either2Name (Right i) = 'b' .> i

inverse :: (Universe a, Eq b) => (a -> b) -> (b -> a)
inverse f b = fromJust (find ((==b) . f) universe)

