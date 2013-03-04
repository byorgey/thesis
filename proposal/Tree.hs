{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

import           Diagrams.TwoD.Layout.Tree
import           Math.Combinatorics.Species

import           NumericPrelude

data Tree a = E | B (Tree a) a (Tree a)

deriveDefaultSpecies ''Tree
