{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module GraphViz where

import           Diagrams.Backend.Cairo.CmdLine
import           Diagrams.Prelude

import           SpeciesDiagrams                   (mlocColor)

import           Data.Graph.Inductive.Graph        (Graph, Node, labEdges,
                                                    labNodes)
import           Data.Graph.Inductive.PatriciaTree
import           Data.GraphViz
import           Data.GraphViz.Attributes.Complete (Attribute (Pos), Point (..),
                                                    Pos (..))
import           Data.GraphViz.Commands.IO         (hGetDot)
import           Data.GraphViz.Types.Generalised   (FromGeneralisedDot (..))

graphToDia :: (Int -> Diagram B R2) -> (Int -> Int -> Diagram B R2 -> Diagram B R2) -> Gr (AttributeNode nl) (AttributeNode el) -> Diagram B R2
graphToDia dn de gr = drawNodes # drawEdges
  where
    nodes = labNodes gr
    edges = labEdges gr
    drawNodes = mconcat . map drawNode $ nodes
    drawEdges = applyAll . map drawEdge $ edges
    drawNode (n,(attrs,_)) =
      case [p | Pos (PointPos p) <- attrs] of
        [] -> mempty
        [pt] -> dn n # named n # moveTo (pointToP2 pt)
        -- it's actually using ellipses by default.  Need to set input shape.
        -- I will just draw edges myself, using diagrams.
    drawEdge (n1,n2,_) = de n1 n2
    --   case [ss | Pos (SplinePos ss) <- attrs] of
    --     [] -> mempty
    --     [splines] -> mconcat . map drawSpline $ splines
    -- drawSpline (Spline { startPoint = s, endPoint = e, splinePoints = pts}) =
    --   (pointToP2 (head pts') ~~ (pointToP2 (last pts'))) -- FIXME.
    --                                                      -- should be
    --                                                      -- cubic
    --                                                      -- B-spline.
    --   where
    --     pts' = maybeToList s ++ pts ++ maybeToList e

pointToP2 (Point {xCoord = x, yCoord = y}) = (x ^& y) # scale (1/20)

------------------------------------------------

graphToGraph' :: (Ord cl, Graph gr) => GraphvizParams Node nl el cl l
                 -> GraphvizCommand
                 -> gr nl el
                 -> IO (gr (AttributeNode nl) (AttributeEdge el))
graphToGraph' params com gr = dotAttributes' com (isDirected params) gr' dot
  where
    dot = graphToDot params' gr'
    params' = params { fmtEdge = setEdgeIDAttribute $ fmtEdge params }
    gr' = addEdgeIDs gr

dotAttributes' :: (Graph gr, PPDotRepr dg Node, FromGeneralisedDot dg Node)
                  => GraphvizCommand -> Bool -> gr nl (EdgeID el)
                  -> dg Node -> IO (gr (AttributeNode nl) (AttributeEdge el))
dotAttributes' command isDir gr dot
  = augmentGraph gr . parseDG <$> graphvizWithHandle command dot DotOutput hGetDot
  where
    parseDG = (`asTypeOf` dot) . fromGeneralised
