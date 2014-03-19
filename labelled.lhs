%% -*- mode: LaTeX; compile-command: "mk" -*-

\chapter{Labelled structures}
\label{chap:labelled}

\begin{itemize}
\item Joyal's analytic functors.  Labelled structures.
\item Operations on labelled structures.
\item Sharing.
\end{itemize}

\section{Analytic functors and labelled structures}
\label{sec:analytic}

\section{Operations on labelled structures}
\label{sec:labelled-operations}


\section{Sharing}
\label{sec:sharing}

That is, multiple parts of the same shape can all ``point to'' the
same data.  In pure functional languages such as Haskell or Agda,
sharing is a (mostly) unobservable operational detail; with a labelled
structure we can directly model and observe
it. \pref{fig:tree-list-cp} illustrates the Cartesian product of a
binary tree and a list.
\begin{figure}
  \centering
  \begin{diagram}[width=200]
import           Data.List.Split
import           Diagrams.TwoD.Layout.Tree
import           Diagrams.TwoD.Path.Metafont

import           SpeciesDiagrams

leaf1 = circle 1 # fc white # named "l1"
leaf2 = circle 1 # fc white # named "l2"

tree = maybe mempty (renderTree (const leaf1) (~~))
     . symmLayoutBin' (with & slVSep .~ 4 & slHSep .~ 6)
     $ (BNode () (BNode () (BNode () Empty (BNode () Empty Empty)) Empty) (BNode () (BNode () Empty Empty) (BNode () Empty Empty)))

listL shp l = hcat . replicate 7 $ (shp # fc white # named l)

connectAll l1 l2 perm =
  withNameAll l1 $ \l1s ->
  withNameAll l2 $ \l2s ->
  applyAll (zipWith conn l1s (perm l2s))

conn l1 l2 = beneath (lc grey . metafont $ location l1 .- leaving unit_Y <> arriving unit_Y -. endpt (location l2))

dia = vcat' (with & sep .~ 5)
  [ hcat' (with & sep .~ 5)
    [ tree # centerY
    , listL (circle 1) "l2" # centerY
    ] # centerXY
  , listL (square 2) "s" # centerXY
  ]
  # connectAll "l1" "s" id
  # connectAll "l2" "s" (concat . map reverse . chunksOf 2)
  # centerXY # sized (Width 4) pad 1.1
  \end{diagram}%$
  \caption{Superimposing a tree and a list on shared data}
  \label{fig:tree-list-cp}
\end{figure}
