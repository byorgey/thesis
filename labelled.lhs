%% -*- mode: LaTeX; compile-command: "mk" -*-

%include thesis.fmt

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

\todo{Edit. Dumped here from description of product from paper.}

%%% XXX remove me
\newcommand{\under}[1]{\floor{#1}}
\newcommand{\lift}[1]{\ceil{#1}}
\newcommand{\lab}[1]{\langle #1 \rangle}
\newcommand{\LStr}[3]{#1 #2 #3}

One introduces a labelled $(F \sprod G)$-shape by pairing a labelled
$F$-shape and a labelled $G$-shape, using a label set isomorphic to
the coproduct of the two label types:
\begin{align*}
  - \sprod_- - &: (\under{L_1} + \under{L_2} \iso \under{L}) \to F\ L_1
  \to G\ L_2 \to (F \sprod G)\ L \\
  - \lab{\sprod}_- - &: (\under{L_1} + \under{L_2} \iso \under{L}) \to \LStr F {L_1} A \to \LStr G {L_2} A \to
  \LStr {F \sprod G} L A
\end{align*}
We use here (and for the rest of the paper) the notational convention that
the isomorphism arguments are given first, but are written as subscripts
in mathematical notation.



%% XXX remove me
\newcommand{\List}{\cons{List}}
\newcommand{\inl}{\cons{inl}}
\newcommand{\inr}{\cons{inr}}
\newcommand{\StoreNP}{\mapsto}

\todo{Edit. Dumped here from paper.}

As an example, we may now encode the standard algebraic data type of
lists, represented by the inductively-defined species satisfying
$\List \iso \One + (\X \sprod \List)$ (for convenience, in what
follows we leave implicit the constructor witnessing this
equivalence).  We can then define the usual constructors $\cons{nil}$
and $\cons{cons}$ as follows:
\begin{align*}
  &\cons{nil} : \LStr{\List}{\Fin 0} A \\
  &\cons{nil} \defeq \lab{\inl} \lab{\One} \\
  &\cons{cons} : A \to \LStr \List L A \to (\Fin 1 + \under L \iso
  \under{L'}) \to \LStr \List {L'} A \\
  &\cons{cons}\ a\ (|shape|,|elts|)\ e \defeq (\inr\ (\cons{x} \sprod_e
  |shape|), |append|\ e\ (|allocate|\ (\lambda x. a))\ |elts|)
\end{align*}
The interesting thing to note here is the extra equivalence passed as
an argument to $\cons{cons}$, specifying the precise way in which the
old label type augmented with an extra distinguished label is
isomorphic to the new label type.  Again, one might intuitively expect
something like \[ \cons{cons} : A \to \LStr \List L A \to \LStr \List
{\lift{\Fin 1} + L} A, \] but this is nonsensical: we cannot take the
coproduct of two elements of $\FinType$, as it is underspecified.  For
implementations of $\StoreNP - -$ which make use of the equivalence to
$\Fin n$ stored in $\FinType$ values (we give an example of one such
implementation in \pref{sec:vecmap}), the extra equivalence given as
an argument to \cons{cons} allows us to influence the particular way
in which the list elements are stored in memory.  For lists, this is
not very interesting, and we would typically use a variant $\cons{cons'}
: A \to \LStr \List L A \to \LStr \List {\cons{inc}(L)} A$ making use of a
canonical construction $\cons{inc}(-) : \FinType \to \FinType$ with
$\Fin 1 + \under L \iso \under{\cons{inc}(L)}$.

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
  # centerXY # sized (Width 4) # pad 1.1
  \end{diagram}%$
  \caption{Superimposing a tree and a list on shared data}
  \label{fig:tree-list-cp}
\end{figure}
