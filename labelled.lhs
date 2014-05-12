%% -*- mode: LaTeX; compile-command: "mk" -*-

%include thesis.fmt

\chapter{Labelled structures}
\label{chap:labelled}

Now that we have a foundation for describing labelled shapes, the next
step is to extend them into full-blown \emph{data structures} with
mappings from labels to data.  For example, \pref{fig:shape-data}
illustrates an example of a labelled shape together with a mapping
from the labels to data values.
\begin{figure}
\centering
\begin{diagram}[width=400]
import SpeciesDiagrams
dia = shapePlusData # centerXY # pad 1.1

shapePlusData = hcat
  [ octo' elt "species!"
  , strutX 2
  , text "=" # fontSize 3 <> phantom (square 1 :: D R2)
  , strutX 2
  , octo [0..7]
  , strutX 2
  , text "×" # fontSize 3 <> phantom (square 1 :: D R2)
  , strutX 2
  , mapping
  , strutX 2
  ]

mapping = centerXY . vcat' (with & sep .~ 0.2) . map mapsto $ zip [0..7] "species!"
mapsto (l,x) = hcat' (with & sep .~ 0.5) [mloc l, a, elt x]
  where
    a = (arrow' (with & headSize .~ 1) 2 <> hrule 2) |||||| strutX 0.4
\end{diagram}
%$
\caption{Data structure = shape + data} \label{fig:shape-data}
\end{figure}
However, this must be done in a principled way.  The idea is to derive
\todo{operations\dots from structure \dots}

% One useful intuition is to think of the labels as \emph{memory
%   addresses}, which point off to some location where a data value is
% stored. This intuition has some particularly interesting consequences
% when it comes to operations like Cartesian product and functor
% composition---explained in~\pref{sec:operations}---since it gives us a
% way to model sharing (albeit in limited ways).


\begin{itemize}
\item Joyal's analytic functors.  Labelled structures.
\item Operations on labelled structures.
\item Sharing.
\end{itemize}

\section{Kan extensions}
\label{sec:kan-extensions}

The definition of analytic functors makes central use of the notion of
a (left) \term{Kan extension}.

\todo{Some of this should perhaps go in the preliminaries chapter}

\begin{defn} \label{defn:lan}
  Given functors $F : \C \to \D$ and $J : \C \to \E$, the \term{left
    Kan extension of $F$ along $J$}, written $\lan J F$ (following
  \citet{art-and-dan}), is a functor $\D \to \E$ characterized by the
  isomorphism \[ (\lan{J}{F} \to G) \cong (F \to G \comp J), \]
  natural in $G$. \todo{check this} If this exists for all $F$, then
  we may say even more succinctly that the left Kan extension functor
  $\lan J -$ is left adjoint to $- \comp J$, that is, \[ \lan J - \adj
  - \comp J. \]
\end{defn}

Intuitively, if $J : \C \to \E$ is thought of as an ``embedding'' of
$\C$ into $\E$, then $\lan J F$ can be thought of as a way of
``extending'' the domain of $F$ from $\C$ to $\E$ in a way compatible
with $J$. \[ \xymatrix{\C \ar[r]^{F} \ar[d]_J & \D \\ \E \ar[ur]_{\lan
    J F}} \] If we substitute $\lan J F$ for $G$ in the isomorphism of
\pref{defn:lan} and take the image of $\id_{\lan J F}$, we obtain
$\eta : F \to \lan J F \comp J$


\todo{simple example(s)?}

\section{Analytic functors and labelled structures}
\label{sec:analytic}

As our starting place, consider Joyal's definition of \term{analytic
  functors}~\cite{Joyal-analytic-functors}.
\begin{defn}
  Given a species $F \in [\B,\Set]$, the \term{analytic functor} $\hat
  F$ corresponding to $F$ is given by the left Kan extension of $F$
  along the inclusion functor $\iota : \B \inj \Set$.  This can also
  be expressed as a coend: \[ \hat F\ A = \coend{L} F\ L \times (\iota
  L \to A). \] A functor $\Set \to \Set$ is \term{analytic} when it
  arises in this way from some species.
\end{defn}
We can think of $\hat F$ as the polymorphic ``data type'' arising from
the species $F$. Given a set $A$, a value in $\hat F\ A$ consists of
an $L$-labelled $F$-shape together with a function (\ie a morphism in
$\Set$) from $\iota L$ to $A$.  The coend means that the choice of a
particular label set $L$ does not matter: any two values $f : F\ L
\times (\iota L \to A)$ and $g : F\ L' \times (\iota L' \to A)$ are
considered equal if there is some bijection $\sigma : L \bij L'$ which
sends $f$ to $g$.

Analytic functors have many nice properties: for example, they are
closed under \todo{?}, and have corresponding \term{generating
  functions} (indeed, part of the motivation of Joyal's work seems to
have been to categorify the theory of generating functions).

However, the above definition of analytic functors is specific to
$[\B,\Set]$.  It must first be modified to apply to the generalized
species from the previous chapter.

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

\section{Recursion and the implicit species theorem}
\label{sec:recursion}

\todo{Write me}

\section{Other stuff}

\todo{Examples. Bounded tree width.  Generic programming.}

\todo{Apply combinatorics?  e.g. generating trees.  Random generation,
  Boltzmann sampling...}

\todo{Stick in a bit of the generating functions story?  Just enough
  to show where it's going?  With some applications to enumeration or
  counting etc.  Maybe put it in a future work section---can be very
  concrete.}
