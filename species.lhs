%% -*- mode: LaTeX; compile-command: "mk" -*-

%include thesis.fmt

\chapter{Combinatorial species}
\label{chap:species}

The theory of \term{combinatorial species}, introduced by
\citet{joyal}, is a unified, algebraic theory of \term{combinatorial
  structures} or \term{shapes}.  The algebraic nature of species is of
particular interest in the context of data structures and will be
explored in depth in this chapter.  The theory can also be seen as a
\term{categorification} of the theory of \term{generating functions}.

The present chapter begins in \pref{sec:species-intuition} by
presenting an intuitive sense for species along with a collection of
examples.  \pref{sec:species-definition} presents Joyal's formal
definition of species and related definitions in set theory, along
with more commentary and intuition.  The same section also discusses
an encoding of species within homotopy type theory
(\pref{sec:species-hott}), and the benefits of such an encoding. As a
close follow-up to the formal definition, \pref{sec:iso-equipotence}
presents two equivalence relations on species, \term{isomorphism} and
\term{equipotence}, and in particular sheds some new light on
equipotence via the encoding of species in
HoTT. Finally, \pref{sec:generating-functions} introduces \term{generating
  functions}, which are in some sense the point of origin for the
entire theory.

\section{Intuition and examples}
\label{sec:species-intuition}

In the process of generalizing the theory of generating functions, one
of Joyal's great insights in formulating the theory of species was to
take the notion of \emph{labelled} structures as fundamental, and to
build other notions (such as \emph{unlabelled} structures) on top of
it.  Species fundamentally describe labelled objects; for example,
\pref{fig:example-labelled} shows two representative examples, a
labelled tree and a labelled ``octopus''.  In these examples the
integers $\{0, \dots, 7\}$ are used as labels, but in general, labels
can be drawn from any set.

\begin{figure}
\centering
\begin{diagram}[width=250]
import SpeciesDiagrams
dia = hcat [tree # centerXY, strutX 4, octo [0..7]]
    # centerXY
    # frame 0.5
    # lwO 0.7
\end{diagram}
\caption{Representative labelled shapes} \label{fig:example-labelled}
\end{figure}

Why \emph{labelled} shapes?  In the tree shown
in~\pref{fig:example-labelled}, one can uniquely identify each
location in the tree by a path from the root, without referencing
labels at all.  However, the ``octopus'' illustrates one reason labels
are needed. The particular way it is drawn is intended to indicate
that the structure has fourfold rotational symmetry, which means there
would be no way to uniquely refer to any location except by label.
More abstractly, \term{unlabelled} shapes can be defined as
equivalence classes of labelled shapes (\pref{sec:unlabelled}), which
is nontrivial in the case of shapes with symmetry.

Besides its focus on labels, the power of the theory of species also
derives from its ability to describe structures of interest
\emph{algebraically}, making them amenable to analysis with only a
small set of general tools.

\begin{ex}
  Consider the species $\List$ of \term{lists}, or \term{linear
    orderings}; \pref{fig:lists} illustrates all the labelled list
  structures (containing each label exactly once) on the set of labels
  $[3] = \{0,1,2\}$.  Of course, there are exactly $n!$ such list
  structures on any set of $n$ labels.

  \begin{figure}
    \centering
    \begin{diagram}[width=400]
import SpeciesDiagrams
import Data.List
import Data.List.Split

dia =
  hcat' (with & sep .~ 0.5)
  [ unord (map labT [0..2])
  , mkArrow 2 (txt "L")
  , listStructures
  ]
  # centerXY
  # pad 1.1
  # lwO 0.7

listStructures
  = centerXY
  . hcat' (with & sep .~ 0.7)
  . map (vcat' (with & sep .~ 0.5))
  . chunksOf 2
  . map (drawList' labT)
  . permutations
  $ [0..2]
    \end{diagram}
    \caption{The species $\List$ of lists}
    \label{fig:lists}
    %$
  \end{figure}
  The species of lists can be described by the recursive algebraic
  expression \[ \List = \One + \X \cdot \List. \] The meaning of this
  will be made precise later. For now, its intuitive meaning should be
  clear to anyone familiar with recursive algebraic data types in a
  language such as Haskell or OCaml: a labelled list ($\List$) is
  empty ($\One$) or ($+$) a single label ($\X$) together with
  ($\cdot$) another labelled list ($\List$).
\end{ex}

\begin{ex}
As another example, consider the species $\Bin$ of \emph{(rooted,
  ordered) binary trees}.  The set of all labelled binary trees on
$\{0,1,2\}$ is shown in \pref{fig:binary-trees}.

  \begin{figure}
    \centering
    \begin{diagram}[width=400]
import SpeciesDiagrams
import Data.Tree
import Diagrams.TwoD.Layout.Tree
import Control.Arrow (first, second)
import Data.List.Split (chunksOf)
import Data.Maybe (fromJust)

dia =
  hcat' (with & sep .~ 0.5)
  [ unord (map labT [0..2])
  , mkArrow 2 (txt "B")
  , treeStructures # scale 0.5
  ]
  # centerXY
  # pad 1.1
  # lwO 0.7

nil = square 0.2 # fc black

treeStructures
  = centerXY
  . vcat' (with & sep .~ 0.5)
  . map (centerX . hcat' (with & sep .~ 0.5))
  . chunksOf 10
  . map (drawBinTreeWide . fmap labT)
  . enumTrees
  $ [0..2]
    \end{diagram}
    \caption{The species $\Bin$ of binary trees}
    \label{fig:binary-trees}
    %$
  \end{figure}
  Algebraically, such trees can be described by \[ \Bin = \One + \Bin
  \cdot \X \cdot \Bin. \]
\end{ex}

\begin{ex}
  The species $\Bag$ of \term{sets} describes shapes consisting simply of an
  unordered collection of unique labels, with no other structure
  imposed.  There is exactly one such shape for any set of labels, as
  illustrated in \pref{fig:sets}.

  \begin{figure}
    \centering
    \begin{diagram}[width=200]
import SpeciesDiagrams

dia =
  hcat' (with & sep .~ 0.5)
  [ unord (map labT [0..3])
  , mkArrow 2 (txt "E")
  , unord (map labT [0..3])
  ]
  # centerXY
  # pad 1.1
  # lwO 0.7
    \end{diagram}
    \caption{The species $\Bag$ of sets}
    \label{fig:sets}
    %$
  \end{figure}
\end{ex}

\begin{ex}
  The species $\msf{Mob}$ of \emph{mobiles} consists of non-empty
  binary trees where each node has exactly zero or two subtrees, and
  sibling subtrees are considered unordered.
  \pref{fig:mobiles} shows a single example $\msf{Mob}$-shape, drawn
  in four (equivalent) ways.
  \begin{figure}
    \centering
    \begin{diagram}[width=200]
import           Data.List.Split                (chunksOf)
import           Data.Maybe                     (fromJust)
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

dia = mobiles
    # centerXY
    # frame 0.5
    # lwO 0.7

enumMobiles :: [a] -> [BTree a]
enumMobiles []  = []
enumMobiles [x] = [BNode x Empty Empty]
enumMobiles xxs
  = [ BNode x l r
    || (x, (x':xs))  <- select xxs
    ,  (ys,zs) <- subsets xs
    ,  l <- enumMobiles (x':ys)
    ,  r <- enumMobiles zs
    ]

mobileRotations :: BTree a -> [BTree a]
mobileRotations Empty = [Empty]
mobileRotations t@@(BNode _ Empty Empty) = [t]
mobileRotations (BNode x l r) = concat
  [ [BNode x l' r', BNode x r' l'] || l' <- mobileRotations l, r' <- mobileRotations r ]

drawMobile
  = renderTree id corner . fromJust
  . symmLayoutBin' (with & slHSep .~ 1.5)
  where
    corner p q = strokeLocTrail (fromOffsets [project unitY v, project unitX v] `at` p)
      where
        v = q .-. p

mobiles
  = centerXY
  . vcat' (with & sep .~ 1)
  . map (centerX . hcat' (with & sep .~ 1))
  . chunksOf 2
  . map (drawMobile . fmap labT)
  . mobileRotations
  . (!!15)
  . enumMobiles
  $ [0..4]  -- $
    \end{diagram}
    \caption{An example $\msf{Mob}$-shape, drawn in four equivalent ways}
    \label{fig:mobiles}
  \end{figure}
  Algebraically, \[ \msf{Mob} = \X + \X \cdot (\Bag_2 \comp
  \msf{Mob}), \] that is, a mobile is either a single label, or a
  label together with an unordered pair ($\Bag_2$) of ($\comp$)
  mobiles.
\end{ex}

\begin{ex}
  The species \Cyc of \term{cycles}, illustrated in \pref{fig:cycles},
  describes shapes that consist of an ordered cycle of labels.  One
  way to think of the species of cycles is as a quotient of the
  species of lists, where two lists are considered equivalent if one
  is a cyclic rotation of the other (see \pref{sec:molecular-atomic}).
  \begin{figure}
    \centering
    \begin{diagram}[width=400]
import SpeciesDiagrams
import Data.List
import Data.List.Split

dia =
  hcat' (with & sep .~ 0.5)
  [ unord (map labT [0..3])
  , mkArrow 2 (txt "C")
  , cycleStructures
  ]
  # centerXY
  # pad 1.1
  # lwO 0.7

cycleStructures
  = centerXY
  . hcat' (with & sep .~ 0.7)
  . map (vcat' (with & sep .~ 0.5))
  . chunksOf 2
  . map ((\l -> cyc' l 0.8) . map labT)
  . cycles
  $ [0..3]
    \end{diagram}
    \caption{The species $\Cyc$ of cycles}
    \label{fig:cycles}
    %$
  \end{figure}
\end{ex}

\begin{ex}
  The species \Perm of \term{permutations}---\ie bijective
  endofunctions---is illustrated in \pref{fig:permutations}.
  \begin{figure}
    \centering
    \begin{diagram}[width=400]
import           Data.List
import           Data.List.Split
import           SpeciesDiagrams

dia =
  hcat' (with & sep .~ 0.5)
  [ unord (map labT [0..3])
  , mkArrow 2 (txt "S")
  , permStructures
  ]
  # centerXY
  # pad 1.1
  # lwO 0.7

permStructures
  = centerXY
  . hcat' (with & sep .~ 1)
  . map (vcat' (with & sep .~ 0.5))
  . chunksOf 6
  . map drawPerm
  . perms
  $ [0..3]
    \end{diagram}
    \caption{The species $\Perm$ of permutations}
    \label{fig:permutations}
    %$
  \end{figure}
  Algebraically, it can be described by \[ \Perm = \Bag \comp
  \Cyc, \] that is, a permutation is a set of cycles.
\end{ex}

\begin{ex}
  The species $\Sp{End}$ of \term{endofunctions} consists of directed
  graphs corresponding to valid endofunctions on the labels---that is,
  where every label has exactly one outgoing edge
  (\pref{fig:example-End}).

  \begin{figure}
    \centering
    \begin{diagram}[width=300]
import           SpeciesDiagrams                   (colors)

import           Data.Graph.Inductive.Graph        (mkGraph)
import           Data.Graph.Inductive.PatriciaTree
import           Data.GraphViz
import           Data.List                         (findIndex)
import           Data.Maybe                        (fromJust)
import           System.IO.Unsafe

import           GraphViz

numNodes = 17

endo :: Int -> Int
endo n = fromJust (lookup n [(0,3),(1,3),(2,3),(3,7),(4,6),(5,6),(6,7),(7,8),(9,7),(8,10),(10,9),(11,10),(12,13),(13,13),(14,10),(15,9),(16,10)])

data EndoStatus = InTree [Int] || InLoop [Int]
  deriving Show

endoStatus :: Int -> (Int -> Int) -> EndoStatus
endoStatus x f = endoStatus' [x] (f x)
  where
    endoStatus' (i:seen) y
      || y == i = InLoop (i:seen)
      || y `elem` seen = InTree (i : takeWhile (/= y) seen ++ [y])
      || otherwise = endoStatus' (i : seen ++ [y]) (f y)

gr :: Gr () ()
gr = mkGraph [(n,()) || n <- [0..numNodes-1]] [(n,endo n,()) || n <- [0..numNodes-1]]

colorFor n = colors !! (fromJust $ findIndex (==n) [8,7,9,10,13])  -- $

dn n = circle 0.8 # fc c
  where
    c = case endoStatus n endo of
          InLoop _ -> colorFor n
          InTree pth -> colorFor (last pth)

loopStyle = lw veryThick . dashingG [0.2,0.2] 0

de n1 n2
  || n1 == n2  = connectPerim' (with & arrowShaft .~ arc (3/8 @@@@ turn) (1/8 @@@@ turn) & shaftStyle %~ loopStyle) n1 n2 (5/8 @@ turn) (7/8 @@ turn)
  || otherwise = case (endoStatus n1 endo, endoStatus n2 endo) of
                   (InLoop _, InLoop _)
                     -> connectOutside' (with & shaftStyle %~ loopStyle) n1 n2
                   _
                     -> connectOutside n1 n2

dia = graphToDia dn de (unsafePerformIO (graphToGraph' nonClusteredParams TwoPi gr))
    # frame 0.5 # lwO 0.7
    \end{diagram}
    \caption{An example $\Sp{End}$-shape}
    \label{fig:example-End}
  \end{figure}

% IN PROGRESS -- ABANDONED
%
% import           Data.Maybe
% import           Data.Tree
% import           Diagrams.TwoD.Layout.Tree
% import           Diagrams.TwoD.Polygons
% import           SpeciesDiagrams

% type Endofun = [[Tree Int]]

% mkEndo :: Int -> (Int -> Int) -> Endofun
% mkEndo n f = [map mkTree c | Cycle c <- g]
%   where
%     g = mkGraph f [0 .. n-1]
%     hairs = [h | Hair h <- g]
%     mkTree :: Int -> Tree Int
%     mkTree i = Node i (map mkTree (childrenOf i))
%     childrenOf i = catMaybes (map (childOf i) hairs)
%     childOf i [] = Nothing
%     childOf i (x:xs) = childOf' i x xs
%     childOf' i x [] = Nothing
%     childOf' i x (y:ys) | y == i = Just x
%                         | otherwise = childOf' i y ys

% drawEndo :: Endofun -> Diagram B R2
% drawEndo = hcat' (with & sep .~ 1) . map drawComponent

% drawComponent :: [Tree Int] -> Diagram B R2
% drawComponent = flip cyc' 1 . map drawT
%   where
%     drawT = renderTree mloc (~~) . symmLayout' (with & slHSep .~ 4 & slVSep .~ 4)

% endo = drawEndo (mkEndo 10 (\n -> if n == 0
%                                      then 1
%                                      else (n `div` 3)))

% dia = endo
%   # lwO 0.7
%   # frame 0.5

  Some reflection shows that endofunctions can be characterized as
  permutations of rooted trees, \[ \Sp{End} = \Perm \comp T = \Bag
  \comp \Cyc \comp T, \] where $T = \X \cdot (\Bag \comp T)$. Each
  element which is part of a cycle serves as the root of a tree;
  iterating an endofunction starting from any element must eventually
  reach a cycle, so every element belongs to some
  tree. \pref{fig:example-End} illustrates this by highlighting each
  tree in a different color.  The large component contains a central
  cycle of four elements, each a different color, with a tree hanging
  off of each; the small component consists of just a single tree with
  a self-loop at its root.

  \citet{joyal} makes use of this characterization in giving an
  elegant combinatorial proof of Cayley's formula, namely, that there
  are $n^{n-2}$ labelled trees (in the graph-theoretic sense) of size
  $n$.  One can likewise give characterizations of the species of
  endofunctions with various special properties, such as injections,
  surjections, and involutions.
\end{ex}

In a computational context, it is important to keep in mind the
distinction between \emph{labels} and \emph{data}, or more generally
between \emph{labelled shapes} and \emph{(labelled) data structures}.
Labels are merely names for locations where data can be stored, and
(typically) have no particular computational significance beyond the
ability to compare them for equality. Data structures contain data
associated with each label, whereas labelled shapes have no data, only
labels.  Put more intuitively, species shapes are ``form without
content''.  As a concrete example, the numbers in
\pref{fig:example-labelled} are not data being stored in the
structures, but merely labels for the locations.  To talk about a data
structure, one must additionally specify a mapping from labels to
data; this will be made precise in~\pref{chap:labelled}.

\section{Definitions}
\label{sec:species-definition}

Informally, as we have seen, a species is a family of labelled shapes.
Crucially, the actual labels used shouldn't matter: for example,
we should get the ``same'' family of binary trees no matter what labels
we want to use.  This intuition is made precise in the formal
definition of combinatorial species as \emph{functors}.  In fact, one
of the reasons Joyal's work was so groundbreaking was that it brought
category theory to bear on combinatorics, showing that many
specific combinatorial insights could be modeled abstractly using the
language of categories.

\subsection{Species as functors}
\label{sec:species-functors}

\begin{defn}[Species \citep{joyal}]
  \label{defn:species-cat}
  A \term{species} is a functor $F : \B \to \Set$.
\end{defn}

Recall that $\B$ is the groupoid of finite sets whose morphisms are
bijections, and $\Set$ is the category of sets and (total)
functions.

It is worth spelling out this definition in more detail, which will
also give an opportunity to explain some intuition and
terminology. Even for those who are very comfortable with category
theory, it may be hard to grasp the intuition for the abstract
definition right away.

\begin{defn}
\label{defn:species-set}

A \term{species} $F$ is a pair of mappings which
\begin{itemize}
\item sends any finite set $L$ (of \term{labels}) to a set $F\ L$ (of
  \term{shapes}), and
\item sends any bijection on finite sets $\sigma : L \bij L'$ (a
  \term{relabelling}) to a function $F\ \sigma : F\ L \to F\ L'$
  (illustrated in \pref{fig:relabelling}),
\end{itemize}
satisfying the following functoriality conditions:
\begin{itemize}
\item $F\ \id_L = \id_{F L}$, and
\item $F\ (\sigma \circ \tau) = F\ \sigma \circ F\ \tau$.
\end{itemize}
\end{defn}

\begin{figure}
  \centering
  \begin{diagram}[width=300]
import           Data.Char                      (ord)
import           Data.Maybe                     (fromMaybe)
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

t :: BTree Int
t = BNode 1 (leaf 0) (BNode 2 (leaf 3) (leaf 4))

sig :: Int -> Char
sig = ("acebd"!!)

mkNamedNode :: IsName n => (Int -> n) -> (Int -> String) -> Int -> Diagram B R2
mkNamedNode name sh n = (text (sh n) # scale labR <> lab n) # named (name n)

mkNamedTree :: IsName n => (Int -> n) -> (Int -> String) -> BTree Int -> BTree (Diagram B R2)
mkNamedTree name sh = fmap (mkNamedNode name sh)

t1 = drawBinTreeWide . mkNamedTree id show $ t
t2 = drawBinTreeWide . mkNamedTree sig ((:[]) . sig) $ t

linkedTrees = hcat' (with & sep .~ 0.5) [t1, t2]
  # applyAll (map conn [0..4 :: Int])
  where
    conn i = connectOutside'
      (with & arrowShaft .~ selectShaft i
            & shaftStyle %~ dashingG [0.05,0.05] 0
            & arrowHead .~ noHead
      )
      i (sig i)
    selectShaft i || i `elem` [0,3] = theArc # reverseTrail
                  || i `elem` [2,4] = theArc
    selectShaft _ = hrule 1
    theArc = arc (0 @@@@ deg) (75 @@@@ deg)

drawSig :: Int -> (Int -> Char) -> Diagram B R2
drawSig n sig = hcat' (with & sep .~ 0.1) (map drawOne [0..(n-1)])
  where
    drawOne i = vcat
      [ mkNamedNode id show i
      , vrule 1 # dashingG [0.05,0.05] 0
      , mkNamedNode sig ((:[]) . sig) i ]

dia = hcat' (with & sep .~ 3)
  [ drawSig 5 sig # centerXY # named "sig"
  , linkedTrees   # centerXY # named "trees"
  ]
  # connectOutside' (with & gap .~ Local 0.5) "sig" "trees"
  # frame 0.5
  # lwO 0.7
  \end{diagram}
  \caption{Relabelling} \label{fig:relabelling}
\end{figure}

We call $F\ L$ the set of ``$F$-shapes with labels drawn from $L$'',
or simply ``$F$-shapes on $L$'', or even (when $L$ is clear from
context) just ``$F$-shapes''.\footnote{Margaret Readdy's translation
  of \citet{bll} uses the word ``structure'' instead of ``shape'', but
  that word is likely to remind computer scientists of ``data
  structures'', which is, again, the wrong association: data
  structures contain \emph{data}, whereas species shapes contain only
  labels.  I try to consistently use the word ``shape'' to refer to
  the elements of a species, and reserve ``structure'' for the
  labelled data structures to be introduced in \pref{chap:labelled}.}
$F\ \sigma$ is called the ``transport of $\sigma$ along $F$'', or
sometimes the ``relabelling of $F$-shapes by $\sigma$''.

The functoriality of a species $F$ means that the actual labels used
don't matter; the resulting family of shapes is independent of the
particular labels used.  We might say that species are
\term{parametric} in label sets of a given size. In particular,
$F$'s action on all label sets of size $n$ is determined by its action
on any particular such set: if $||L_1|| = ||L_2||$ and we know $F\
L_1$, we can determine $F\ L_2$ by lifting an arbitrary bijection
between $L_1$ and $L_2$.  More formally, although Definitions
\ref{defn:species-cat} and \ref{defn:species-set} say only that a
species $F$ sends a bijection $\sigma : L \bij L'$ to a
\emph{function} $F\ \sigma : F\ L \to F\ L'$, the functoriality of $F$
guarantees that $F\ \sigma$ is a bijection as well. In particular,
$(F\ \sigma)^{-1} = F\ (\sigma^{-1})$, since $F\ \sigma \comp F\
(\sigma^{-1}) = F\ (\sigma \comp \sigma^{-1}) = F\ id = id$, and
similarly $F\ (\sigma^{-1}) \comp F\ \sigma = id$.  Thus, \emph{up to
  isomorphism}, a functor $F$ must do the same thing for any two
label sets of the same size.

We may therefore take the finite set of natural numbers $[n] = \{0,
\dots, n-1\}$ as \emph{the} canonical label set of size $n$, and write
$F\ n$ (instead of $F\ [n]$) for the set of $F$-shapes built from this
set.  In fact, since $\B$ and $\P$ are equivalent, we may formally
take the definition of a species to be a functor $\P \to \Set$ (or an
anafunctor, if we wish to avoid AC; see \pref{sec:finiteness-sets}),
which amounts to the same thing.

\begin{rem}
  Typically, the sets of shapes $F\ L$ are required to be
  \emph{finite}, that is, species are defined as functors $\B \to
  \FinSet$ into the category of \emph{finite} sets.  Of course, this
  is important if the goal is to \emph{count} things!  However,
  nothing in the present work hinges on this restriction, so it is
  simpler to drop it.

  It should be noted, however, that requiring finiteness in this way
  would be no great restriction: requiring each \emph{particular} set of
  shapes $F\ L$ to be finite is not at all the same thing as requiring
  the \emph{entire family} of shapes, $\uplus_{n \in \N} F\ n$, to be
  finite.  Typically, even in the cases that programmers care about,
  each individual $F\ n$ is finite but the entire family is not---that
  is, a type may have infinitely many inhabitants but only finitely
  many of a given size.
\end{rem}

\begin{rem}
  In my experience, computer scientists tend to have a bit of trouble
  with these definitions, because their first instinct is to think of a
  functor $\B \to \Set$ from a \emph{computational} point of view: \ie
  a species $F : \B \to \Set$, given some set of labels $L \in \B$,
  \emph{computes} some family of shapes having those labels.

  However, I find this intuition unhelpful, since it places too much
  emphasis on analyzing the ``input'' set of labels, making case
  distinctions on the size of the set, and so on.  Instead of thinking
  of functors $\B \to \Set$ as computational, it is better to think of
  them as \emph{descriptive}.  We begin with some entire family of
  labelled shapes, and want to classify them according to the labels
  that they use. A functor $\B \to \Set$ is then a convenient
  technical device for organizing such a classification: it describes
  a family of labelled shapes \emph{indexed by} their labels.

  Given this shift in emphasis, one might think it more natural to
  define a set of labelled shapes along with a function mapping shapes
  to the set of labels contained in them (indeed, down this path lie
  the notions of \term{containers} \citep{abbott_categories_2003,
    abbott_quotient, alti:cont-tcs, alti:lics09} and \term{stuff
    types} \citep{baez2000finite, Byrne2005}).  Species can be seen as roughly dual to these
  shapes-to-labels mappings, giving the \term{fiber} of each label
  set.  This is parallel to the equivalence between the functor
  category $\Set^\N$ and the slice category $\Set/\N$~(see the
  discussion under functor categories in \pref{sec:ct-fundamentals}).
  However, since $\B$ is not discrete, there is not an equivalence
  between $\Set^\B$ and $\Set/\B$; this seems to account for the fact
  that species and containers (and, more generally, operads and stuff
  types/clubs \citep[p. 2]{kelly2005operads}) seem so closely related
  but without a simply expressible relationship.
\end{rem}

\begin{rem}
  Historically, Joyal's first paper~\citeyearpar{joyal} defined
  species as endofunctors $\B \to \B$.  Given a restriction to finite
  families of shapes, and the observation that functors preserve
  isomorphisms, this is essentially equivalent to $\B \to \FinSet$,
  which is the definition used in Joyal's second
  paper~\citeyearpar{joyal86} as well as, later, by \citet{bll}.  It
  can be argued, however, that this second formulation is more
  natural, especially when one wishes to make the connection to
  functors $\FinSet \to \FinSet$ (or $\Set \to \Set$); see
  \pref{chap:labelled}.
\end{rem}

\subsection{Cardinality restriction}
\label{sec:cardinality-restr}

For any species $F$ and natural number $n$, we may define \[ F_n\ L
\defeq \begin{cases} F\ L & \text{if } \size L = n \\ \varnothing &
  \text{otherwise} \end{cases}. \] That is, $F_n$ is the restriction
of $F$ to label sets of size exactly $n$.  For example, $\Bag$ is the
species of sets of any size; $\Bag_4$ is the species of sets of size
$4$.  This is well defined since the action of a species is determined
independently on label sets of each size.  More abstractly, as noted
previously, $\B$ (and $\P$) are disconnected categories, so functors
out of them are equivalent to a disjoint union of individual functors
out of each connected component; replacing the component functors at
individual sizes will always result in another valid overall functor.

More generally, we can ``kill'' any subset of sizes using arbitrary
predicates.  For example, $F_{\leq n}$ is the species of $F$-shapes of
size $n$ or less; similarly, $F_{\geq n}$ is the species of $F$-shapes
of size $n$ or greater.  We also write $F_+$ as a shorthand, and say
``nonempty $F$'', for $F_{\geq 1}$, the species $F$ restricted to
nonempty sets of labels.

\subsection{The category of species}
\label{sec:category-of-species}

Recall that $\fc \C \D$ denotes the \term{functor category} whose
objects are functors and whose morphisms are natural transformations
between functors.  We may thus consider the \term{category of
  species}, $\Spe \defeq (\fc \B \Set)$, where the objects are
species, and morphisms between species are label-preserving mappings
which commute with relabelling---that is, mappings which are entirely
``structural'' and do not depend on the labels in any way. For
example, an in-order traversal constitutes such a mapping from the
species of binary trees to the species of lists, as illustrated in
\pref{fig:species-morphism}: computing an in-order traversal and then
relabelling yields the same list as first relabelling and then doing
the traversal.

\begin{figure}
    \later{Add labels to the arrows?}
    \centering
  \begin{diagram}[width=300]
import Diagrams.TwoD.Layout.Tree
import SpeciesDiagrams
import Data.Char (ord)

charLabel c = mkLeaf (text [c] # fc black <> circle 1 # fc (colors !! (ord c - ord 'a'))) ()
cnumbered n = mkLeaf (text (show n) # fc black <> circle 1 # fc (colors !! n)) ()
clettered n = mkLeaf (text [['a' ..] !! n] # fc black <> circle 1 # fc (colors !! n)) ()

sps =
  [ drawList' charLabel "cdbafeg"      # centerXY # named "la"
  , drawList' cnumbered [2,3,1,0,5,4,6] # centerXY # named "l1"
  , wideTree cnumbered sampleBTree7     # centerXY # named "t1"
  , wideTree clettered sampleBTree7     # centerXY # named "ta"
  ]

dia = decoratePath (rect 25 20) sps
    # connectOutside' (aOpts & tailGap .~ Local 5) "t1" "l1" -- top
    # connectOutside' (aOpts & tailGap .~ Local 5) "t1" "ta" -- left
    # connectOutside' aOpts "l1" "la" -- right
    # connectOutside' (aOpts & tailGap .~ Local 5) "ta" "la" -- bottom
    # frame 1
    # lwO 0.7

aOpts = with & gap .~ Local 3 & headLength .~ Local 1.5
  \end{diagram}
  %$
    \caption{Inorder traversal is natural}
    \label{fig:species-morphism}
\end{figure}

It turns out that functor categories have a lot of interesting
structure.  For example, as we will see, $\fc \B \Set$ has (at least)
six different monoidal structures!  Much of
\pref{chap:generalized-species} is dedicated to exploring and
generalizing this structure.

\subsection{Species in HoTT}
\label{sec:species-hott}

We now turn to porting the category of species from set theory
into HoTT.  Recall that $\BT$ denotes the \hott{groupoid} with
objects \[ \FinSetT \defeq (A : \Type) \times \isFinite(A), \]
where \[ \isFinite(A) \defeq \ptrunc{(n : \N) \times (A \equiv \Fin
  n)} \] and with morphisms given by paths. \later{mention something
  about $\PT$ here?}
% Recall
% also that $\PT$ denotes the \hott{groupoid} whose objects are natural
% numbers and whose morphisms $\hom[\PT] m n$ are equivalences $\Fin m
% \equiv \Fin n$, and that $\ST$ denotes the \hott{category} of
% $0$-types (sets) and functions.

\begin{defn}
  A \term{constructive species}, or \hott{species}, is an
  \hott{functor} $F : \BT \to \ST$.  We use $\Spe = \fc \BT \ST$ to
  refer to the \hott{category} of constructive species, the same name
  as the category $\fc \B \Set$ of set-theoretic species; while
  technically ambiguous, this should not cause confusion since it
  should always be clear from the context whether we are working in
  set theory or in HoTT.  Likewise, when working in the context of
  HoTT we will often simply say ``species'' instead of ``constructive
  species''.
\end{defn}

The above definition corresponds directly to the definition of species
in set theory.  However, it is more specific than necessary.  In fact,
in HoTT, \emph{any} function of type $\BT \to \ST$ (that is, a
function from objects of $\BT$ to objects of $\ST$) is automatically
an \hott{functor}.  Since the morphisms in $\BT$ are just paths,
functoriality corresponds to transport.  Thus, as hinted in
\pref{chap:prelim}, within HoTT it is simply impossible to write down
an invalid species.  This is a strong argument for working within type
theory in general and HoTT in particular: it provides exactly the
right sort of type system which allows expressing only valid species.

Nevertheless, it is still not perfectly clear whether this is the
right encoding of species within homotopy type theory.  It cannot be
directly justified by showing that $\fc \B \Set$ and $\fc \BT \ST$ are
categorically equivalent; this does not even make sense since they
live in entirely different foundational frameworks.  Rather, a
justification must be extensional, in the sense of showing that the
two definitions have similar properties and support similar
operations.  In a sense, much of \pref{chap:generalized-species} is
precisely such an extensional justification.

\section{Isomorphism and equipotence}
\label{sec:iso-equipotence}

Just as with HoTT itself, \emph{sameness} and related notions are also
at the heart of the theory of species.  In this section we explore
isomorphism of species and of species shapes, as well as a coarser
notion of equivalence on species known as \term{equipotence}.

\subsection{Species isomorphism}
\label{sec:species-isomorphism}

An isomorphism of species is just an isomorphism in the category of
species, that is, a pair of inverse natural transformations.  Species
isomorphism preserves all the interesting \emph{combinatorial}
properties of species; hence in the combinatorics literature
everything is always done up to isomorphism. However, this is usually
done in a way that glosses over the \emph{computational} properties of
the isomorphisms.  Formulating species within HoTT gives us the best
of both worlds: naturally isomorphic functors between
\hott{categories} are equal, and hence isomorphic species are
literally identified; however, equalities (\ie paths) in HoTT may
still have computational content. \later{HoTT forces us to be
  disciplined about applying conversions in the right places, which
  may seem less convenient than the happy-go-lucky world of
  traditional mathematics, where isomorphisms are simply glossed over,
  but types\dots should I include a sentence like this at all?}

\subsection{Shape isomorphism and unlabelled species}
\label{sec:unlabelled}

In addition to isomorphism of entire species, there is also a natural
notion of isomorphism for individual species \emph{shapes}.  For
example, consider the set of permutations on the labels $\{0,1,2\}$,
shown in \pref{fig:permutations-three}. Notice that some of these
permutations ``have the same form''.  For example, the only difference
between the two permutations shown in \pref{fig:same-form-perms} is
their differing labels.  On the other hand, the two permutations shown
in \pref{fig:different-form-perms} are fundamentally different, in the
sense that there is no way to merely \emph{relabel} one to get the
other.

\begin{figure}
  \centering
  \begin{diagram}[width=200]
import SpeciesDiagrams
import Data.List.Split
import Data.List (permutations)

permStructures
  = centerXY
  . hcat' (with & sep .~ 1)
  . map (vcat' (with & sep .~ 0.5))
  . chunksOf 2
  . map drawPerm
  . perms
  $ [0..2]  -- $

dia = permStructures
  # lwO 0.7
  # frame 0.5
  \end{diagram}
  \caption{Permutations of size three}
  \label{fig:permutations-three}
\end{figure}

\begin{figure}
  \centering
  \begin{diagram}[width=200]
import SpeciesDiagrams

permStructures
  = centerXY
  . hcat' (with & sep .~ 1)
  . map drawPerm
  $ [[[1],[0,2]], [[2],[0,1]]]  -- $

dia = permStructures
  # lwO 0.7
  # frame 0.5
  \end{diagram}
  \caption{Two permutations with the same form}
  \label{fig:same-form-perms}
\end{figure}

\begin{figure}
  \centering
  \begin{diagram}[width=200]
import SpeciesDiagrams

permStructures
  = centerXY
  . hcat' (with & sep .~ 1)
  . map drawPerm
  $ [[[1],[0,2]], [[0,1,2]]]  -- $

dia = permStructures
  # lwO 0.7
  # frame 0.5
  \end{diagram}
  \caption{Two permutations with different forms}
  \label{fig:different-form-perms}
\end{figure}

We can formalize this idea as follows.

\begin{defn}
  Given a species $F$ and $F$-shapes $f_1 : F\ L_1$ and $f_2 : F\
  L_2$, we say $f_1$ and $f_2$ are \term{equivalent up to
    relabelling}, or \term{have the same form}, and write $f_1
  \relabel f_2$, if there is some bijection $\sigma : L_1 \bij L_2$
  such that $F\ \sigma\ f_1 = f_2$. If we wish to emphasize the
  particular bijection relating $f_1$ and $f_2$ we may write $f_1
  \relabel_\sigma f_2$.
\end{defn}

Thus, the two labelled shapes shown in \pref{fig:same-form-perms} are
related by $\relabel$, whereas those shown in
\pref{fig:different-form-perms} are not.

\begin{defn}
  Given a species $F$, denote by $\sh(F)$ the groupoid whose objects
  are $F$-shapes---that is, finite sets $L$ together with an element
  of $F\ L$---and whose morphisms are given by the $\relabel$
  relation.
\end{defn}

\begin{proof}
  We need to show this is a well-defined groupoid, \ie that $\relabel$
  is an equivalence relation.  The $\relabel$ relation is reflexive,
  yielding identity morphisms, since any shape is related to itself by
  the identity bijection.  If $f \relabel g \relabel h$ then $f
  \relabel h$ by composing the underlying bijections.  Finally, $f
  \relabel g$ implies $g \relabel f$ since the underlying bijections
  are invertible.
\end{proof}

Given these preliminary definitions, we can now define what we mean by
a \term{form}, or \term{unlabelled shape}.

\begin{defn}
  An $F$-\term{form} is an equivalence class under $\relabel$, that
  is, a connected component of the groupoid $\sh(F)$.
\end{defn}

In other words, an $F$-form is a maximal class of labelled $F$-shapes
which are all interconvertible by relabelling.  As defined,
such classes are rather large, as they include labellings by \emph{all
  possible} sets of labels!  Typically, we consider only a
single label set of each size, such as $\Fin n$.  For example,
\pref{fig:perm-forms-four} shows all the $\Perm$-forms of size four,
using two different representations: on the right are the literal
equivalence classes of permutations on $\Fin 4$ which are equivalent
up to relabelling.  On the left are schematic representations of each
form, drawn by replacing labels with indistinguishable dots.  Note
that the schematic representations, while convenient, can break down
in more complex situations, so it is important to also keep in mind
the underlying definition in terms of equivalence classes.

\begin{figure}
  \centering
  \begin{diagram}[width=400]
import           Data.Function                  (on)
import           Data.List                      (partition, sortBy)
import           Data.Ord                       (comparing)
import qualified Math.Combinatorics.Multiset    as MS
import           SpeciesDiagrams

permForms
  = centerXY
  . vcat' (with & sep .~ 1)
  . map drawPermRow
  . (map . map) lenSort
  . groupBy' sameForm
  . perms
  $ [0 .. 3 :: Int]  -- $

parts' :: Ord a => [a] -> [[[a]]]
parts' = map (map MS.toList . MS.toList) . MS.partitions . MS.fromList

sameForm :: [[a]] -> [[a]] -> Bool
sameForm xs ys = eqLen xs ys && (and $ zipWith eqLen (lenSort xs) (lenSort ys))
  where
    eqLen = (==) `on` length

lenSort = sortBy (comparing length)

groupBy' :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy' _    []     = []
groupBy' comp (x:rest) = (x:xs) : groupBy' comp ys
  where (xs,ys) = partition (x `comp`) rest

drawPermForm
  = hcat' (with & sep .~ 0.2)
  . map ((\l -> cyc' l 0.8) . map (const dot))
  where
    dot = circle labR # fc black

drawPermRow ps = hcat' (with & sep .~ 2)
    [ (map . map . const) () (head ps) # drawPermForm # alignR
    , lPerms
    ]
  where
    lPerms = hcat' (with & sep .~ 1) . map drawPerm $ ps

dia = permForms
  # lwO 0.7
  # frame 0.5
  \end{diagram}
  \caption{$\Perm$-forms of size $4$}
  \label{fig:perm-forms-four}
\end{figure}

\begin{rem}
  What are here called \term{forms} are more often called \term{types}
  in the species literature; but using that term would lead to
  unnecessary confusion in the present context.
\end{rem}

\subsection{Equipotence}
\label{sec:equipotence}

It turns out that there is another useful equivalence relation on
species which is \emph{weaker} (\ie coarser) than
isomorphism/equality, known as \term{equipotence}.

\begin{defn}
  An \term{equipotence} between species $F$ and $G$, denoted $F
  \equipot G$,\footnote{In the species literature, equipotence is
    usually denoted $F \jeq G$, but we are already using that symbol
    to denote judgmental equality.} is defined as an ``unnatural''
  isomorphism between $F$ and $G$---that is, two families of functions
  $\varphi_L : F\ L \to G\ L$ and $\psi_L : G\ L \to F\ L$ such that
  $\varphi_L \comp \psi_L = \psi_L \comp \varphi_L = \id$ for every
  finite set $L$.  Note in particular there is no requirement
  that $\varphi$ or $\psi$ be natural.
\end{defn}

We can see that an equipotence preserves the \emph{number} of shapes
of each size, since $\varphi$ and $\psi$ constitute a bijection, for
each label set $L$, between the set of $F$-shapes $F\ L$ and the set
of $G$-shapes $G\ L$.  Isomorphic species are of course equipotent,
where the equipotence also happens to be natural.  It may be initially
surprising, however, that the converse is false: there exist
equipotent species which are not isomorphic. Put another way, having
the same number of structures of each size is not enough to ensure
isomorphism.

One good example is the species $\List$ of lists and the species
$\Perm$ of permutations.  As is well-known, there are the same number
of linear orderings of $n$ labels as there are permutations of $n$
labels (namely, $n!$).  In fact, this is so well-known that
mathematicians routinely conflate the two, referring to an ordered
list as a ``permutation''. \pref{fig:lists-and-perms} shows the six
lists and six permutations on three labels.

\begin{figure}
  \centering
  \begin{diagram}[width=400]
import SpeciesDiagrams
import Data.List.Split
import Data.List (permutations)

listStructures
  = centerXY
  . hcat' (with & sep .~ 0.7)
  . map (vcat' (with & sep .~ 0.5))
  . chunksOf 2
  . map (drawList' labT)
  . permutations
  $ [0..2]  -- $

permStructures
  = centerXY
  . hcat' (with & sep .~ 1)
  . map (vcat' (with & sep .~ 0.5))
  . chunksOf 2
  . map drawPerm
  . perms
  $ [0..2]  -- $

dia = hcat' (with & sep .~ 3) [listStructures, permStructures]
  # lwO 0.7
  # frame 0.5
  \end{diagram}
  \caption{Lists and permutations on three labels}
  \label{fig:lists-and-perms}
\end{figure}

However, $\List$ and $\Perm$ are not isomorphic.  The intuitive way to
see this is to note that although there is only a single list form of
any given size, for $n \geq 2$ there are multiple permutation forms.
Every permutation, \ie bijective endofunction, can be decomposed into
a set of cycles, and a relabelling can only map between permutations
with the same number of cycles of the same sizes.  There is thus one
$\Perm$-form corresponding to each integer partition of $n$
(\pref{fig:perm-forms-four} shows the five permutation forms of size
$4$, corresponding to $4 = 3 + 1 = 2 + 2 = 2 + 1 + 1 = 1+1+1+1$).

More formally, suppose there were some \emph{natural} isomorphism
witnessed by $\varphi : \nt \List \Perm$ and $\psi : \nt \Perm \List$.
In particular, for any $\sigma : K \bij K$ we would then have \[
\xymatrix{ \List\ K
  \ar[r]^{\varphi_K} \ar[d]_{\List\ \sigma} & \Perm\ K \ar[d]^{\Perm\ \sigma} \\
  \List\ K \ar[r]_{\varphi_K} & \Perm\ K } \] and similarly for
$\psi_K$ in the opposite direction.  This says that any two
$K$-labelled lists related by the relabelling $\sigma$ correspond to
permutations which are also related by $\sigma$.  However, as we have
seen, \emph{any} two lists are related by some relabelling, and thus
(since $\varphi$ and $\psi$ constitute a bijection) any two
permutations would have to be related by some relabelling as well, but
this is false.

This argument shows that there cannot exist a natural isomorphism
between $\List$ and $\Perm$.  However, the claim is that they are
nonetheless equipotent.  Again, this fact is very well known, but it
is still instructive to work out the details of a formal proof.

The first and most obvious ``proof'' is to send the permutation
$\sigma : \perm{(\Fin n)}$ to the list whose $i$th element is
$\sigma(i)$, and vice versa.  Note, however, that this is not really a
proof, since it only gives us a specific bijection $\List\ (\Fin n)
\bij \Perm\ (\Fin n)$, rather than a family of bijections $\List\ K
\bij \Perm\ K$.  We will return to this point shortly.

The second proof, known as the \term{fundamental transform}, is more
elegant from a combinatorial point of view.  For more details, see
\citet{cartier1969problemes}, \citet{knuth1973sorting}, or
\citet[p. 22]{bll}.  We first describe the mapping from permutations
on $\Fin n$ to lists on $\Fin n$: given a permutation, order its
cycles in decreasing order of their smallest element, and then
transcribe each cycle as a list beginning with the smallest element.
\pref{fig:fundamental-transform} shows an example where the
permutation $(35)(26)(014)$ (whose cycles have minimum elements $3$,
$2$, and $0$ respectively) is sent to the list $3526014$, which for
emphasis is drawn with the height of each node corresponding to the
size of its label.  To invert the transformation, partition a list
into segments with each record minimum beginning a new segment, and
turn each such segment into a cycle.  For example, in the list
$3526014$, the elements $3$, $2$, and $0$ are the ones which are
smaller than all the elements to their left, so each one marks off the
beginning of a new cycle.

\begin{figure}
  \centering
  \begin{diagram}[width=300]
import           Control.Arrow
import           SpeciesDiagrams

permToList = hcat' (with & sep .~ 1)
  [ drawPerm [[3,5],[2,6],[0,1,4]]
  , arrow 1
  , mountainRange labT [3,5,2,6,0,1,4]
  ]

mountainRange nd ns = lst # applyAll [conn i || i <- [0 :: Int .. length ns - 2]] # centerY
  where
    elts = map (id &&& nd) ns # zipWith (second . named) [0 :: Int ..] # map (\(i,n) -> n # translateY (fromIntegral i / 2))
    w    = (maximum . map width) elts
    lst  = hcat' (with & sep .~ w/2) elts
    conn i = withNames [i,i+1] (\[a,b] -> beneath (location a ~~ location b))

dia = permToList
  # lwO 0.7
  # frame 0.5
  \end{diagram}
  \caption{The fundamental transform}
  \label{fig:fundamental-transform}
\end{figure}

The way the fundamental transform is presented also makes it clear how
to generalize from $\Fin n$ to other finite sets of labels $L$: all we
require is a linear order on $L$, in order to find the minimum label
in a given cycle and sort the cycles by minimum element, and to
determine the successive record minima in a list.  Looking back at the
first, ``obvious'' proof, which sends $\sigma$ to the list whose $i$th
element is $\sigma(i)$, we can see that it also can be generalized to
work for any finite set $L$ equipped with a linear order.  In
particular, being equipped with a linear order is equivalent to being
equipped with a bijection to $\Fin n$, as explained in
\pref{sec:manifestly-finite}.

Intuitively, then, the reason that these two families of bijections
are not natural is that they do not work \emph{uniformly} for all sets
of labels, but require some extra structure.  Any finite label set can
be given a linear order, but the precise choice of linear order
determines how the bijections work.

Considering this from the viewpoint of HoTT yields additional insight.
A family of functions like $\varphi_K$ would typically correspond in
HoTT to a function of type \[ \varphi : (K : \FinSetT) \to \List\ K
\to \Perm\ K. \] It is certainly possible to implement a function with
the above type (for example, one which sends each list to the cyclic
permutation with elements in the same order), but as we have seen, it
is not possible to implement one which is invertible.  Writing an
invertible such function also requires a linear ordering on the type
$K$.  We could, of course, simply take a linear order as an extra
argument, \[ \varphi : (K : \FinSetT) \to \cons{LinOrd}\ K \to \List\
K \to \Perm\ K. \]

Alternatively, recall that $K$ contains evidence of its finiteness in
the form of an equivalence $K \equiv \Fin n$.  This equivalence
induces a linear ordering on $K$, corresponding to the natural linear
ordering $0 < 1 < 2 < \dots$ on $\Fin n$.  In other words, each finite
set $K$ already comes equipped with a linear ordering!  However,
recall that the finiteness evidence is sealed inside a propositional
truncation, so we cannot use it in implementing a function of type $(K
: \FinSetT) \to \List\ L \to \Perm\ K$.  If we could, the resulting
function would indeed \emph{not} be natural, and it is instructive to
see why.  A path $K = K$ corresponds to a permutation on $K$, but
\emph{does not have to update the finiteness evidence in conjunction}
with the permutation.  Thinking of the finiteness evidence as giving a
linear order on $K$, another way to say this is that permutations $K =
K$ need not be order-preserving.  Naturality is not satisfied,
therefore, since applying the fundamental transform directly may give
results completely incompatible with those obtained by applying a
non-order-preserving permutation followed by the fundamental transform.

\citet[p. 22]{bll} note that the fundamental transform \emph{is} in
fact compatible with \emph{order-preserving} bijections.  If we
consider functors $\L \to \Set$, where $\L$ is the groupoid of finite
sets equipped with linear orders, along with order-preserving
bijections, then the fundamental transform is indeed a natural
isomorphism between $\List$ and $\Perm$.  Such functors are called
$\L$-species, and are discussed further in \pref{sec:L-species}.

Back in $\FinSetT$, however, in order to use the linear order
associated to each finite set $K$, we must produce a mere proposition.
We cannot directly produce an equivalence---but we certainly can
produce the propositional truncation of one.  In particular we can
encode the fundamental transform as a function of type \[ \chi : (K :
\FinSetT) \to \ptrunc{\List\ K \equiv \Perm\ K}. \] This is precisely
the right way to encode equipotence in HoTT.  For suppose we know that
$\List\ K$ is finite of size $n$, that is, we have an inhabitant of
the type $(n : \N) \times \ptrunc{\List\ K \equiv \Fin n}$.  Then we
can conclude that $\Perm\ K$ has the same size: since we want to
produce the mere proposition $\ptrunc{\Perm\ K \equiv \Fin n}$, we are
allowed to use the equivalence $\List\ K \equiv \Fin n$ as well as the
equivalence $\List\ K \equiv \Perm\ K$ produced by $\chi_K$; composing
them and injecting back into a truncation yields the desired result.
On the other hand, we cannot use the results of $\chi$ to actually
compute a correspondence between elements of $\List\ K$ and $\Perm\
K$.

One might expect that there are other ways to obtain an equipotence.
That is, the correspondence between $\List$ and $\Perm$ is not a
natural isomorphism because it additionally requires a linear order
structure on the labels; might there be other equipotences which
require other sorts of structure on the labels?

I conjecture that a linear order is as strong as one could ever want;
that is, for any species which are provably equipotent, there exists a
proof making use of a linear order on the set of labels.

\begin{conj} \label{conj:linear-equipotence}
  The type of natural isomorphisms with access to a linear order is
  logically equivalent to the type of equipotences. That is, for all
  species $F$ and $G$, \[ ((L : \SetL) \to (F\ L \equiv G\ L)) \lequiv
  ((L : \FinSetT) \to \ptrunc{F\ L \equiv G\ L}). \]
\end{conj}

Note that on the left-hand side, $F\ L$ and $G\ L$ are not well-typed
as written, but are used as shorthands for the application of $F$ and
$G$ to $\iota L$, where $\iota : \SetL \to \FinSetT$ is the evident
injection.

\begin{proof}[Proof (sketch)]
  I describe here a plan of attack, \ie an outline of a possible
  proof, although as explained below, I expect that completing the
  proof will require a considerable amount of effort.
  \begin{itemize}
  \item[$(\to)$] This direction is certainly true and quite easy to
    show.  We are given a function $f : (L : \SetL) \to (F\ L \equiv
    G\ L)$ and some $L : \FinSetT$, and must produce
    $\ptrunc{F\ L \equiv G\ L}$.  Since we are producing a mere
    proposition we may unwrap the finiteness evidence in $L$ to turn
    it into a $\SetL$, pass it to $f$, and then wrap the result in a
    propositional truncation.  Intuitively, this direction is true
    since every natural isomorphism is also an equipotence.
  \item[$(\leftarrow)$] This is the more interesting direction.  We
    are given a function $f : (L : \FinSetT) \to \ptrunc{F\ L \equiv
      G\ L}$ and some $L : \SetL$, \ie a finite set equipped with a
    linear order.  We must produce an equivalence $F\ L \equiv G\ L$.
    We can easily turn $L$ into a $\FinSetT$ by applying a
    propositional truncation; passing this to $f$ results in
    some $s : \ptrunc{F\ L \equiv G\ L}$.

    The trick is now to uniquely characterize the particular
    equivalence $F\ L \equiv G\ L$ we wish to produce, which we can do
    by producing linear orderings on the $(F\ L)$-shapes and $(G\
    L)$-shapes, and matching them in order. We have the linear
    ordering on $L$ to help, but the task still seems impossible
    without some sort of knowledge about $F$ and $G$.  Fortunately, it
    is possible to deeply characterize species based on their
    extensional behavior.  In particular, every species can be
    uniquely decomposed as a sum of \term{molecular}
    species~\citep[\Sect 2.6]{bll}, where each molecular species is of
    the form $\X^n/H$ for some natural number $n$ and some subgroup $H
    \subseteq \S_n$ of the symmetric group on $n$ elements.  That is,
    molecular species are lists of a particular length quotiented by
    some symmetries: we let $H$ act on $\X^n$-shapes by permuting
    their elements, and consider equivalence classes of $\X^n$-shapes
    corresponding to orbits under $H$.  (For a fuller discussion of
    such quotient species, see \pref{sec:molecular-atomic}.) The study
    and classification of, molecular and atomic species takes up an
    entire section of \citet{bll}, and porting all of the definitions
    and theorems there to HoTT would be a formidable undertaking,
    though I expect it would yield considerable insight.  Such an
    undertaking is left to future work.

    In any case, an equivalence $F\ L \equiv M_1\ L + M_2\ L + M_3\ L
    + \dots$ should yield a canonical ordering on the classes of
    $F$-shapes resulting from each $M_i$: all the $M_1$ shapes come
    first, followed by the $M_2$ shapes, and so on.  It remains to
    show that we can put a linear ordering on the $F$ shapes generated
    by each $M_i$.

    Recall that each $M_i$ is of the form $\X^n/H$.  We can thus use
    the linear order on $L$ to put an ordering on $M_i\ L$ as follows.
    First, in the case that $H = 1$, \ie the trivial group, we can
    order all the $n!$ labelled $\X^n$ shapes using a lexicographic
    order (or some other appropriate order derived from the order on
    $L$).  If $H$ is nontrivial, then the orbits of $\X^n$ under the
    action of $H$ are themselves the $M_i$-shapes, and we can extend
    the ordering on the $\X^n$ shapes to orbits thereof, for example,
    by ordering the orbits according to the smallest $\X^n$-shape
    contained in each.

    Even if we succeed in uniquely characterizing some equivalence,
    note that the equivalence we thus characterize may not be the same
    as the $s$ obtained as the output of the function $f$.  We must
    construct the final equivalence ``from scratch'', somehow using
    the fact that we know \emph{some} equivalence exists to construct
    the one we have characterized.  It is not entirely clear how to do
    this.  One idea might be to construct a permutation on $G\ L$
    which, when composed with the equivalence given by $f$, produces
    the desired equivalence.  However, this is admittedly the
    sketchiest part of the proof.
  \end{itemize}
\end{proof}

\section{Generating functions}
\label{sec:generating-functions}

\term{Generating functions} are a well-known tool in combinatorics,
used to manipulate sequences of interest by representing them as the
coefficients of certain formal power series.  As Wilf says, ``A
generating function is a clothesline on which we hang up a sequence of
numbers for display'' \citep{wilf-gfology}.  Generating functions are
important to discuss here since they are in some sense the point of
departure for the entire theory of species: although species can be
understood independently, from a historical point of view species were
explicitly developed in order to generalize (specifically, to
\emph{categorify}) the theory of generating functions.  As such,
generating functions yield important insights into the theory of
species.

There are many types of generating functions; we will consider two in
particular: \term{ordinary} generating functions (ogfs), and
\term{exponential} generating functions (egfs).  Ordinary generating
functions are of the form \[ \sum_{n \geq 0} a_n x^n \] and represent
the sequence $a_0,a_1,a_2, \dots$.  For example, the ogf $x + 2x^2 +
3x^3 + \dots$ represents the sequence $0,1,2,3,\dots$.  Exponential
generating functions are of the form \[ \sum_{n \geq 0}
a_n \frac{x^n}{n!}. \]  For example, the egf $1/(1-x) = 1 + x + x^2 + x^3
+ \dots = 1 + x + \frac{2x^2}{2} + \frac{6x^3}{6} + \dots$ represents
the sequence $1,1,2,6,24,\dots$.

This would be unremarkable if it were just a \emph{notation} for
sequences, but it is much more.  The crucial point is that natural
\emph{algebraic} operations on generating functions correspond to
natural \emph{combinatorial} operations on the sequences they
represent (or, more to the point, on the combinatorial objects the
sequences are counting).  This theme will be explored throughout the
chapter: as each combinatorial operation on species is introduced, its
corresponding algebraic operation on generating functions will also be
discussed.

To each species $F$ we associate two generating
functions\footnote{There are more, \eg the cycle index series and
  asymmetry index series \citep{bll}, but they are outside the scope of
  this dissertation.}, an egf $F(x)$ and an ogf $\unl{F}(x)$, defined
as follows.
\begin{defn}
  The egf $F(x)$ associated to a species $F$ is defined by
  \[ F(x) = \sum_{n \geq 0} f_n \frac{x^n}{n!}, \] where $f_n =
  \size{(F\ n)}$ is the number of labelled $F$-shapes of size $n$.
\end{defn}
\begin{ex}
  There are $n!$ labelled $\List$-shapes (that is, linear
  orders) on $n$ labels, so \[ \List(x) = \sum_{n \geq 0} n!
  \frac{x^n}{n!} = \sum_{n \geq 0} x^n = \frac{1}{1-x}. \] Note that
  this is a \emph{formal} power series, and in particular we do not
  worry about issues of convergence.
\end{ex}

\begin{defn}
  The ogf $\unl F(x)$ associated to a species $F$ is defined by \[
  \unl F(x) = \sum_{n \geq 0} \unl f_n x^n, \] where $\unl f_n =
  \size{(F\ n/\mathord{\relabel})}$ is the number of distinct $F$-\emph{forms} (that
  is, equivalence classes of $F$-shapes under relabelling) of size $n$.
\end{defn}
\begin{ex}
  There is only one list form of each size, so \[ \unl \List(x) =
  \sum_{n \geq 0} x^n = \frac{1}{1-x} \] as well.  Species for which
  $F(x) = \unl F(x)$ are called \term{regular} and are discussed in
  more detail in \pref{sec:molecular-atomic}.  For an example of a non-regular
  species, the reader is invited to work out the egf and ogf for the
  species $\Cyc$ of cycles.
\end{ex}

One can see that the mapping from species to generating functions
discards information, compressing an entire set of shapes or forms
into a single number (\pref{fig:species-gf-hom}).  Once one has
defined the notion of species, it is not hard to come up with the
notion of generating functions as a sort of ``structured summary'' of
species.

\begin{figure}
  \centering
  \begin{diagram}[width=350]
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams
import           Structures                     hiding (text')

dia =
  (vcat' (with & sep .~ 3) . map alignR)
  [ hcat' (with & sep .~ 3) [text' 8 "B", myBinTreeBuckets (with & showIndices .~ False)]
  , hcat' (with & sep .~ 3) [text' 8 "B(x)", bucketed (map ((:[]) . text' 8 . show) [1,1,2,5,14,42])]
  ]
  # frame 0.5
  # lwO 0.7

myBinTreeBuckets opts
  = bucketed' opts
      ( map (map (pad 1.3 . centerXY . drawBinTree' (with & slHSep .~ 4 & slVSep .~ 3) . fmap (const genElt))) allBinTrees
      # zipWith scale [1,1,0.5, 0.2, 0.2, 0.08]
      )

genElt = circle 0.8 # fc mlocColor
  \end{diagram}
  \caption{Correspondence between species and generating functions}
  \label{fig:species-gf-hom}
\end{figure}

Historically, however, generating functions came first.  As Joyal
makes explicit in the introduction to his seminal paper \textit{Une
  Th{\'e}orie Combinatoire des {S}{\'e}ries Formelles}
\citeyearpar{joyal}---in fact, it is even made explicit in the title of
the paper itself---the main motivation for inventing species was to
generalize the theory of generating functions, putting it on firmer
combinatorial and categorical ground.  The theory of generating
functions itself was already well-developed, but no one had yet tried
to view it through a categorical lens.

The general idea is to ``blow everything up'', replacing natural
numbers by sets; addition by disjoint union; product by pairing; and
so on.  In a way, one can see this process as ``imbuing everything
with constructive significance''; this is one argument for the
naturalness of the theory of species being developed within a
constructive type theory, as attempted by this dissertation.

\section{Conclusion}
\label{sec:species-conclusion}

In this chapter we have seen the definition of species, both in set
theory and type theory, and some related notions.  