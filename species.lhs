%% -*- mode: LaTeX; compile-command: "mk" -*-

%include thesis.fmt

\chapter{Combinatorial species}
\label{chap:species}

\todo{Go through and add some back references to preliminaries chapter?}
\todo{List contributions of this chapter somewhere?}
\todo{Need a story for building with both color or black/white
  figures}
\todo{Include example of bounded tree width graphs somewhere.}
\todo{Include $\Cat$-valued species as an example.}

The theory of combinatorial species, introduced by \citet{joyal}, is a
unified theory of \term{combinatorial structures} or \term{shapes}.
It was originally intended as a unified framework for algebraically
describing combinatorial structures of interest, and in particular one
which gave new justification and a unifying context for an existing
body of techniques involving \term{generating functions}. It is hoped
that the beautiful theory of generating functions will also prove a
rich seam of material to mine for computational significance. However,
that is left to future work; this dissertation instead focuses on the
idea of \term{labels}.

One of Joyal's great insights in formulating the theory of species was
to take the notion of \emph{labelled} structures as fundamental, and
to build other notions (such as \emph{unlabelled} structures) on top
of it.  Species fundamentally describe labelled objects; for example,
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
    # pad 1.1
\end{diagram}
\caption{Representative labelled shapes} \label{fig:example-labelled}
\end{figure}

Why \emph{labelled} shapes?  In the tree shown
in~\pref{fig:example-labelled}, one can uniquely identify each
location in the tree by a path from the root, without referencing
labels at all.  However, the structure on the right illustrates one
reason labels are needed. The circle indicates that the structure has
\emph{rotational symmetry}, so there is be no way to uniquely refer
to any location except by label.  More abstractly, to correctly
enumerate unique unlabelled shapes, it is necessary to consider the
action of label permutations on labelled shapes: which shapes are
fixed by which permutations?

Beyond its focus on labels, the power of the theory of species derives
in large part from its ability to describe structures of interest
\emph{algebraically}, making them amenable to further analysis with
only a relatively small set of general tools.

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
expression \[ \List = \One + \X \cdot \List. \] The meaning of this will be
made precise later. For now, its intuitive meaning should be clear
to anyone familiar with recursive algebraic data types in a language
such as Haskell or OCaml: a labelled list ($\List$) is empty ($1$), or ($+$) a
single label ($\X$) together with ($\cdot$) another labelled list ($\List$).
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
  , mkArrow 2 (txt "T")
  , treeStructures # scale 0.5
  ]
  # centerXY
  # pad 1.1

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
  Algebraically, such trees can be described by \[ \Bin = \One + \X
  \cdot \Bin \cdot \Bin. \]
\end{ex}

\todo{More examples: Cycles, bags, permutations.}

  In a computational context, it is important to keep in mind the
  distinction between \emph{labels} and \emph{data}, or more generally
  between \emph{labelled shapes} and \emph{labelled (data)
    structures}.  Labels are merely names for locations where data can
  be stored; data structures contain data associated with each label,
  whereas labelled shapes have no data, only labels.  Put more
  intuitively, species shapes are ``form without content''.  As a
  concrete example, the numbers in \pref{fig:example-labelled} are not
  data being stored in the structures, but merely labels for the
  locations.  To talk about a data structure, one must also specify a
  mapping from locations to data; this will be made precise
  in~\pref{chap:labelled}.

\section{Definition}
\label{sec:species-definition}

Informally, a species is a family of labelled shapes.  Crucially, the
actual labels used ``shouldn't matter'': for example, we should get
the ``same'' binary trees no matter what labels we want to use.  This
intuition is made precise in the formal definition of combinatorial
species.

\begin{defn}[Species \citep{joyal, bll}]
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
\item $F\ id_L = id_{F L}$, and
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
            & shaftStyle %~ dashing [0.05,0.05] 0
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
      , vrule 1 # dashing [0.05,0.05] 0
      , mkNamedNode sig ((:[]) . sig) i ]

dia = hcat' (with & sep .~ 3)
  [ drawSig 5 sig # centerXY # named "sig"
  , linkedTrees   # centerXY # named "trees"
  ]
  # connectOutside' (with & gap .~ 0.5) "sig" "trees"
  # frame 0.5
  \end{diagram}
  \caption{Relabelling} \label{fig:relabelling}
\end{figure}

We call $F\ L$ the set of ``$F$-shapes with labels drawn from $L$'',
or simply ``$F$-shapes on $L$'', or even (when $L$ is clear from
context) just ``$F$-shapes''.\footnote{Margaret Readdy's translation
  of \citet{bll} uses the word ``structure'' instead of ``shape'', but
  that word is likely to remind computer scientists of ``data
  structures'', but again, that is the wrong association: data
  structures contain \emph{data}, whereas species shapes do not.}  $F\
\sigma$ is called the ``transport of $\sigma$ along $F$'', or
sometimes the ``relabelling of $F$-shapes by $\sigma$''.

The functoriality of relabelling means that the actual labels used
don't matter; we get ``the same shapes'', up to relabelling, for any
label sets of the same size.  We might say that species area
\term{parametric} in the label sets of a given size. In particular,
$F$'s action on all label sets of size $n$ is determined by its action
on any particular such set: if $||L_1|| = ||L_2||$ and we know $F\
L_1$, we can determine $F\ L_2$ by lifting an arbitrary bijection
between $L_1$ and $L_2$.  So we often take the finite set of natural
numbers $[n] = \{0, \dots, n-1\}$ as \emph{the} canonical label set of
size $n$, and write $F\ n$ (instead of $F\ [n]$) for the set of
$F$-shapes built from this set.

Some intuition is in order: why is $F$ required to be functorial?
The answer is that it is functoriality which forces the family of
shapes to be ``independent'' of the particular labels chosen.
Intuitively, labels should be arbitrary; a species $F$ should not be
able to ``do something different'' depending on the particular set of
labels.  For example, we could define a mapping $B$ which
\todo{picture(s)}
\begin{itemize}
\item sends the set of labels $\{a,b,c\}$ to the set of ``shapes''
  $\{I,J,K\}$,
\item sends any other set to $\{P,Q\}$, and
\item sends every bijection to the identity function when possible, or
  to the constantly $I$ or constantly $P$ functions as
  appropriate. (For example, a bijection between $\{1,2\}$ and
  $\{x,y\}$ is mapped to the identity function on $\{P,Q\}$, whereas a
  bijection bewteen $\{a,b,c\}$ and $\{1,2,3\}$ is sent to the
  constantly $P$ function from $\{I,J,K\}$.)
\end{itemize}
The fact that this definition singles out the special set of labels
$\{a,b,c\}$ seems ``bogus'', and it is exactly functoriality that
prevents this sort of definition.  Indeed, this definition is not
functorial.  Though it does preserve identities, it does not preserve
composition: consider, for example, a bijection $\sigma : \{a,b,c\}
\bij \{1,2,3\}$ (it does not matter which).  Then $B (\sigma \comp
\sigma^{-1}) = id_{\{P,Q\}}$, but $B \sigma \comp B \sigma^{-1}$ is
the constantly $P$ endofunction on $\{P,Q\}$.  This example is
somewhat egregious; the reader may enjoy formulating more subtly wrong
mappings and showing why they do not satisfy functoriality.

Using the language of category theory, we can also give an equivalent, more
concise definition of species:
\begin{defn}
  \label{defn:species-cat}
  A \term{species} is a functor $F : \B \to \Set$, where $\B$ is the
  groupoid of finite sets whose morphisms are bijections, and $\Set$
  is the category of sets and (total) functions. (Even more abstractly,
  since $\B$ is self-dual, we may say that a species is a
  \term{presheaf} on $\B$, that is, a functor $\B^\op \to \Set$.)
\end{defn}

Reflecting the fact that the groupoid $\P$ of natural numbers and
finite permutations is equivalent to the groupoid $\B$, it is also
possible to define species as families of shapes, indexed not by their
labels but merely by their \emph{size}:

\begin{defn}[Species (alternate)]
  \label{defn:species-p}
  A species is a functor $F : \P \to \Set$.
\end{defn}

In this case, the set of shapes corresponding to a given size $n$ can be
thought of as precisely those labelled by the canonical label set $[n]$.

\begin{rem}
  Typically, the sets of shapes $F\ L$ are required to be
  \emph{finite}, that is, species are defined as functors into the
  category of \emph{finite} sets.  Of course, this is important if the
  goal is to \emph{count} them!  However, nothing in the present work
  hinges on this restriction, so it is simpler to drop it.

  It should be noted, however, that requiring finiteness in this way
  is actually no great restriction: requiring each \emph{particular}
  set of shapes $F\ L$ to be finite is not at all the same thing as
  requiring the \emph{entire family} of shapes, $\uplus_{n \in \N} F\
  n$, to be finite!  Typically, even in the cases that computer
  scientists care about, each individual $F\ n$ is finite but the
  entire family is not---that is, a type may have infinitely many
  inhabitants but only finitely many of a given size.
\end{rem}

\begin{rem}
  Although Definitions \ref{defn:species-set}-- \ref{defn:species-p}
  say only that a species $F$ sends a bijection $\sigma : L \bij L'$
  to a \emph{function} $F\ \sigma : F\ L \to F\ L'$, the functoriality
  of $F$ guarantees that $F\ \sigma$ is a bijection as well. In
  particular, $(F\ \sigma)^{-1} = F\ (\sigma^{-1})$, since $F\ \sigma
  \comp F\ (\sigma^{-1}) = F\ (\sigma \comp \sigma^{-1}) = F\ id =
  id$, and similarly $F\ (\sigma^{-1}) \comp F\ \sigma = id$.  So
  (given the restriction that $F\ n$ be finite) one could, and some
  authors do, define species as endofunctors $F : \B \to \B$ with no
  loss of expressivity.
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
  labelled shapes, and want to classify them by the labels that they
  use. A functor $\B \to \Set$ is then a convenient technical device
  for organizing such a classification: it describes a family of
  labelled shapes \emph{indexed by} their labels.

  Given this shift in emphasis, one might think it more natural to
  define a set of labelled shapes along with a function from shapes to
  the set of labels contained in them (indeed, down this path lies the
  notion of \term{containers} \citep{abbott_categories_2003,
    abbott_quotient, alti:cont-tcs, alti:lics09}).  Species can be
  seen as roughly dual to these shapes-to-labels mappings, giving the
  \term{fiber} of each label set.  This is parallel to the equivalence
  between the functor category $\Set^\N$ and the slice category
  $\Set/\N$~(see the discussion under functor categories in
  \pref{sec:ct-fundamentals}), though the details are more subtle
  since $\B$ is not discrete.  Both formulations have their strengths
  and weaknesses; a fuller discussion can be found in
  \pref{sec:related-work}. \todo{Make sure this reference gets filled
    in.}
\end{rem}

\subsection{The category of species}
\label{sec:category-of-species}

Recall that $[\C, \D]$ denotes the \term{functor category} whose
objects are functors $\C \to \D$ and whose morphisms are natural
transformations between functors.  We may thus consider the
\term{category of species}, $\Spe = [\B, \Set]$, where the objects are
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
    # connectOutside' (aOpts & tailGap .~ 5) "t1" "l1" -- top
    # connectOutside' (aOpts & tailGap .~ 5) "t1" "ta" -- left
    # connectOutside' aOpts "l1" "la" -- right
    # connectOutside' (aOpts & tailGap .~ 5) "ta" "la" -- bottom
    # lw 0.05
    # frame 1

aOpts = with & gap .~ 3 & headSize .~ 1.5
  \end{diagram}
  %$
    \caption{Inorder traversal is natural}
    \label{fig:species-morphism}
  \end{figure}

  It turns out that functor categories have a lot of interesting
  structure.  For example, as we will see, $[\B, \Set]$ has (at least)
  five different monoidal structures!  The rest of this chapter is
  dedicated to exploring and generalizing this structure.

\section{Generalized species}
\label{sec:constructive-species}

In many ways, $[\B, \Set]$ as the definition of species is too
specific and restrictive.  For example, one of the big motivations for
this work is to use species as a basis for computation, but ideally
this means working with shapes and labels corresponding to
\emph{types}, formalized in type theory, rather than sets.  Even
within the realm of pure mathematics, there are many extensions to the
basic theory of species (\eg multisort species, weighted species,
$\L$-species, vector species, \dots) which require moving beyond $[\B,
\Set]$ in some way.

The goal of the rest of this chapter is to examine a number of species
operations in the context of general functor categories $[\Lab,\Str]$,
in order to identify precisely what properties of $\Lab$ and $\Str$
are necessary to define each operation. That is, starting ``from
scratch'', we will build up a generic notion of species that supports
the operations we are interested in. In the process, we get a much
clearer picture of where the operations ``come from''.  In particular,
$\B$ and \Set enjoy many special properties as categories (for
example, \Set is cartesian closed, has all limits and colimits, and so
on).  It is enlightening to see precisely which of these properties
are required in which situations.

Along the way, by way of examples, we will also explore various
generalizations of species and see how they fit in this framework:
each arises from considering particular categories in place of $\B$
and $\Set$.  To keep these various functor categories straight, the
word ``species'' will be used for $[\B,\Set]$, and ``generalized
species'' (or, more specifically,
``$[\Lab,\Str]$-species''\footnote{Not to be confused with the
  generalized species of~\citet{Fiore08}, who define
  ``$(A,B)$-species'' as functors from $\B A$ (a generalization of
  $\B$) to $\hat B$, the category of presheaves $B^\op \to \Set$ over
  $B$.}) for some abstract $[\Lab, \Str]$.

\subsection{Species in type theory}
\label{sec:species-in-type-theory}

\todo{Come back to this and attack it on paper, figuring out how to
  incorporate new insights re: HoTT and CT.}
\todo{Move this up somehow, and follow it with a general description
  of the rest of the chapter, to make a nice transition into the more
  technical material on lifted monoids etc.}
One generalization that will be of particular interest is a ``port''
of species into type theory. Recall that $\BT$ denotes the
($\infty$-)groupoid whose objects are triples consisting of a type $A$, a
size $n$, and an equivalence $A \iso \Fin n$, and whose morphisms are
paths between types.  Recall also that $\Type$ denotes the category of
types and (well-typed) functions.

\begin{defn}
  A \term{constructive species} is a functor $F : \BT \to \Type$.  We
  use $\CSpe = [\BT,\Type]$ to refer to the category of constructive
  species.
\end{defn}

Another one of the major goals of this chapter is to argue that this
is an appropriate encoding of species within homotopy type theory.
Note that this cannot be directly justified by showing that
$[\B,\Set]$ and $[\BT,\Type]$ are categorically equivalent.  In fact,
that is unlikely to be true, since $\Set$ is ``too big'': there are
many sets that do not correspond to any type definable in type theory.

However, most working mathematicians do not actually make use of such
``exotic'' sets;  the constructions they care about
are typically those which can indeed be encoded in type theory.  In
order to justify $[\BT, \Type]$ as a constructive counterpart to $[\B,
\Set]$, therefore, we must look at what operations and constructions
are typically carried out on $[\B, \Set]$, and show that $[\BT,\Type]$
supports them as well.

\section{Lifted monoids: sum and Cartesian product}

Two of the simplest operations on species are the \emph{sum} and
\emph{Cartesian product}.  As we will see, these operations are
structurally analogous: the only difference is that species sum arises
from coproducts in $\Set$ (disjoint union), whereas the Cartesian
product of species arises from products in $\Set$.

\subsection{Species sum}

The \emph{sum} of two species is given by their disjoint union: an $(F
+ G)$-shape is either an $F$-shape \emph{or} a $G$-shape, together
with a tag so we can tell which (\pref{fig:sum}).

  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import SpeciesDiagrams

theDia
  = hcat' (with & sep .~ 1)
    [ struct 5 "F+G"
    , text' 1 "="
    , vcat
      [ struct 5 "F"
      , text' 0.5 "OR"
      , struct 5 "G"
      ]
      # centerY
    ]

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Species sum}
    \label{fig:sum}
  \end{figure}

\begin{defn}
  Given $F, G : \B \to \Set$, their sum $F + G : \B \to \Set$ is
  defined on objects by \[ (F + G)\ L \defeq F\ L \uplus G\ L, \]
  where $\uplus$ denotes disjoint union (coproduct) of sets, and on
  morphisms by \[ (F + G)\ \sigma \defeq F\ \sigma \uplus G\
  \sigma, \] where $\uplus$ is considered as a bifunctor in the
  evident way: $(f \uplus g)\ (\inl\ x) = \inl\ (f\ x)$ and $(f \uplus
  g)\ (\inr\ y) = \inr\ (g\ y)$.
\end{defn}

It remains to prove that the $F + G$ defined above is actually
functorial.
\begin{proof}
  The functoriality of $F + G$ follows from that of $F$, $G$, and
  $\uplus$:
  \[ (F + G)\ id = F\ id \uplus G\ id = id \uplus id = id, \]
  and
  \begin{sproof}
  \stmt{(F + G) (f \comp g)}
  \reason{=}{$+$ definition}
  \stmt{F\ (f \comp g) \uplus G\ (f \comp g)}
  \reason{=}{$F$, $G$ functors}
  \stmt{(F\ f \comp F\ g) \uplus (G\ f \comp G\ g)}
  \reason{=}{$\uplus$ functor}
  \stmt{(F\ f \uplus G\ f) \comp (F\ g \uplus G\ g)}
  \reason{=}{$+$ definition}
  \stmt{(F + G)\ f \comp (F + G)\ g.}
  \end{sproof}
\end{proof}

\begin{rem}
  More abstractly, when defining a functor with a groupoid as its
  domain (such as $F + G$ above), it suffices to specify only its
  action on objects, using an arbitrary expression composed of (co-
  and contravariant) functors.  For example, $(F + G)\ L = F\ L \uplus
  G\ L$ is defined in terms of the functors $F$, $G$, and $\uplus$.
  In that case the action of the functor on morphisms can be derived
  automatically by induction on the structure of the expression,
  simply substituting the morphism in place of covariant occurrences
  of the object, and the morphism's inverse in place of contravariant
  occurrences.  In fact, in a HoTT-based formulation of category
  theory, this is simply the transport operation; that is, given a
  groupoid $B$ and a category $C$, any function $B_0 \to C_0$ extends
  to a functor $B \to C$.

  By the same token, to define a functor with an arbitrary category
  (not necessarily a groupoid) as its domain, it suffices to define
  its action on an object using an expression containing only
  covariant occurrences of the object.

  \later{Flesh this out some more\dots ?  This could all be made formal
  and precise but the idea should be clear, and it's not necessarily
  worth it.  Could also probably find something to cite.}
\end{rem}

\begin{ex}
  $\Bin + \List$ is the species representing things which are
  \emph{either} binary trees or lists (\pref{fig:bin-plus-list}).
\end{ex}

\begin{figure}
  \centering
  \begin{diagram}[width=250]
import SpeciesDiagrams
import Data.List (permutations)

dia = (hcat' (with & sep .~ 0.5)) (map (tag 1) trees ++ map (tag 2) lists)
    # frame 0.5

trees
  = map (drawBinTreeWide . fmap labT)
  $ enumTrees [0,1 :: Int]

lists
  = map (drawList' labT)
  . permutations
  $ [0,1 :: Int]
  \end{diagram}
  \caption{$(\Bin + \List)\ 2$}
  \label{fig:bin-plus-list}
\end{figure}

\begin{ex}
  As another example, consider $\Bin + \Bin$.  It is important to bear
  in mind that $+$ yields a \emph{disjoint} or ``tagged'' union; so
  $\Bin + \Bin$ yields two copies of every binary tree
  (\pref{fig:bin-plus-bin}), and in particular it is distinct from
  $\Bin$.
\end{ex}

\begin{figure}
  \centering
  \begin{diagram}[width=250]
import SpeciesDiagrams

dia = (hcat' (with & sep .~ 0.5)) (map (tag 1) trees ++ map (tag 2) trees)
    # frame 0.5

trees
  = map (drawBinTreeWide . fmap labT)
  $ enumTrees [0,1 :: Int]  -- $
  \end{diagram}
  \caption{The species $\Bin + \Bin$}
  \label{fig:bin-plus-bin}
\end{figure}

There is also a primitive species which is an identity element for
species sum:

\begin{defn}
  The \term{zero} or \term{empty} species,
  $\Zero$, is the unique species with no shapes whatsoever.  That is,
  on objects,
    $\Zero\ L \defeq \varnothing$,
  and on morphisms $\Zero$ sends every $\sigma$ to the unique function
  $\varnothing \to \varnothing$.
\end{defn}

\begin{prop}
  $(+,\Zero)$ is a symmetric monoid on $[\B, \Set]$.
\end{prop}

\begin{proof}
  First, we must show that $+$ is a bifunctor. By definition it sends
  two functors to a functor, but this is only its action on the
  objects of $\Spe$.  We must also specify its action on morphisms,
  that is, natural transformations between species, and we must show
  that it preserves identity natural transformations and (vertical)
  composition of natural transformations.

  In this case it's enough simply to unfold definitions and follow the
  types.  Given species $F$, $F'$, $G$, and $G'$, and natural
  transformations $\phi : \nt F {F'}$ and $\psi : \nt G {G'}$, we
  should have $\phi + \psi : \nt {F+G} {F'+G'}$.  The component of
  $\phi + \psi$ at some $L \in \B$ should thus be a morphism in $\Set$
  of type $F\ L \uplus G\ L \to F'\ L \uplus G'\ L$; the only thing
  that fits the bill is $\phi_L \uplus \psi_L$.

  This nicely fits with the ``elementwise'' definition of $+$ on
  species: $(F + G)\ L = F\ L \uplus G\ L$, and likewise $(\phi +
  \psi)_L = \phi_L \uplus \psi_L$.  The action of $+$ on natural
  transformations thus reduces to the elementwise action of $\uplus$
  on their components.  From this it follows that
  \begin{itemize}
  \item $\phi + \psi$ is natural (because $\phi$ and $\psi$ are), and
  \item $+$ preserves identity and composition (because $\uplus$
    does).
  \end{itemize}
  Finally, we note that $+$ inherits the symmetry of $\uplus$.
\end{proof}

Stepping back a bit, we can see that this monoidal structure on
species arises straightforwardly from the corresponding monoidal
structure on sets: the sum of two functors is defined as the pointwise
sum of their outputs, and likewise \Zero, the identity for the sum of
species, is defined as the functor which pointwise returns
$\varnothing$, the identity for the coproduct of sets.  This general
construction will be spelled out in \pref{sec:lifting-monoids}; but
first, we turn to the formally similar operation of \emph{Cartesian
  product}.

\subsection{Cartesian/Hadamard product}
\label{sec:cartesian}

$\Set$ also has products, given by $S \times
T = \{ (s,t) \mid s \in S, t \in T \}$, with any one-element set as
the identity. (We may suppose there is some canonical
choice of one-element set, $\singleton$.)
\begin{defn}
  The \term{Cartesian} or \term{Hadamard product} of species, is defined on
  objects by $ (F \times G)\ L = F\ L \times G\ L.$
\end{defn}
\begin{rem}
  The action of $(F \times G)$ on morphisms, functoriality, \etc are
  omitted; the details are exactly parallel to the definition of
  species sum, and are presented much more generally in the next
  subsection.
\end{rem}
An $(F \times G)$-shape is both an $F$-shape \emph{and} a $G$-shape,
on \emph{the same set of labels}.  There are several ways to think
about this situation, as illustrated in \pref{fig:Cartesian-product}.
\begin{figure}
  \centering
  \begin{diagram}[width=380]
import           Data.List.Split
import           Diagrams.TwoD.Layout.Tree
import           Diagrams.TwoD.Path.Metafont

import           SpeciesDiagrams

connectAll l1 l2 n perm =
  withNames (map (l1 .>) [0 :: Int .. n-1]) $ \l1s ->
  withNames (map (l2 .>) [0 :: Int .. n-1]) $ \l2s ->
  applyAll (zipWith conn l1s (perm l2s))

conn l1 l2 = beneath (lc grey . metafont $ location l1 .- leaving unit_Y <> arriving unit_Y -. endpt (location l2))
-- $

sharedMem = vcat' (with & sep .~ 5)
  [ hcat' (with & sep .~ 3)
    [ wideTree (mkLeaf (circle 1) . ("l1" .>)) sampleBTree7 # centerY
    , drawList (mkLeaf (circle 1) . ("l2" .>)) 7 # centerY
    ] # centerXY
  , drawList (mkLeaf (square 2) . ("s" .>)) 7 # centerXY
  ]
  # connectAll "l1" "s" 7 perm1
  # connectAll "l2" "s" 7 perm2
  # centerXY # pad 1.1

perm1 = id
perm2 = concat . map reverse . chunksOf 2

asFun :: ([Int] -> [Int]) -> Int -> Int
asFun perm i = perm [0..6] !! i

numbering = hcat' (with & sep .~ 3) . map centerXY $  -- $
  [ wideTree numbered sampleBTree7 # centerX
  , drawList (numbered . asFun perm2) 7 # centerX
  ]
  where
    numbered n = mkLeaf (text (show n) # fc black <> circle 1) ()

listOnTree = wideTree (mkLeaf (circle 1)) sampleBTree7
  # cCurve 1 0 (1/4 @@@@ turn)
  # cStr   0 3
  # cCurve 3 2 (1/2 @@@@ turn)
  # cStr   2 5
  # cCurve 5 4 (1/4 @@@@ turn)
  # cCurve 4 6 (0 @@@@ turn)
  where
    cCurve :: Int -> Int -> Angle -> Diagram B R2 -> Diagram B R2
    cCurve n1 n2 a =
      connectPerim'
        (superASty & arrowShaft .~ arc (0 @@@@ turn) (1/5 @@@@ turn) # reverseTrail)
        n1 n2
        a (a ^+^ (1/4 @@@@ turn))
    cStr :: Int -> Int -> Diagram B R2 -> Diagram B R2
    cStr   = connectOutside' superASty

superASty   = with & shaftStyle %~ dashing [0.3,0.3] 0 . lw 0.2
                   & arrowHead .~ tri
                   & headSize .~ 1

treeOnList = drawList (mkLeaf (circle 1)) 7
  # top 1 0
  # top 1 5
  # top 3 2
  # bot 0 3
  # bot 5 4
  # bot 5 6
  where
    top = conn True
    bot = conn False
    conn :: Bool -> Int -> Int -> Diagram B R2 -> Diagram B R2
    conn isTop x y = connectPerim'
        (superASty & arrowShaft .~ (arc (zeroV) (3/8  @@@@ turn) # adjShaft))
        x y pAng pAng
      where
        adjShaft || (x < y) /= isTop = id
                 || otherwise        = reverseTrail
        pAng || isTop     = 1/4 @@@@ turn
             || otherwise = 3/4 @@@@ turn

super = (hcat' (with & sep .~ 5) . map centerXY) [listOnTree, treeOnList]

dia
  = frame 0.5 . centerXY . lw 0.1
  . vcat' (with & sep .~ 4) . map centerXY
  $
  [ numbering
  , sharedMem
  , super
  ]
  \end{diagram}
  %$
  \caption{Four views on the Cartesian product $\Bin \times \List$}
  \label{fig:Cartesian-product}
\end{figure}
One can think of two distinct shapes, with labels duplicated between
them. One can think of the labels as \emph{pointers} for locations in
a shared memory (this view will be explored more in
\pref{sec:sharing}).  Finally, one can think of the shapes themselves
as being superimposed.  This last view highlights the fact that
$\times$ is symmetric, but only up to isomorphism, since at root it
still consists of an \emph{ordered} pair of shapes.

There is also a species, usually called $\Bag$, which is an identity
element for Cartesian product.  Considering that we should have $(\Bag
\times G)\ L = \Bag\ L \times G\ L \iso G\ L$, the proper definition of
$\Bag$ becomes clear:

\begin{defn}
  The species of \emph{sets}, $\Bag$, is defined as the constant functor
  yielding $\singleton$, that is, $\Bag\ L = \singleton$.
\end{defn}

\begin{figure}
  \centering
  \begin{diagram}[width=100]
import SpeciesDiagrams

dia = tag 0 (decoratePath (pentagon 1) (map labT [0..4]))
    # frame 0.5
  \end{diagram}
  \caption{The unique $\Bag\ 5$ shape}
  \label{fig:bag}
\end{figure}

\begin{rem}
  $\Bag$ is called the \term{species of sets} since there is exactly
  one shape on any set of labels, which can be thought of as the set
  of labels itself, with no additional structure.  In
  fact, since all one-element sets are isomorphic, we may define
  $\Bag\ L = \{L\}$ (\pref{fig:bag}).
\end{rem}

\begin{prop}
  $(\times, \Bag)$ is a symmetric monoid on $\Spe$.
\end{prop}

\begin{proof}
  The proof is omitted, since it is almost exactly the same as the
  proof for $(+, \Zero)$; the only difference is the substitution of
  Cartesian product of sets for disjoint union.  In the next section
  we will see how to generalize both proofs.
\end{proof}

As we will see in \pref{sec:closed}, $\Spe$ is also closed with
respect to $\times$.

\subsection{Lifting monoids}
\label{sec:lifting-monoids}

Both these constructions generalize readily. In fact, any monoidal
structure on a category $\Str$ can be lifted to one on $[\Lab,\Str]$
where everything is done ``elementwise''.  The basic idea is exactly
the same as the standard Haskell type class instance
\begin{spec}
instance Monoid a => Monoid (e -> a) where
  mempty         = \ _ -> mempty
  f `mappend` g  = \a -> f a `mappend` g a
\end{spec}
but quite a bit more general.

\begin{prop} \label{prop:lift-monoid-simple} Any (strict) monoid
  $(\otimes, I)$ on $\Str$ lifts to a monoid, denoted $(\otimes^\Lab,
  I^\Lab)$, on the functor category $[\Lab,\Str]$.  In particular, $(F
  \otimes^\Lab G)\ L = F\ L \otimes G\ L$, and $I^\Lab$ is $\Delta_I$,
  the functor which is constantly $I$.  Moreover, this lifting
  preserves products, coproducts, symmetry, and distributivity.
\end{prop}

In fact, non-strict monoids lift as well; a yet more general version
of this proposition, along with a detailed proof, will be given
later. First, however, we consider some examples.

\begin{ex}
  Lifting coproducts in $\Set$ to $[\B,\Set]$ yields the $(+, \Zero)$
  structure on species, and likewise lifting products yields $(\times,
  \Bag)$. According to \pref{prop:lift-monoid-simple}, since
  $(\uplus,\varnothing)$ is a coproduct structure on $\Set$, $(+,
  \Zero)$ is likewise a coproduct structure on the category $[\B,\Set]$
  of species, and similarly $(\times, \One)$ is a categorical product.
\end{ex}

\begin{ex}
  Take $\Lab = \cat{1}$ (the trivial category with one object and one
  morphism). In this case, functors in $[\cat{1}, \Str]$ are just
  objects of $\Str$, and a lifted monoidal operation is isomorphic
  to the unlifted one.
\end{ex}

\begin{ex}
  Take $\Lab = \disc{\cat{2}}$, the discrete category with two
  objects.  Then a functor $F : \disc{\cat{2}} \to \Str$ is just a
  pair of objects in $\Str$.  For example, if $\Str = \Set$, a functor
  $\disc{\cat{2}} \to \Set$ is a pair of sets.  In this case, taking
  the lifted sum $F + G$ of two functors $F,G : \disc{\cat{2}} \to
  \Set$ corresponds to summing the pairs elementwise, that is, $(S_1,
  T_1) + (S_2, T_2) = (S_1 \uplus S_2, T_1 \uplus T_2)$.

  Recall that when $X$ is a discrete category, the functor category
  $[X,\Set]$ is equivalent to the slice category $\Set / X$.  This
  gives another way to think of a functor $\disc{\cat{2}} \to \Set$,
  namely, as a single set of elements $S$ together with a function $S
  \to \disc{\cat{2}}$ which ``tags'' each element with one of two tags
  (``left'' or ``right'', $0$ or $1$, \etc).  From this point of view,
  a lifted sum can be thought of as a tag-preserving disjoint union.

  \todo{picture?}
\end{ex}

\begin{ex}
  As an example in a similar vein, consider $\Lab = \N$, the discrete
  category with natural numbers as objects.  Functors $\N \to \Str$
  are countably infinite sequences of objects $[S_0, S_1, S_2,
  \dots]$.  One way to think of this is as a collection of
  $\Str$-objects, one for each natural number \emph{size}.  For
  example, when $\Str = \Set$, a functor $\N \to \Set$ is a sequence
  of sets $[S_0, S_1, S_2, \dots]$, where $S_i$ can be thought of as
  some collection of objects of size $i$. (This ``size'' intuition
  is actually fairly arbitrary at this point---the objects of $\N$ are
  in some sense just an arbitrary countably infinite set of labels,
  and there is no particular reason they should represent ``sizes''.
  However, the ``size'' intuition of course carries over well to
  species.)

  Again, $[\N, \Set] \cong \Set/\N$, so functors $\N \to \Set$ can
  also be thought of as a single set $S$ along with a function $S \to
  \N$ which gives the size of each element.

  Lifting a monoidal operation to countable sequences of objects
  performs a ``zip'', applying the monoidal operation between matching
  positions in the two lists: \[ [S_1, S_2, S_3, \dots] \oplus [T_1,
  T_2, T_3, \dots] = [S_1 \oplus T_1, S_2 \oplus T_2, S_3 \oplus T_3,
  \dots] \]
\end{ex}

\begin{ex}
  Up until now we have mostly considered examples with $\Str = \Set$,
  but any monoidal category will do.  $\Type$ works similarly to
  $\Set$, for example, with disjoint union of sets replaced by
  coproduct of types.  \todo{Give an example with some non-set-like
    monoidal category.}
\end{ex}

\begin{ex}
  All the previous examples have used a discrete category in place of
  $\Lab$; it is instructive to see an example with nontrivial
  morphisms involved. As the simplest nontrivial example, consider
  $\Lab = \cat{2}$, the category with two objects $0$ and $1$ and a
  single non-identity morphism $\mor 0 1$.  A functor $\cat{2} \to
  \Str$ is not just a pair of objects (as with $\Lab = \disc{\cat 2}$)
  but a pair of objects with a morphism between them: \[ S_0
  \stackrel{f}{\longrightarrow} S_1. \] Combining two such functors
  with a lifted monoidal operation combines not just the objects but
  also the morphisms: \[ (S_0 \stackrel{f}{\longrightarrow} S_1)
  \oplus (T_0 \stackrel{g}{\longrightarrow} T_1) = (S_0 \oplus T_0)
  \stackrel{f \oplus g}{\longrightarrow} (S_1 \oplus T_1) \] This is
  possible since the monoidal operation $\oplus$ is, by definition,
  required to be a bifunctor.
\end{ex}

\begin{ex}
  In $\Type$, the coproduct of two types $A$ and $B$ is given by their
  sum, $A + B$, with the void type $\TyZero$ serving as the identity.
  We may thus lift this coproduct structure to the functor category
  $[\BT, \Type]$---or indeed to any $[\Lab, \Type]$, since no
  requirements are imposed on the domain category.
\end{ex}

\begin{ex}
  Similarly, categorical products in $\Type$ are given by product
  types $A \times B$, with the unit type $\TyOne$ as the identity.
  This then lifts to products on $[\BT,\Type]$ (or, again, any
  $[\Lab,\Type]$) which serve as an analogue of Cartesian product of
  species.
\end{ex}

\todo{give some examples with other categories. $1/\Set$,
  \ie\ pointed sets with smash product? $\cat{Vect}$?}

For completeness, we now turn to a detailed and fully general
construction which shows how monoids (and many other structures of
interest) can be lifted from a category $\Str$ to a functor category
$[\Lab,\Str]$.  We must first develop some technical machinery
regarding functor categories.  In particular, we show how to lift
objects, functors, and natural transformations based on some category $\Str$
into related objects, functors, and natural transformations based on
the functor category $\Str^\Lab$.

\begin{lem} \label{lem:lift-object}
  \bay{Not sure if this is actually needed at all.}
  An object $D \in \D$ lifts to an object (\ie a functor) $D^\C \in
  \D^\C$, defined as the constant functor $\Delta_D$.
\end{lem}

\begin{lem} \label{lem:lift-functor}
  Any functor $F : \D \to \E$ lifts to a functor $F^\C : \D^\C \to
  \E^\C$ given by postcomposition with $F$.  That is, $F^\C(G) = F
  \comp G = FG$, and $F^\C(\alpha) = F\alpha$.
\end{lem}

\begin{proof}
  As usual, $F\alpha$ denotes the ``right whiskering'' of $\alpha$ by $F$,
  \[ \xymatrix{ \C \rtwocell^G_H{\alpha} & \D \ar[r]^F & \E. } \]
  $F^\C$ preserves identities since
  \[ \xymatrix{ \C \ar[r]^G & \D \ar[r]^F & \E } \]
  can be seen as both $F id_G$ and $id_{FG}$, and it preserves
  composition since
  \[ \xymatrixrowsep{1pc}
     \xymatrix{ \C \ruppertwocell{\alpha} \rlowertwocell{\beta} \ar[r]
              & \D \ar[r]^F & \E }
     =
     \vcenter{
     \xymatrix{ \C \ruppertwocell{\alpha} \ar[r] & \D \ar[r]^F & \E \\
                \C \rlowertwocell{\beta} \ar[r] & \D \ar[r]_F & \E }
     }
  \] \bay{Improve this picture with composition symbols?}
  by the interchange law for horizontal and vertical composition.
\end{proof}

Natural transformations lift in the same way:

\begin{lem} \label{lem:lift-nt} Given functors $F,G : \D \to \E$,
  any natural transformation $\alpha : \nt F G$ lifts to a natural
  transformation $\alpha^\C : \nt {F^\C} {G^\C} : \D^\C \to \E^\C$
  given by postcomposition with $\alpha$.  That is, the component of
  $\alpha^\C$ at $H :\C \to \D$ is $\alpha^\C_H = \alpha H$. Moreover,
  if $\alpha$ is an isomorphism then so is $\alpha^\C$.
\end{lem}

\begin{proof}
  Here $\alpha H$ denotes the ``left whiskering'' of $\alpha$ by $H$,
  \[ \xymatrix{ \C \ar[r]^H & \D \rtwocell^F_G{\alpha} & \E. } \]
  Note that $\alpha^\C_H$ should be a morphism $\mor {F^\C H} {G^\C
    H}$ in $\E^\C$, that is, a natural transformation $\nt {FH} {GH}$,
  so $\alpha H$ has the right type.  The naturality square for
  $\alpha^\C$ is
  \[ \xymatrix {
        FH \ar[r]^{\alpha^\C_H} \ar[d]_{F\beta}
      & GH \ar[d]^{G\beta}
     \\ FJ \ar[r]_{\alpha^\C_J}
      & GJ
     }
  \]
  which commutes by naturality of $\alpha$: at any particular $C \in
  \C$ the above diagram reduces to
  \[ \xymatrix{
        FHC \ar[r]^{\alpha_{HC}} \ar[d]_{F\beta_C}
      & GHC \ar[d]^{G\beta_C}
     \\ FJC \ar[r]_{\alpha_{JC}}
      & GJC
     }
  \]
  If $\alpha$ is an isomorphism, then $(\alpha^{-1})^\C$ is the
  inverse of $\alpha^\C$: for any $H$, $\alpha^{-1}H \cdot \alpha H =
  (\alpha^{-1} \cdot \alpha) H = id_{FH}$.
  \[ {\xymatrixcolsep{5pc} \xymatrix{ \C \ar[r]^H & \D
     \ruppertwocell^F{\mathrlap{\alpha}} \ar[r] \rlowertwocell_F{\mathrlap{\alpha^{-1}}} & \E
     }}
     =
     \xymatrix{ \C \ar[r]^H & \D \ar[r]^F & \E }
   \]
\end{proof}

\begin{thm} \label{thm:lift-expressions}
\todo{Theorem here about lifting expressions/diagrams.}
\end{thm}

We now have the necessary tools to show how monoids lift into a
functor category.

\begin{thm} \label{thm:lift-monoid}
  Any monoidal structure $(\otimes, I, \alpha, \lambda, \rho)$ on a
  category $\Str$ lifts pointwise to a monoidal structure $(\otimes^\Lab,
  I^\Lab, \alpha^\Lab, \lambda^\Lab, \rho^\Lab)$ on the functor category
  $[\Lab, \Str]$.
\end{thm}

\begin{proof}
  Immediate from Propositions \ref{lem:lift-object},
  \ref{lem:lift-functor}, and \ref{lem:lift-nt}, and
  \pref{thm:lift-expressions}.
\end{proof}

In \pref{prop:lift-monoid-simple} it was claimed that this lifting
preserves products, coproducts, symmetry, and distributivity.  We can
already show that symmetry and distributivity are preserved:

\begin{prop}
  The lifting defined in \pref{thm:lift-monoid} preserves symmetry.
\end{prop}

\begin{proof}
  Symmetry is given by a natural isomorphism $\all {X Y} {X \otimes Y
  \iso Y \otimes X}$. By \pref{thm:lift-expressions}, this lifts to a natural isomorphism
  $\all {F G} {F \otimes^\Lab G \iso G \otimes^\Lab F}$.
\end{proof}

\begin{prop}
  The lifting defined in \pref{thm:lift-monoid} preserves
  distributivity.
\end{prop}

\begin{proof}
  In any category with all products and coproducts, there is a natural
  transformation $\all {X Y Z} {X \times Y + X \times Z \to X \times
    (Y + Z)}$, given by
  $\fork{\choice{\pi_1}{\pi_1}}{\choice{\pi_2}{\pi_2}}$.  The category
  is \term{distributive} if this is an isomorphism.  Again by
  \pref{thm:lift-expressions}, such an isomorphism lifts to another natural
  isomorphism $\all {F G H} {(F \times^\Lab G) +^\Lab (F \times^\Lab H) \to F \times^\Lab (G +^\Lab
    H)}$.
\end{proof}

To show that products and coproducts are preserved requires first
showing that lifting preserves adjunctions.

\begin{lem} \label{lem:lift-adj}
  Let $F : \D \to \E$ and $G : \D \leftarrow \E$ be functors.  If $F
  \adj G$, then $F^\C \adj G^\C$.
\end{lem}

\begin{proof}
  Since $F \adj G$, assume we have $\gamma_{A,B} : \E(FA, B) \cong
  \D(A, GB)$.  To show $F^\C \adj G^\C$, we must define a natural
  isomorphism $\gamma^\C_{H,J} : \E^\C(F \comp H, J) \cong \D^\C(H, G
  \comp J)$.  Given $\phi \in \E^\C(FH,J)$, that is, $\phi : \nt {FH}
  J : \C \to \E$, and an object $C \in \C$, define \[
  \gamma^\C_{H,J}(\phi)_C = \gamma_{HC,JC}(\phi_C). \]  Note that
  $\gamma_{HC,JC} : \E(FHC,JC) \cong \D(HC,GJC)$, so it sends $\phi_C
  : FHC \to JC$ to a morphism $HC \to GJC$, as required.

  From the fact that $\gamma$ is an isomorphism it thus follows
  directly that $\gamma^\C$ is an isomorphism as well.  Naturality of
  $\gamma^\C$ also follows straightforwardly from naturality of
  $\gamma$. \bay{Weasel words!  Should try to actually prove this.
    Intuitively I believe it really is ``straightforward'' but getting
    the details straight is tricky.  Is this just an application of
    the previous lemma about lifting natural transformations?  It
    might be, but if so it would require a bit of unfolding to see it.}
\end{proof}

\begin{prop}
  The lifting defined in \pref{thm:lift-monoid} preserves coproducts
  and products.
\end{prop}

\begin{proof}
  Consider a category $\Str$ with coproducts, given by a bifunctor $+
  : \Str \times \Str \to \Str$.  Lifting yields a functor $+^\Lab :
  (\Str \times \Str)^\Lab \to \Str^\Lab$.  Note that $(\Str \times
  \Str)^\Lab \cong \Str^\Lab \times \Str^\Lab$, so we may consider
  $+^\Lab$ as a bifunctor $\Str^\Lab \times \Str^\Lab \to \Str^\Lab$.

  There is \latin{a priori} no guarantee that $+^\Lab$ has any special
  properties, but it turns out that $+^\Lab$ is a coproduct on
  $\Str^\Lab$, which we demonstrate as follows.  The key idea is that
  the property of being a coproduct can be described in terms of an
  adjunction: in particular, $+$ is a coproduct if and only if it is
  left adjoint to the diagonal functor $\Delta : \Str \to \Str \times
  \Str$. \bay{Is it worth proving this?  In an appendix?  It's fairly
    standard.}  Since lifting preserves adjunctions
  (\pref{lem:lift-adj}), we must have $+^\Lab \adj \Delta^\Lab$. But
  note we have $\Delta^\Lab : \Str^\Lab \to (\Str \times \Str)^\Lab
  \cong \Str^\Lab \times \Str^\Lab$, with $\Delta^\Lab (F) = \Delta
  \comp F \cong (F,F)$, so in fact $\Delta^\Lab$ is the diagonal
  functor on $\Str^\Lab$.  Hence $+^\Lab$, being left adjoint to the
  diagonal functor, is indeed a coproduct on $\Str^\Lab$.

  Of course, this dualizes to products as well, which are
  characterized by being right adjoint to the diagonal functor.
\end{proof}

\section{Day convolution: partitional and arithmetic product}
\label{sec:day}

There is another notion of product for species, the \term{partitional}
or \term{Cauchy} product.  It it is the partitional product, rather
than Cartesian product, which corresponds to the product of generating
functions and which gives rise to the usual notion of product on
algebraic data types.  For these reasons, partitional product is often
simply referred to as ``product'', without any modifier.

There is also another less well-known product, \term{arithmetic
  product} \citep{Maia2008arithmetic}, which can be thought of as a
symmetric form of composition.  These two products arise in an
analogous way, via a categorical construction known as \emph{Day
  convolution}.

\subsection{Partitional/Cauchy product}
\label{sec:partitional-product}


The partitional product $F \sprod G$ of two species $F$ and $G$
consists of paired $F$- and $G$-shapes, as with the Cartesian product,
but with the labels \emph{partitioned} between the two shapes instead
of replicated (\pref{fig:product}).

  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import           Data.List.Split
import           Diagrams.TwoD.Layout.Tree
import           Diagrams.TwoD.Path.Metafont

import           SpeciesDiagrams

connectAll l1 l2 n =
  withNames (map (l1 .>) [0 :: Int .. n-1]) $ \l1s ->
  withNames (map (l2 .>) [0 :: Int .. n-1]) $ \l2s ->
  applyAll (zipWith conn l1s l2s)

conn l1 l2 = beneath (lc grey . metafont $ location l1 .- leaving unit_Y <> arriving unit_Y -. endpt (location l2))
-- $

sharedMem = vcat' (with & sep .~ 5)
  [ hcat' (with & sep .~ 3)
    [ wideTree (mkLeaf (circle 1) . ("l" .>) . (part1!!)) sampleBTree5 # centerY
    , drawList (mkLeaf (circle 1) . ("l" .>) . (part2!!)) 3 # centerY
    ] # centerXY
  , drawList (mkLeaf (square 2) . ("s" .>)) 8 # centerXY
  ]
  # connectAll "l" "s" 8
  # centerXY # pad 1.1

perm1 = id
perm2 = id

part1, part2 :: [Int]
part1 = [3,0,1,2,6]
part2 = [5,4,7]

numbering = hcat' (with & sep .~ 3) . map centerXY $  -- $
  [ wideTree (numbered . (part1!!)) sampleBTree5 # centerX
  , drawList (numbered . (part2!!)) 3 # centerX
  ]
  where
    numbered n = mkLeaf (text (show n) # fc black <> circle 1) ()

dia
  = frame 0.5 . centerXY . lw 0.1
  . vcat' (with & sep .~ 4) . map centerXY
  $
  [ numbering
  , sharedMem
  ]
    \end{diagram}
    %$

%     \begin{diagram}[width=250]
% import SpeciesDiagrams

% theDia
%   = hcat' (with & sep .~ 1)
%     [ struct 5 "F•G"
%     , text' 1 "="
%     , vcat' (with & sep .~ 0.2)
%       [ struct 2 "F"
%       , struct 3 "G"
%       ]
%       # centerY
%     ]

% dia = theDia # centerXY # pad 1.1
%     \end{diagram}
    \caption{Partitional species product}
    \label{fig:product}
  \end{figure}

\begin{defn}
  The \term{partitional} or \term{Cauchy product} of two species $F$
  and $G$ is the functor defined on objects by \[ (F \sprod G)\ L =
  \biguplus_{L_F,L_G \partition L} F\ L_F \times G\ L_G \] where
  $\biguplus$ denotes an indexed coproduct of sets, and $L_F,L_G
  \partition L$ denotes that $L_F$ and $L_G$ constitute a partition of
  $L$, (\ie $L_F \union L_G = L$ and $L_F \intersect L_G =
  \varnothing$).

  On morphisms, $(F \cdot G)\ \sigma$ is the function which sends \[
  (L_F,L_G, x, y) \mapsto (\sigma\ L_F, \sigma\ L_G, F\ (\sigma
  \vert_{L_F})\ x, G\ (\sigma \vert_{L_G})\ y), \] where $L_F,L_G
  \partition L$, $x \in F\ L_F$, and $y \in G\ L_G$.
\end{defn}

The identity for partitional product should evidently be some species
$\One$ such that \[ (\One \cdot G)\ L = \left(\biguplus_{L_F,L_G
    \partition L} \One\ L_F \times G\ L_G \right) \iso G\ L. \] The only
way for this isomorphism to hold naturally in $L$ is if $\One\
\varnothing = \singleton$ (yielding a summand of $G\ L$ when
$\varnothing,L \partition L$) and $\One\ L_F = \varnothing$ for all other $L_F$
(cancelling all the other summands).

\begin{defn}
  The \term{unit species}, $\One$, is defined by
  \[ \One\ L =
  \begin{cases}
    \singleton & L = \varnothing \\
    \varnothing & \text{otherwise}.
  \end{cases}
  \]
\end{defn}

\begin{rem}
  The unit species denotes a sort of ``trivial'' or ``leaf'' structure
  containing no labels.  Intuitively, it corresponds to a Haskell type
  like |data Unit a = Unit|.
\end{rem}

\todo{Examples.  Pairs, lists, trees, $X \cdot E$.}

\subsection{Arithmetic product}
\label{sec:arithmetic-product}

\newcommand{\aprod}{\boxtimes}

There is another, more recently discovered monoidal structre on
species known as \emph{arithmetic product} \citep{Maia2008arithmetic}.
The arithmetic product of species $F$ and $G$, written $F \aprod G$,
can intuitively be thought of as an ``$F$-assembly of cloned
$G$-shapes'', that is, an $F$-shape containing multiple copies of a
\emph{single} $G$-shape.  Unlike the usual notion of composition
(\pref{sec:composition}), where the $F$-shape would be allowed to
contain many different $G$-shapes, this notion is symmetric: an
$F$-assembly of cloned $G$-shapes is isomorphic to a $G$-assembly of
cloned $F$-shapes.  Another intuitive way to think of the arithmetic
product, which points out the symmetry more clearly, is to think of a
rectangular matrix of labels, together with an $F$-shape labelled by
the rows of the grid, and a $G$-shape labelled by the
columns. \pref{fig:arithmetic-product} illustrates these intuitions
with the arithmetic product of a tree and a list.

\begin{figure}
  \centering
  \begin{diagram}[width=250]
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

grays  = map (\k -> blend k black white) [0, 0.2, 0.8, 1, 0.5]
shapes = [circle 0.2, triangle 0.4, square 0.4]

grid = vcat' (with & sep .~ 0.5)
  [ tree3 (\n -> mkLeaf (circle 0.4 # fc (grays !! n)) n) # translateX 3.4
  , hcat' (with & sep .~ 0.5)
    [ list2 (\n -> (mkLeaf ((shapes !! n) # rotateBy (1/4) <> circle 0.4) n)) # rotateBy (3/4)
    , theGrid
    ]
  ]
  where
    theGrid :: Diagram B R2
    theGrid = vcat . map hcat $
      [ [ (shapes !! i) # fc (grays !! j) <> square 1
        || j <- [1,0,3,2,4]
        ]
      || i <- [0..2]
      ]

assembly1 =
  tree3 (mkLeaf $ enrect (list2 (mkLeaf (circle 0.4)) # centerX # scale 0.5))

assembly2 = hcat' (with & sep .~ 0.4)
  (map (fc white . enrect . (mkLeaf (tree3 (mkLeaf (circle 0.4)) # centerXY # scale 0.5))) [0 .. 2 :: Int])
  <>
  hrule 7 # alignL

enrect d = d <> roundedRect (width d + 0.2) (height d + 0.2) 0.2

tree3 nd
  = maybe mempty (renderTree nd (~~))
  . uniqueXLayout 1 1
  $ sampleBTree5

list2 nd = hcat' (with & sep .~ 1 & catMethod .~ Distrib)
  (map nd [0 :: Int .. 2])
  <>
  hrule 2 # alignL
  where
    aSty = with & arrowHead .~ noHead

dia = frame 0.2 . centerXY . vcat' (with & sep .~ 2) . map centerXY $
  [ assembly1 # scale 1.3
  , assembly2
  , grid
  ]
  # lw 0.03
  \end{diagram}
  \caption{Three views on arithmetic product of species}
  \label{fig:arithmetic-product}
\end{figure}

A more formal definition requires the notion of a \term{rectangle} on
a set~\citep{Maia2008arithmetic, XXX}, which plays a role similar to
that of set partition in the definition of partitional product. (So
perhaps arithmetic product ought to be called \emph{rectangular
  product}.)  In particular, whereas a binary partition of a set $L$
gives a canonical decomposition of $L$ into a sum, a rectangle on $L$
gives a canonical decomposition into a product.  The basic idea is to
partition $L$ in two different ways, and require the partitions to act
like the ``rows'' and ``columns'' of a rectangular matrix.

\begin{defn}[\citet{Maia2008arithmetic}]
  \label{defn:rectangle}
  A \term{rectangle} on a set $L$ is a pair $(\pi, \tau)$ of families
  of subsets of $L$, such that
  \begin{itemize}
  \item $\pi \partition L$ and $\tau \partition L$, and
  \item $||X \intersect Y|| = 1$, for all $X \in \pi$, $Y \in \tau$.
  \end{itemize}
  Here, $\pi \partition L$ denotes that $\pi$ is a partition of $L$
  into any number of nonempty parts, that is, the elements of $\pi$
  are nonempty, pairwise disjoint, and have $L$ as their union.  We
  write $\pi,\tau \rectangle L$ to denote that $(\pi,\tau)$ constitute
  a rectangle on $L$, and call $\pi$ and $\tau$ the \term{sides} of
  the rectangle.
\end{defn}

We can now formally define arithmetic product as follows:

\begin{defn}
  The \term{arithmetic product} $F \aprod G$ of two species $F$ and
  $G$ is the species defined on objects by \[ (F \aprod G)\ L =
  \biguplus_{L_F, L_G \rectangle L} F\ L_F \times G\ L_G. \]

  $(F \aprod G)$ lifts bijections $\sigma : L \bij L'$ to functions
  $(F \aprod G)\ L \to (F \aprod G)\ L'$ as follows: \[ (F \aprod G)\
  \sigma\ (L_F, L_G, f, g) = (\powerset(\sigma)\ L_F,
  \powerset(\sigma)\ L_G, F\ \powerset(\sigma)\ L_F, G\
  \powerset(\sigma)\ L_G), \] where $\powerset(\sigma) : \powerset(L)
  \bij \powerset(L')$ denotes the functorial lifting of $\sigma$ to a
  bijection between subsets of $L$ and $L'$.
\end{defn}

\begin{rem}
  The similarity of this definition to the definition of partitional
  product should be apparent: the only difference is that we have
  substituted rectangles ($L_F,L_G \rectangle L$) for partitions
  ($L_F,L_G \partition L$).
\end{rem}

An identity element for arithmetic product should be some species $\X$
such that \[ (\X \aprod G)\ L = \left(\biguplus_{L_\X, L_G \rectangle L} \X\
L_\X \times G\ L_G\right) \cong G\ L. \] Thus we want $\X\ L_\X = \singleton$
when $L_\X, L \rectangle L$ and $\X\ L_\X = \varnothing$ otherwise.
Consider $L_\X, L \rectangle L$.  Of course, $L$ does not have the
right type to be one side of a rectangle on itself, but it is
isomorphic to the set of all singleton subsets of itself, which does.
The definition of a rectangle now requires every element of $L_\X$ to
have a nontrivial intersection with every singleton subset of $L$
(such intersections will automatically have size $1$).  Therefore
$L_\X$ has only one element, namely, $L$ itself, and is isomorphic to
$\singleton$.  Intuitively, $\singleton, L \rectangle L$ corresponds
to the fact that we can always make a $1 \times n$ rectangle on any
set of size $n$, that is, any number $n$ can be ``factored'' as $1
\times n$.

This leads to the following definition:
\begin{defn}
  The \term{singleton species}, $\X$, is defined by \[ \X\ L =
  \begin{cases}
    \singleton & ||L|| = 1 \\
    \varnothing & \text{otherwise}.
  \end{cases}
  \]
\end{defn}

\todo{More intuitive ideas about $\X$.}

\todo{Examples. $\List \aprod \List$.}

\subsection{Day convolution}
\label{sec:day-convolution}

Just as sum and Cartesian product were seen to arise from the same
construction applied to different monoids, both partitional and
arithmetic product arise from \emph{Day convolution}, applied to
different monoidal structures on $\B$.

The essential idea, first described by Brian
Day~\cite{day-convolution}, is to construct a monoidal structure on a
functor category $[\Lab^\op, \Str]$ based primarily on a monoidal
structure on the \emph{domain} category $\Lab$.  In particular, Day
convolution requires
\begin{itemize}
\item a monoidal structure $\oplus$ on the domain $\Lab$;
\item that $\Lab$ be \emph{enriched over} $\Str$, \ie\ for any two
  objects $L_F,L_G \in \Lab$ there is a hom-object $\Lab(L_F,L_G) \in
  \Str$ rather than a set, with approrpiate coherent notions of
  composition and identity morphisms;
\item a symmetric monoidal structure $\otimes$ on the codomain $\Str$;
\item that $\Str$ be cocomplete, and in particular
  have coends over $\Lab$.
\end{itemize}

Note that any monoidal structures will do; in particular there is no
requirement that $\oplus$ be ``sum-like'' or $\otimes$
``product-like'', though that is indeed the case for partitional
product.

\begin{defn}
  Given the above conditions, the Day convolution product of $F, G \in
  [\Lab^\op, \Str]$ is given by the coend \[ F \oast G = \coend{L_F, L_G}
  F\ L_F \otimes G\ L_G \otimes \Lab(-, L_F \oplus L_G). \]
\end{defn}

\begin{rem}
  Since groupoids are self-dual, we may ignore the $-^\op$ in the
  common case that $\Lab$ is a groupoid.
\end{rem}

\begin{rem}
  Note that there are only covariant occurrences of $L_F$ and $L_G$ in
  the above definition, which simplifies the definition of the
  coend. \todo{flesh out}
\end{rem}

This operation is associative, and has as a unit $j(I)$ where $I$ is
the unit for $\oplus$ and $j : \Lab \to [\Lab^{\text{op}}, \Str]$ is the Yoneda
embedding, that is, $j(L) = \Lab(-,L)$.

\begin{ex}
  Let's begin by looking at the traditional setting of $\Lab = \B$ and
  $\Str = \Set$.  As noted in~\pref{sec:groupoids}, $\B$ has a
  monoidal structure given by disjoint union of finite sets. $\B$ is
  indeed enriched over $\Set$, which is also cocomplete and has a
  symmetric monoidal structure given by Cartesian product.

  Specializing the definition to this case, we obtain
  \begin{align*}
    (F \cdot G)(L) &= \coend{L_F, L_G} F\ L_F \times G\ L_G \times
    (L \bij L_F \uplus L_G).
  \end{align*}
  Let $R \defeq \biguplus_{L_F, L_G} F\ L_F \times G\ L_G \times (L
  \bij L_F \uplus L_G)$; elements of $R$ look like quintuples $(L_F, L_G,
  f, g, i)$, where $f \in F\ L_F$, $g \in G\ L_G$, and $i : L \bij L_F
  \uplus L_G$.  Then, as we have seen, the coend can be expressed as a
  quotient $\quotient{R}{\sim}$, where every pair of bijections
  $(\sigma_F : L_F \bij L_F', \sigma_G : L_G \bij L_G')$ induces an
  equivalence of the form \[ (L_F, L_G, f, g, i) \sim (L_F',\; L_G',\;
  F\ \sigma_F\ f,\; G\ \sigma_G\ g,\; i \then (\sigma_F \uplus
  \sigma_G)). \] That is, $f \in F\ L_F$ is sent to $F\ \sigma_F\ f$
  (the relabelling of $f$ by $\sigma_F$); $g \in G\ L_G$ is sent to
  $G\ \sigma_G\ g$; and $i : L \bij L_F \uplus L_G$ is sent to $i ;
  (\sigma_F \uplus \sigma_G) : L \bij L_F' \uplus L_G'$.

  When are two elements of $R$ inequivalent, that is, when can we be
  certain two elements of $R$ are not related by a pair of
  relabellings?  Two elements $(L_{F1}, L_{G2}, f_1, g_1, i_1)$ and
  $(L_{F2},L_{G2},f_2,g_2,i_2)$ of $R$ are unrelated if and only if
  \begin{itemize}
  \item $f_1$ and $f_2$ are unrelated by any relabelling, or
  \item $g_1$ and $g_2$ are unrelated by any relabelling, or
  \item $L_{F1}$ and $L_{G1}$ ``sit inside'' $L$ differently than $L_{F2}$ and
    $L_{G2}$ in $L_2$, that is, $i_1^{-1}(L_{F1}) \neq i_2^{-1}(L_{F2})$.
  \end{itemize}
  The first two bullets are immediate; the third follows since a pair
  of relabellings can permute the elements of $L_F$ and $L_G$
  arbitrarily, or replace $L_F$ and $L_G$ with any other sets of the
  same size, but relabelling alone can never change which elements of
  $L$ correspond to $L_F$ and which to $L_G$, since that is preserved
  by composition with a coproduct bijection $\sigma_F \uplus \sigma_G$.

  Therefore, all the equivalence classes of $\quotient{R}{\sim}$ can
  be represented canonically by a partition of $L$ into two disjoint
  subsets, along with a choice of $F$ and $G$ structures, giving rise
  to the earlier definition: \[ (F \sprod G)\ L =
  \biguplus_{L_F,L_G \partition L} F\ L_F \times G\ L_G. \]

  Also, in this case, the identity element is $j(I) = j(\varnothing) =
  \B(-,\varnothing)$, that is, the species which takes as input a
  label set $L$ and constructs the set of bijections between $L$ and
  the empty set.  Clearly there is exactly one such bijection when $L
  = \varnothing$, and none otherwise: as expected, this is the species
  $\One$ defined in the previous section.
\end{ex}

\begin{ex}
  Although $\B$ and $\P$ are equivalent, it is still instructive to
  work out the general definition in the case of $\P$, particulary
  because, as we have seen, proving $\B \cong \P$ requires the axiom
  of choice.

  We find that $\P$ has not just one but \emph{many} monoidal
  structures corresponding to disjoint union.  The action of such a
  monoid on objects of $\P$ is clear: the natural numbers $m$ and $n$
  are sent to their sum $m + n$.  For the action on morphisms, we are
  given $\sigma : \perm{(\Fin m)}$ and $\tau : \perm{(\Fin n)}$ and
  have to produce some $\perm{(\Fin (m+n))}$.  However, there are many
  ways to do this---in fact, one for every choice of \[ \varphi : \Fin
  m \uplus \Fin n \bij \Fin (m + n), \] which specifies how to embed
  $\{0, \dots, m-1\}$ and $\{0, \dots, n-1\}$ into $\{0, \dots,
  m+n-1\}$.  \todo{picture}

  Given such a $\varphi$, we may construct \[ \Fin (m+n)
  \stackrel{\varphi^{-1}}{\bij} \Fin m \uplus \Fin n \stackrel{\sigma
    \uplus \tau}{\bij} \Fin m \uplus \Fin n \stackrel{\varphi}{\bij}
  \Fin (m+n). \] Conversely, given some functorial $q : \perm{(\Fin
    m)} \to \perm{(\Fin n)} \to \perm{(\Fin (m+n))}$, we can recover
  $\varphi$ by passing some transitive bijection (say, $\lam{i}{(i +
    1) \bmod m}$) as the first argument to $q$, and $\id$ as the
  second---the resulting permutation will increment those indices
  which are matched with $\Fin m$, and fix those matched with $\Fin
  n$. \todo{picture?}

  The choice of $\varphi$ does not matter up to isomorphism---hence
  this is where the axiom of choice can be invoked, in order to define
  a single, canonical monoid structure on $\P$.  However, it is
  preferable to simply retain a plethora of monoidal structures, each
  indexed by a bijection $\varphi : \Fin m \uplus \Fin n \bij \Fin
  (m+n)$ and denoted $+_\varphi$.

  We may now instantiate the definition of Day convolution,
  obtaining \[ (F \sprod G)_n = \coend{n_F, n_G} F_{n_F} \times G_{n_G}
  \times (\Fin n \bij \Fin (n_F + n_G)). \] Again, letting $R \defeq
  \biguplus_{n_F, n_G} F_{n_F} \times G_{n_G} \times (\Fin n \bij \Fin
  (n_F + n_G))$, the coend is equivalent to $\quotient{R}{\sim}$,
  where \[ (n_F, n_G, f, g, i) \sim (n_F, n_G,\;F\ \sigma_F\ f,\;G\
  \sigma_G\ g,\;i \then (\sigma_F +_\varphi \sigma_G)) \] for any
  $\sigma_F : \perm{(\Fin n_F)}$ and $\sigma_G : \perm{(\Fin
    n_G)}$. \todo{Finish}
\end{ex}

\begin{ex}
  There is another monoidal structure on $\B$ corresponding to the
  Cartesian product of sets. If we instantiate the framework of Day
  convolution with this product-like monoidal structure---but
  keep everything else the same, in particular continuing to use
  products on $\Set$---we obtain the arithmetic product.

  \todo{Flesh out.  Derive $\X$ categorically.}
\end{ex}

\begin{ex}
  \todo{Work out details here.  Do arithmetic product but in
    $[\P,\Set]$.}  Let's examine this in detail in the case of
  $[\P,\Set]$.  The monoidal structure on $\P$ is defined on objects
  as $m \otimes n = mn$.  On morphisms, given $f : \fin m \bij \fin m$
  and $g : \fin n \bij \fin n$, we have $f \otimes g : \fin{mn} \bij
  \fin{mn}$ defined by \todo{finish}.

  Instantiating the definition of Day convolution yields
  \begin{align*}
    (F \boxtimes G)\ n &= \coend{n_F,n_G} F\ n_F \times G\ n_G \times
    \P(n, n_Fn_G) \\
    &= \coend{n_F,n_G} F\ n_F \times G\ n_G \times (\fin n \bij \fin
    {n_F n_G}) \\
    &= ? \\
    &= \biguplus_{d \mid n} F\ d \times G\ (n/d)
  \end{align*}
\end{ex}

\begin{ex}
  We now verify that $\BT$ and $\Type$ have the right properties, so
  that partitional and arithmetic product are well-defined on
  $[\BT,\Type]$-species.
  \begin{itemize}
  \item Like $\B$, there are monoidal structures on $\BT$
    corresponding to the coproduct and product of types. As with $\P$,
    however, there are many monoidal structures corresponding to
    each. In contrast to $\P$, however, the choice concerns what to do
    with \emph{objects}.  A monoidal operation on $\BT$ does not
    simply combine two types into their coproduct or product, but also
    combines their finiteness evidence into corresponding evidence for
    the combined type, via some function $\oplus_{\Fin{}} : \IsFinite
    A \to \IsFinite B \to \IsFinite (A \oplus B)$.  Any such function,
    in combination with a monoid $\oplus$ on $\Type$, gives rise to a
    valid monoid on $\FinType$, since \todo{finish}
  \item $\BT$ is indeed enriched over $\Type$, since the class of
    arrows between $(A,m,i)$ and $(B,n,j)$ is given by the type $A
    \iso B$.
  \item We have already seen that there is a symmetric monoidal
    structure on $\Type$ given by the product of types.
  \item The last condition is the most interesting: we need to say
    what a coend over $\BT$ is in $\Type$. In fact, in this case a
    coend is just a $\Sigma$-type!  This is because the morphisms in
    $\BT$ are paths, and hence the required identifications between
    inhabitants of the $\Sigma$-type are already present---they are
    induced by transport of paths in $\BT$. \todo{flesh out more}
  \end{itemize}

  Given $F,G \in [\BT,\Type]$, and picking some particular sum-like
  monoid $\oplus$ on $\BT$, we can instantiate the definition
  of Day convolution to get
  \[ (F \cdot G)\ L = \sum_{L_F, L_G} F\ L_F \times G\ L_G \times
  (\mor L {L_F \oplus L_G}). \] \todo{Flesh out. Need some notation
    for the underlying sets of $L$, $L_F$, and $L_G$.  Particular
    monoid chosen doesn't actually matter here.}
\end{ex}

\begin{ex}
  Try it with $(\otimes, \oplus)$ and $(\oplus, \oplus)$.
\end{ex}

\section{Composition}
\label{sec:composition}

We have already seen that arithmetic product can be thought of as a
restricted sort of composition, where an $F$-structure contains
$G$-structures all of the same shape (or vice versa).  More generally,
there is an unrestricted version of composition, where $(F \comp
G)$-shapes consist of $F$-shapes containing \emph{arbitrary}
$G$-shapes.  In more detail, to create an $(F \comp G)$-shape over a
given set of labels $L$, we first \emph{partition} $L$ into some
number of nonempty subsets; create a $G$-shape over each subset; then
create an $F$-shape over the resulting set of $G$-shapes.

Formally,
\[ (F \comp G)\ L = \sum_{\pi \partition L} F\ \pi \times \prod_{p \in
  \pi} G\ p. \] \pref{fig:composition} shows an abstract
representation of the definition.

%   \begin{figure}
%     \centering
%     \begin{diagram}[width=250]
% import SpeciesDiagrams

% theDia = struct 6 "F∘G"
%          ||||||
%          strutX 1
%          ||||||
%          txt "="
%          ||||||
%          strutX 1
%          ||||||
%          drawSpT
%          ( nd (txt "F")
%            [ struct' 2 "G"
%            , struct' 3 "G"
%            , struct' 1 "G"
%            ]
%          )

% dia = theDia # centerXY # pad 1.1
%     \end{diagram}
%     \caption{Species composition}
%     \label{fig:composition}
%   \end{figure}

One can see that in addition to being the identity for $\aprod$, $\X$
is the (two-sided) identity for $\comp$ as well, since an $F$-shape
containing singletons and a singleton $F$-shape are both isomorphic to
an $F$-shape.

\begin{ex}
  As an example, we may define the species $\Par$ of set partitions
  by \[ \Par = \E \comp \E_+.\] \todo{picture + more commentary}
\end{ex}

\begin{ex}
  The species $\Sp{R}$ of nonempty $n$-ary (``rose'') trees, with data
  stored at internal nodes, may be defined by the recursive species
  equation \[ \Sp{R} = \X \sprod (\L \comp \Sp{R}). \] \todo{picture +
    more commentary}
\end{ex}

\begin{ex}
  The species $\Sp{P}$ of \emph{perfect trees}, with data stored in
  the leaves, may be defined by \[ \Sp{P} = \X + (\Sp{P} \comp
  \X^2). \] \todo{picture + more commentary}
\end{ex}

\subsection{Generalized composition}
\label{sec:generalized-composition}

We first show how to carry out the definition of composition in $[\B,
\Set]$ more abstractly, and then discuss how it may be generalized to
other functor categories $[\Lab, \Str]$.
\citet{street2012monoidal} gives the following abstract
definition of composition:
\[ (F \comp G)\ L = \coend{K} F\ K \times G^{\size K}\ L, \]
where $G^{n} = \underbrace{G \bullet \dots \bullet G}_n$ is
the $n$-fold partitional product of $G$.  Intuitively, this
corresponds to a top-level $F$-shape on labels drawn from the
``internal'' label set $K$, paired with $\size K$-many $G$-shapes,
with the labels from $L$ partitioned among all the $G$-shapes.  The
coend ensures that the precise choice of $K$ ``does not matter'' up to
isomorphism.

However, this definition is puzzling from a constructive point of
view, since it is would seem that $G^{\size K}$ retains no information
about which element of $K$ corresponds to which $G$-shape in the
product.  The problem boils down, again, to the use of the axiom of
choice.  For each finite set $K$ we may choose some ordering
$K \bij \fin{\size K}$; this ordering then dictates how to match up
the elements of $K$ with the $G$-shapes in the product $G^{\size K}$.

Our goal will be to instead define $G^K$, a ``$K$-indexed partitional
product'' of $G$-shapes, where each $G$-shape corresponds, by
construction, to an element of $K$.

As a warm-up, consider first the situation in $\Set$.  We can
represent a $K$-indexed collection of sets by a functor $K \to \Set$
(where $L$ is regarded as a discrete category). \todo{working here}

be regarded as an
$L$-indexed tuple of sets; \eg in the case $L = \disc{\cat{2}}$, the
discrete category on two objects, a functor $\disc{\cat{2}} \to \Set$
is just an ordered pair of sets. $\Delta_L (X)$ is the $L$-indexed
tuple containing identical copies of $X$.

The fact that $\Set$ has all limits and colimits is equivalent to
saying that for any category $J$, the diagonal functor $\Delta_J :
\Set \to \Set^J$ always has (respectively) a right and left
adjoint~\cite{wikipedia on limits}. \todo{Look up Taylor, Ex 7.3.7
  p.387, 9.1.7 p.474.}  In the particular case of a discrete category
$L$, we call these adjoints $\Pi^L$ and $\Sigma^L$: \[ \Sigma^L \adj
\Delta_L \adj \Pi^L. \] In particular, $\Sigma^L : \Set^L \to \Set$
constructs $L$-indexed coproducts, and $\Pi^L$ indexed products. (In
the special case $L = \cat{2}$, $\Sigma^2$ and $\Pi^2$ resolve to the
familiar notions of binary disjoint union and Cartesian product of
sets, respectively.)  We often omit the superscripts, writing simply
$\Sigma$ and $\Pi$ when $L$ is clear from the context.

As noted previously, $\B$ does not have products or coproducts, so we
cannot directly define $\Sigma$ or $\Pi$ as adjoints in $\B$.
However, we may take the restriction of $\Sigma : \Set^L \to \Set$ to
$\Sigma : \B^L \to \B$ (and likewise for $\Pi$), since $\B$ is a
subcategory of $\Set$ and disjoint union (respectively product)
preserves finiteness.

We now define a general notion of indexed species product. For a
species $F \in [\B,\Set]$ and $K \in \B$ a finite set, $F^K \in
[\B,\Set]$ represents the $\size K$-fold partitional product of $F$,
indexed by the elements of $K$: \todo{picture?} \[ F^K\ L = \coend{P
  \in [K,\B]} \B(\Sigma P, L) \times \Pi (F \comp P). \] Note that $K$
is regarded as a discrete category, so $P \in \B^K$ is a $K$-indexed
collection of finite sets.  $\B(\Sigma P, L)$, a bijection between the
coproduct of $P$ and $L$, witnesses the fact that $P$ represents a
partition of $L$; the coend means there is only one shape per
fundamentally distinct partition. The composite $F \comp P =
\xymatrix{K \ar[r]^P & \B \ar[r]^F & \Set}$ is a $K$-indexed
collection of $F$-structures, one on each finite set of labels in $P$;
the $\Pi$ constructs their product.

\todo{Note this is functorial in $K$, i.e. $F^- : \B \to [\B,\Set]$ is
a functor.}

Finally, the composite $F \comp G$ is defined by
\[ (F \comp G)\ L = \coend{K} F\ K \times G^K\ L, \] \ie an $(F \comp
G)$-shape on $L$ is an $F$-shape on some label set $K$ paired with a $K$-indexed
product of $G$-shapes on $L$; the coend \todo{finish}. \todo{picture}

\todo{Prove it is associative?}
\todo{Distributes over sum and product?}

\section{Closed monoidal structures and elimination}
\label{sec:closed}

\paragraph{Cartesian closed} If $\Lab$ is locally small and $\Str$ is
complete and Cartesian closed, then $[\Lab,\Str]$ is also complete and
Cartesian closed. \todo{cite
  \url{mathoverflow.net/questions/104152/exponentials-in-functor-categories/104178\#104178},
  also check locally small thing?  Jacques asked it on MO?}  In
particular the exponential of $F,G : \Lab \to \Str$ is given by \[ G^F
(L) = \eend{K \in \Lab} \prod_{\Lab(L,K)} G(K)^{F(K)}. \] For example,
$\B$, $\P$, $\BT$, and $\PT$ are all locally small, and $\Set$ and
$\Type$ are complete and Cartesian closed, so $[\B,\Set]$, $[\P,\Set]$,
$[\BT,\Set]$, and $[\PT,\Set]$ are all complete and Cartesian closed
as well.

\todo{Note, here we don't need parametric polymorphism over $\forall
  (n : \N)$ since there are no arrows between different $n$ to
  preserve.  Should unpack this somewhere, and use a different
  notation below.}

Let's unpack this result a bit in the specific case of $[\PT,
\Type]$.  Ends in $\Type$ are given by (parametric) universal
quantification, and indexed products are $\Pi$-types; hence, we
have
\begin{align*}
(H^G)_n &= \eend{m \in \PT} \prod_{\PT(m,n)} (H_n)^{G_n} \\
       &= \all {(m : \N)} {(\Fin m \iso \Fin n) \to G_n \to H_n} \\
       &\iso (\Fin n \iso \Fin n) \to G_n \to H_n
\end{align*}
where the final isomorphism follows since $(\Fin m \iso \Fin n)$ is
only inhabited when $m = n$.

Being Cartesian closed means there is an adjunction $- \times G \adj
-^G$ between products and exponentials, which yields a natural
isomorphism \[ [\PT,\Type](F \times G, H) \iso [\PT,\Type](F,H^G) \]
Expanding morphisms of the functor category $[\PT, \Type]$ as natural
transformations and the definition of $H^G$ derived above, this
yields \[ \left( \all n {(F \times G)_n \to H_n} \right) \iso \left(
  \all n {F_n \to (\Fin n \iso \Fin n) \to G_n \to H_n} \right). \]
Intuitively, this says that a size-polymorphic function that takes a
Cartesian product shape $F \times G$ and yields another species $H$ is
isomorphic to a size-polymorphic function that takes a triple of an
$F$-shape, a $G$-shape, \emph{and a permutation on $\Fin n$}, and
yields an $H$-shape.  The point is that an $(F \times G)$-shape
consists not just of separate $F$- and $G$-shapes, but those shapes
get to ``interact'': in particular we need a permutation to tell us
how the labels on the separate $F$- and $G$-shapes ``line up''.  An
$(F \times G)$-shape encodes this information implicitly, by the fact
that the two shapes share the exact same set of labels. \todo{Need to
  think about this a bit more carefully in the context of $\P$.}
\todo{Note that we could require the equivalence to always be \id.}

\todo{picture.  Two cases with identical shapes but ``interacting''
  differently.}

Practically speaking, this result tells us how to express an
eliminator for $(F \times G)$-shapes. \todo{Elaborate on this.}

Note that $[\B, \Set]$ \emph{is} actually Cartesian closed, since it
is equivalent to $[\P, \Set]$.  \todo{Check this for sure.}  The above
derivations can be carried out in the context of $[\B, \Set]$ as well,
with similar results.  Intuitively, $\B$ ``appears to be too big on
the surface'', but is saved by virtue of being equivalent to a small
category.  In a sense, $\P$ is what is ``really going on''; $\B$ is
like $\P$ with lots of ``extra junk'' thrown in because it's
convenient to talk about \emph{sets} of labels rather than having to
work with the canonical set $\{0, \dots, n-1\}$ all the time.  This is
quite a special property of $\B$; for example, $\Set$ is certainly not
equivalent to any small categories. The same argument shows that
$[\BT, \Type]$ is Cartesian closed as well.

\section{Differentiation}
\label{sec:differentiation}

The \term{derivative} $F'$ of a species $F$ is defined by \[ F'[U] =
F[U \union \{\star\}], \] where $\star$ is some new distinguished
label not already present in $U$.  The transport of relabelings along
the derivative is defined as expected, leaving the distinguished
label alone and transporting the others.

The derivative of container types is a notion already familiar to many
functional programmers through the work of \citet{Huet_zipper},
\citet{mcbride:derivative, mcbride_clowns_2008} and
\citet{abbott_deriv}: the derivative of a type is its type of
``one-hole contexts''.  This can be seen in the definition above;
$\star$ represents the distinguished ``hole'' in the $F$-structure.

\newcommand{\pt}[1]{#1^{\bullet}}

The related operation of \term{pointing} can be defined in terms of
the derivative as \[ \pt F = \X \sprod F'. \] As illustrated in
\pref{fig:pointing}, an $\pt F$-structure can be thought of as an
$F$-structure with one particular distinguished element.

  \begin{figure}
    \centering
    \todo{FIX ME}
    \begin{diagram}[width=250]
import SpeciesDiagrams

theDia = drawSpT (struct'' 5 ((text "F" <> rect 1 1 # lw 0) |||||| circle 0.2 # fc black # translateY 0.2)) # centerXY
         ||||||
         strutX 1
         ||||||
         txt "="
         ||||||
         strutX 1
         ||||||
         ( struct 1 "X" # alignR
           ===
           strutY 0.1
           ===
           drawSpT
           ( nd (txt "F")
             [ lf Leaf
             , lf Leaf
             , lf Leaf
             , lf Hole
             , lf Leaf
             ]
           ) # alignR
         ) # centerXY
         ||||||
         strutX 1
         ||||||
         txt "="
         ||||||
         strutX 1
         ||||||
         drawSpT
         ( nd (txt "F")
           [ lf Leaf
           , lf Leaf
           , lf Leaf
           , lf Point
           , lf Leaf
           ]
         )

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Species pointing}
    \label{fig:pointing}
  \end{figure}


\section{Multisort species}
\label{sec:multisort}

\todo{General introduction to the concept of multisort species, and
  usual definition.}

\todo{The idea is to show that this fits into our general setting,
  which also widens its applicability.}

\newcommand{\lcat}[1]{#1^*}
\newcommand{\emptylist}{[\,]}

\begin{defn}
  Given a category $\C$, define the category $\lcat{\C}$ as follows.
  \begin{itemize}
  \item The objects of $\lcat{\C}$ are finite (possibly empty) lists
    $[C_1, C_2, C_3, \dots]$ of objects from $\C$.
  \item The morphisms from $[C_1, \dots, C_n]$ to $[D_1, \dots, D_n]$
    are lists of morphisms $[f_1, \dots, f_n]$ with $f_i : C_i \to
    D_i$.  Note there are no morphisms $[C_1, \dots, C_m] \to [D_1,
    \dots, D_n]$ when $m \neq n$.
  \end{itemize}
\end{defn}

\todo{Need to add more text here motivating these definitions and
  propositions.  Will go much better once I get a better sense of
  where this all is headed exactly, and which of these properties we
  need and why.}

\begin{lem}
  For any category $\C$, $\lcat{\C}$ is monoidal with list
  concatenation |++| as the tensor product and the empty list as
  the identity object.
\end{lem}

\renewcommand{\Cat}{\cat{Cat}}

\todo{Note that $\lcat{-}$ is a functor $\Cat \to \Cat$? (Is it?)}

\begin{defn}
  Define the embedding functor $e : \C \to \lcat{\C}$ which sends $C$
  to the singleton list $[C]$ and $f$ to $[f]$.
\end{defn}

\begin{prop}
  $e$ is full and faithful.
\end{prop}

\begin{defn}
  If $(\C, \otimes, I)$ is a monoidal category, we may define a
  functor $F^\otimes : \lcat{\C} \to \C$ by:
  \begin{itemize}
  \item $F^\otimes\ \emptylist = I$
  \item $F^\otimes\ [C_1, \dots, C_n] = C_1 \otimes \dots \otimes C_n$
  \end{itemize}
  and similarly for morphisms.
\end{defn}

\begin{prop}
  $F^\otimes$ is a (strict) monoidal functor.
  \begin{proof}
    $F^\otimes\ \emptylist = I$ by definition, and it is easy to check
    that $F^\otimes\ (\ell_1 \plus \ell_2) = F^\otimes\ \ell_1 \otimes
    F^\otimes\ \ell_2$.
  \end{proof}
\end{prop}

\begin{rem}
  Note that $F^\otimes$ is not, in general, an isomorphism.  In
  particular, there may exist morphisms $C_1 \otimes \dots \otimes C_n
  \to D_1 \otimes \dots \otimes D_n$ which do not arise as a tensorial
  product of morphisms $f_i : C_i \to D_i$.  For example, in $(\Set,
  +)$ we may define \todo{finish me}.
\end{rem}

Given a functor category of generalized species $[\Lab, \Str]$, we may
now form the category $[\lcat{\Lab}, \Str]$ of generalized multisort
species.  In particular, $[\lcat{\B}, \Set]$ corresponds exactly to
the notion of multisort species defined in \citet{bll}.

\todo{Note conditions under which this preserves the structure we care
  about.  Need $\lcat{\Lab}$ to still be enriched over $\Str$.  We
  have shown above that $\lcat{\Lab}$ preserves relevant monoidal
  structure.  Hmm\dots multisort corresponds particularly to
  interpreting lists using coproduct from underlying category\dots
  where does that come from?}

\section{Weighted species}
\label{sec:weighted}

\todo{General explanation and intuition for weighted species, and usual definition.}

\newcommand{\A}{\bbb{A}}

Given some object $A \in \Str$, consider the slice category $\Str/A$.
We can interpret objects of $\Str/A$ as objects of $\Str$ paired with
a ``weighting''; morphisms in $\Str/A$ are thus ``weight-preserving''
morphisms of $\Str$.

The first thing to note is that $\Str/A$ inherits coproducts from
$\Str$: given two weighted objects $(X, \omega_X)$ and $(Y,
\omega_Y)$, we can uniquely construct a weaighting $(X+Y, [\omega_X,
\omega_Y])$:
\[ \xymatrix{ X \ar[dr]_{\omega_X} \ar[r]^-{\iota_1} & X + Y
  \ar[d]||{[\omega_X, \omega_Y]} & Y \ar[l]^-{\iota_2}
  \ar[dl]^{\omega_Y} \\ & A & } \] To see that this is indeed the
coproduct $(X,\omega_X) + (Y,\omega_Y)$ in $\Str/A$, \todo{finish}

Products in $\Str/A$ are pullbacks in $\Str$.  For example, given two
weighted sets $(X, \omega_X)$ and $(Y, \omega_Y)$ in $\Set/A$, their
categorical product in $\Str/A$ is the set $\{(x,y) \mid x \in X, y
\in Y, \omega_X(x) = \omega_Y(y)\}$.  However, this is not a very
useful notion of product in this context: intuitively, taking a
product of weighted objects should yield a combined object with some
sort of combined weight, instead of limiting us to cases where the
weights match.

Instead of requiring $\Str$ to have pullbacks, we can define a
different sort of monoidal product on $\Str/A$ if we assume that
$\Str$ has products and $A$ is a monoid object, that is, there exist
morphisms $\eta : 1 \to A$ and $\mu : A \times A \to A$ satisfying
\todo{finish}.  In this case, we may define $(X, \omega_X) \otimes (Y,
\omega_Y)$ by
\[\xymatrixcolsep{4pc} \xymatrix{ X \times Y \ar[r]^-{\omega_X \times \omega_Y} & A
  \times A \ar[r]^-\mu & A. } \]  The identity for $\otimes$ is given
by $\eta$.
%% xymatrix{ \singleton \ar[r]^{!} & 1 \ar[r]^\eta & A. } \]
One can check that $\otimes$ inherits monoidal structure from
$A$. \todo{Finish this proof.}

\todo{Show that this gives the usual notion of weighted species.}

\todo{Show that this construction preserves the properties we care
  about.}

\todo{Give some examples.}

\section{$\L$-species}

\section{Unlabelled species}

\todo{Unlabelled structures, equivalence classes, and HITs}