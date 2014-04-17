%% -*- mode: LaTeX; compile-command: "mk" -*-

%include thesis.fmt

\chapter{Combinatorial species}
\label{chap:species}

\todo{List contributions of this chapter somewhere?}
\todo{Need a story for building with both color or black/white figures}

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

trees :: [a] -> [BTree a]
trees []   = [ Empty ]
trees xxs  = [ BNode x l r
             || (x,xs) <- select xxs
             , (ys, zs) <- subsets xs
             , l <- trees ys
             , r <- trees zs
             ]

treeStructures
  = centerXY
  . vcat' (with & sep .~ 0.5)
  . map (centerX . hcat' (with & sep .~ 0.5))
  . chunksOf 10
  . map (drawBinTree' (with & slHSep .~ 1.5) . fmap labT)
  . trees
  $ [0..2]
    \end{diagram}
    \caption{The species $\Bin$ of binary trees}
    \label{fig:binary-trees}
    %$
  \end{figure}
  Algebraically, such trees can be described by \[ \Bin = \One + \X
  \cdot \Bin \cdot \Bin. \]
\end{ex}

\todo{More examples.  Cycles, bags.  Permutations.  Examples of
    algebra: describe lists and trees algebraically, etc.}

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
\item sends any finite set $U$ (of \term{labels}) to a set $F\ U$ (of
  \term{shapes}), and
\item sends any bijection on finite sets $\sigma : U \bij V$ (a
  \term{relabelling}) to a function $F\ \sigma : F\ U \to F\ V$
  (illustrated in \pref{fig:relabelling}),
\end{itemize}
satisfying the following functoriality conditions:
\begin{itemize}
\item $F\ id_U = id_{F U}$, and
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

\todo{Note about finiteness of output.}

We call $F\ U$ the set of ``$F$-shapes with labels drawn from $U$'',
or simply ``$F$-shapes on $U$'', or even (when $U$ is clear from
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
on any particular such set: if $||U_1|| = ||U_2||$ and we know $F\
U_1$, we can determine $F\ U_2$ by lifting an arbitrary bijection
between $U_1$ and $U_2$.  So we often take the finite set of natural
numbers $[n] = \{0, \dots, n-1\}$ as \emph{the} canonical label set of
size $n$, and write $F\ n$ (instead of $F\ [n]$) for the set of
$F$-shapes built from this set.

Some intuition is in order: why do we require $F$ to be functorial?
\todo{Why indeed?  Functoriality ensures that $F$ is defined uniformly??}

Using the language of category theory, we can also give an equivalent, more
concise definition of species:
\begin{defn}
  \label{defn:species-cat}
  A \term{species} is a functor $F : \B \to \Set$, where $\B$ is the
  groupoid of finite sets whose morphisms are bijections, and
  $\Set$ is the category of sets and (total) functions.
\end{defn}

Reflecting the fact that the groupoid $\P$ of natural numbers and
finite permutations is (weakly) equivalent to the groupoid $\B$, it is
also possible to define species as families of shapes, indexed not by
their labels but merely by their \emph{size}:

\begin{defn}[Species (alternate)]
  \label{defn:species-p}
  A species is a functor $F : \P \to \Set$.
\end{defn}

In this case, the set of shapes corresponding to a given size $n$ can be
thought of as precisely those labelled by the canonical label set $[n]$.

\begin{rem}
  Although Definitions \ref{defn:species-set}-- \ref{defn:species-p}
  say only that a species $F$ sends a bijection $\sigma : U \bij V$ to
  a \emph{function} $F\ \sigma : F\ U \to F\ V$, the functoriality of
  $F$ guarantees that $F\ \sigma$ is a bijection as well. In
  particular, $(F\ \sigma)^{-1} = F\ (\sigma^{-1})$, since $F\ \sigma
  \comp F\ (\sigma^{-1}) = F\ (\sigma \comp \sigma^{-1}) = F\ id =
  id$, and similarly $F\ (\sigma^{-1}) \comp F\ \sigma = id$.  So one
  could (and some authors do) define species as endofunctors $F : \B
  \to \B$ with no loss of expressivity. \todo{Up to issues of
    finiteness!}
\end{rem}

\begin{rem}
  In my experience, computer scientists tend to have a bit of trouble
  with these definitions, because their first instinct is to think of a
  functor $\B \to \Set$ from a \emph{computational} point of view: \ie
  a species $F : \B \to \Set$, given some set of labels $L \in \B$,
  \emph{computes} some family of structures having those labels.

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
  seen as dual to these shapes-to-labels mappings, giving the
  \term{fiber} of each label set.  Both formulations have their
  strengths and weaknesses.
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
    \todo{Add labels to the arrows?}
    \centering
  \begin{diagram}[width=300]
import Diagrams.TwoD.Layout.Tree
import SpeciesDiagrams

charLabel c = mkLeaf (text [c] # fc black <> circle 1) ()

sps =
  [ drawList' charLabel "cdbafeg"      # centerXY # named "la"
  , drawList' numbered [3,4,2,1,6,5,7] # centerXY # named "l1"
  , wideTree numbered sampleBTree7     # centerXY # named "t1"
  , wideTree lettered sampleBTree7     # centerXY # named "ta"
  ]

dia = decoratePath (rect 30 25) sps
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
generalizations of species (multisort, weighted, and see how they fit
in this framework: each arises from considering particular categories
in place of $\B$ and $\Set$.  To keep these various functor categories
straight, the word ``species'' will be used for $[\B,\Set]$,
and ``generalized species'' for some abstract $[\Lab, \Str]$.

\subsection{Species in type theory}
\label{sec:species-in-type-theory}

\todo{Move this up somehow, and follow it with a general description
  of the rest of the chapter, to make a nice transition into the more
  technical material on lifted monoids etc.}
One generalization that will be of particular interest is a ``port''
of species into type theory. Recall that $\BT$ denotes the
($\infty$-)groupoid whose objects are triples consisting of a type $A$, a
size $n$, and an equivalence $\Fin n \iso A$, and whose morphisms are
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
with a tag so we can tell which (\pref{fig:sum}). Alternatively,
thinking of species as functors in $[\P, \Set]$, we may say that an
$(F+G)$-shape of size $n$ is either an $F$-shape of size $n$ or a
$G$-shape of size $n$.

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

For example, $\Bin + \List$ is the species representing things which
are \emph{either} binary trees or lists (\pref{fig:bin-plus-list}). As
another example, consider $\Bin + \Bin$.  It is important to bear in
mind that $+$ yields a \emph{disjoint} or ``tagged'' union; so $\Bin +
\Bin$ yields two copies of every binary tree
(\pref{fig:bin-plus-bin}), and in particular it is distinct from
$\Bin$.

\begin{figure}
  \centering
  \begin{diagram}[width=200]
dia = hcat' (with & sep .~ 0.5) [trees, lists]

trees = 
  \end{diagram}
  \caption{$(\Bin + \List)\ 2$}
  \label{fig:bin-plus-list}
\end{figure}

\begin{figure}
  \centering
  \todo{Make this diagram}

  \begin{diagram}[width=200]
    dia = circle 1 # frame 1
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
  that it preserves identity natural transformations and (vertical
  \todo{double-check}) composition of natural transformations.

  In this case it's enough simply to unfold definitions and follow the
  types.  Given species $F$, $F'$, $G$, and $G'$, and natural
  transformations $\phi : \nt F {F'}$ and $\psi : \nt G {G'}$, we
  should have $\phi + \psi : \nt {F+G} {F'+G'}$.  The component of
  $\phi + \psi$ at some $L \in \B$ should thus be a morphism in $\Set$
  of type $F\ L \uplus G\ L \to F'\ L \uplus G'\ L$; the only thing
  that fits the bill is $\phi_L \uplus \psi_L$.

  This nicely fits with the ``elementwise'' definition of $+$ on
  species: $(F + G)\ L = F\ L \uplus G\ L$, and likewise $(\phi +
  \psi)_L = \phi_L \uplus \psi_L$.  \todo{there's some
    generalization to be made here; what is it?  Is it true that any
    functor from a groupoid need only be defined on objects, and
    ``automatically'' acquires an action on morphisms?  Is this only
    true if we restrict ourselves to some special term language?}

  The action of $+$ on natural transformations thus reduces to the
  elementwise action of $\uplus$ on their components.  From this it
  follows that
  \begin{itemize}
  \item $\phi + \psi$ is natural (because XXX), and
  \item $+$ preserves identity and composition (because $\uplus$
    does). \qedhere
  \end{itemize}

  \todo{Argue it is symmetric.  Note strict vs. non-strict.}
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
choice of one-element set, $\{\star\}$; this is justified since all
one-element sets are isomorphic in \Set.)
\begin{defn}
  The \term{Cartesian} or \term{Hadamard product} of species, is defined on
  objects by $ (F \times G)\ L = F\ L \times G\ L. $
\end{defn}
\todo{Say something about action on morphisms and functoriality.}

An $(F \times G)$-shape is both an $F$-shape \emph{and} a $G$-shape,
on \emph{the same set of labels}.  There are several ways to think
about this situation, as illustrated in \pref{fig:Cartesian-product}.
One can think of two distinct shapes, with labels duplicated between
them. One can think of the labels as \emph{pointers} for locations in
a shared memory (this view will be explored more in
\pref{sec:sharing}).  Finally, one can think of the shapes themselves
as being superimposed..  This last view highlights the fact that
$\times$ is symmetric, but only up to isomorphism, since at root it
still consists of an \emph{ordered} pair of shapes.

\begin{figure}
  \centering
  \begin{diagram}[width=380]
import           Data.Bits
import           Data.List.Split
import           Diagrams.TwoD.Layout.Tree
import           Diagrams.TwoD.Path.Metafont

import           SpeciesDiagrams

connectAll l1 l2 n perm =
  withNames (map (l1 .>) [1 :: Int .. n]) $ \l1s ->
  withNames (map (l2 .>) [1 :: Int .. n]) $ \l2s ->
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
asFun perm i = perm [1..7] !! (i - 1)

numbering = hcat' (with & sep .~ 3) . map centerXY $  -- $
  [ wideTree numbered sampleBTree7 # centerX
  , drawList (numbered . asFun perm2) 7 # centerX
  ]
  where
    numbered n = mkLeaf (text (show n) # fc black <> circle 1) ()

listOnTree = wideTree (mkLeaf (circle 1)) sampleBTree7
  # cCurve 2 1 (1/4 @@@@ turn)
  # cStr   1 4
  # cCurve 4 3 (1/2 @@@@ turn)
  # cStr   3 6
  # cCurve 6 5 (1/4 @@@@ turn)
  # cCurve 5 7 (0 @@@@ turn)
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
  # top 2 1
  # top 2 6
  # top 4 3
  # bot 1 4
  # bot 6 5
  # bot 6 7
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

There is also a species, usually called $\E$, which is an identity
element for Cartesian product.  Considering $(\E \times G)\ L = \E\ L
\times G\ L \iso G\ L$, the proper definition of $\E$ becomes clear:

\begin{defn}
  The species of \emph{sets}, $\E$, is defined as the constant functor
  yielding $\{\star\}$, that is, $\E\ L = \{\star\}$.
\end{defn}

\begin{rem}
  $\E$ is called the \term{species of sets} since there is
  exactly one structure on any set of labels, which can be
  thought of as the set of labels itself, with no additional
  structure.  In fact, as all one-element sets are isomorphic, we
  may define $\E\ L = \{L\}$.
\end{rem}

\todo{Picture for $\E$.}

\begin{prop}
  $(\times, \E)$ is a symmetric monoid on $\Spe$.
\end{prop}

\begin{proof}
  The proof is omitted, since it is almost exactly the same as the
  proof for $(+, \Zero)$; the only difference is the substitution of
  Cartesian product of sets for disjoint union.  In the next section
  we will see how to generalize both proofs.
\end{proof}

\todo{Forward reference to material on closedness?}

\subsection{Lifting monoids}
\label{sec:lifting-monoids}

\begin{rem}
  Say something first about action on morphisms following from action
  on objects.  Always true when expression giving action on objects is
  composed of functors from groupoids; then functoriality comes for
  free too.  Later, can make connection to homotopy type theory.
\end{rem}

Both these constructions generalize readily.
\begin{prop}
  Any monoidal structure $(\otimes, I, \alpha, \lambda, \rho)$ on a
  category $\Str$ lifts pointwise to a monoidal structure $(\lotimes,
  \lifted I, \lifted \alpha, \lifted \lambda, \lifted \rho)$ on
  $[\Lab, \Str]$.
\end{prop}
\noindent The basic idea is exactly the same as the standard Haskell type class
instance
\begin{spec}
instance Monoid a => Monoid (e -> a) where
  mempty         = \ _ -> mempty
  f `mappend` g  = \a -> f a `mappend` g a
\end{spec}
but quite a bit more general.  To understand the basic intuition
behind the proof, the reader may enjoy proving that the above |Monoid|
instance for |e -> a| satisfies the monoid laws if the instance for
|a| does.

The formal construction and proof will be entirely unsurprising to a
category theorist, but is included here for completeness.

\todo{This definition and proof feels repetitive in some fundamental
  way.  Is there an easier way to present it??}
\begin{defn}
  Given a monoidal structure $(\otimes, I, \alpha, \lambda, \rho)$ on
  a category $\Str$, define $(\lifted{\otimes}, \lifted{I},
  \lifted{\alpha}, \lifted{\lambda}, \lifted{\rho})$ as follows.
  \begin{itemize}
  \item $\lifted{\otimes} : [\Lab,\Str] \times [\Lab,\Str] \to [\Lab,\Str]$ is the
    bifunctor computing the lifted monoidal product.
    \begin{itemize}
    \item On objects, $\lotimes$ sends pairs of functors $F,G : \Lab \to
      \Str$ to the functor $F \lotimes G : \Lab \to \Str$, defined as the
      pointwise tensor product of $F$ and $G$.  That is, on objects of
      $\Lab$, \[ (F \lotimes G)\ L = F\ L \otimes G\ L, \] and similarly, on
      morphisms \[ (F \lotimes G)\ f = F\ f \otimes G\ f. \]
      Functoriality of $F \lotimes G$ follows from that of $F$, $G$,
      and $\otimes$:
      \[ (F \lotimes G)\ id = F\ id \otimes G\ id = id \otimes id =
      id, \]
      and
      \begin{sproof}
        \stmt{(F \lotimes G) (f \comp g)}
        \reason{=}{$\lotimes$ definition}
        \stmt{F\ (f \comp g) \otimes G\ (f \comp g)}
        \reason{=}{$F$, $G$ functors}
        \stmt{(F\ f \comp F\ g) \otimes (G\ f \comp G\ g)}
        \reason{=}{$\otimes$ functor}
        \stmt{(F\ f \otimes G\ f) \comp (F\ g \otimes G\ g)}
        \reason{=}{$\lotimes$ definition}
        \stmt{(F \lotimes G)\ f \comp (F \lotimes G)\ g.}
      \end{sproof}

  \item $\lotimes$ also sends pairs of natural transformations $\phi :
    F \nt G : \Lab \to \Str$, $\psi : F' \nt G' : \Lab \to \Str$ to a
    natural transformation $\phi \lotimes \psi : F \lotimes F' \nt G
    \lotimes G'$.  The component of $\phi \lotimes \psi$ at an object
    $L \in \Lab$ is a morphism $\mor {(F \lotimes F')\ L} {(G \lotimes
      G')\ L} = \mor {F\ L \otimes F'\ L} {F\ L \otimes G'\ L}$,
    similarly defined by $\phi_L \otimes \psi_L$.  Naturality of $\phi
    \lotimes \psi$ is thus given by
    \[ \xymatrixcolsep{5pc}
       \xymatrix{
         F\ L \otimes F'\ L
           \ar[r]^{\phi_L \otimes \psi_L}
           \ar[d]_{F f \otimes F' f}
       & G\ L \otimes G'\ L
           \ar[d]^{G f \otimes G' f}
       \\
         F\ L' \otimes F'\ L'
           \ar[r]_{\phi_{L'} \otimes \psi_{L'}}
       & G\ L' \otimes G'\ L'
       }
    \]
    which commutes by naturality of $\phi$ and $\psi$ and
    functoriality of $\otimes$.
    \end{itemize}

    We must show that $\lotimes$ is a bifunctor, which follows
    straightforwardly from the functoriality of $\otimes$:
    \begin{align*}
      (id \lotimes id)_L = id_L \otimes id_L = id_L,
    \end{align*}
    and
    \begin{sproof}
      \stmt{((\phi \comp \phi') \lotimes (\psi \comp \psi'))_L}
      \reason{=}{$\lotimes$ definition}
      \stmt{(\phi \comp \phi')_L \otimes (\psi \comp \psi')_L}
      \reason{=}{definition of vertical composition \todo{check}}
      \stmt{(\phi_L \comp \phi'_L) \otimes (\psi_L \comp \psi'_L)}
      \reason{=}{$\otimes$ functor}
      \stmt{(\phi_L \otimes \psi_L) \comp (\phi'_L \otimes \psi'_L)}
      \reason{=}{$\lotimes$ definition}
      \stmt{(\phi \lotimes \psi)_L \comp (\phi' \lotimes \psi')}
    \end{sproof}

  \item $\lifted{I} \in [\Lab,\Str]$ is the constant functor $\Delta_I$.
  \item Define $\lifted{\alpha}_{F,G,H} : \ntiso {(F \lotimes G) \lotimes H}
    {F \lotimes (G \lotimes H)}$ by $(\lifted \alpha_{F,G,H})_L =
    \alpha_{FL,GL,HL}$. \todo{Need to show $\lifted{\alpha}$
      is a natural isomorphism, and for any $F,G,H$,
      $\lifted{\alpha}_{F,G,H}$ is a natural transformation. (?)}
  \item Similarly, $(\lifted{\lambda}_F)_L = \lambda_{FL}$ and
    $(\lifted{\rho}_F)_L = \rho_{FL}$.
  \end{itemize}
\end{defn}

\begin{thm}
  If $(\otimes, I, \alpha, \lambda, \rho)$ is a monoidal structure on
  $\Str$, then $(\lotimes, \lifted I, \lifted \alpha, \lifted \lambda,
  \lifted \rho)$ defines a monoidal structure on the functor category
  $[\Lab, \Str]$.
\end{thm}
\begin{proof}
  It remains to check the coherence properties. \todo{Finish}
\end{proof}

\begin{prop}
  The monoidal lifting defined above preserves the following properties:
  \begin{itemize}
  \item If $\otimes$ is symmetric, so is $\lotimes$.
  \item If $\otimes$ is a categorical product, so is $\lotimes$.
  \item If $\otimes$ is a categorical coproduct, so is $\lotimes$.
  \item \todo{distributive}
  \end{itemize}
\end{prop}
\todo{\Set is distributive, in the sense that the canonical morphism
  $X \times Y + X \times Z \to X \times (Y + Z)$ is an isomorphism.
  Is $[\B, \Set]$ distributive in the same way?  If so, does lifting
  monoids always preserve distributivity? Answers: yes, and yes.}

\begin{proof}
  \todo{Finish}
\end{proof}

\begin{ex}
  We note that lifting coproducts in $\Set$ to $[\B,\Set]$ yields the
  $(+, \Zero)$ structure on species, and likewise lifting products
  yields $(\times, \E)$, Cartesian product.  Since
  $(\uplus,\varnothing)$ is a coproduct structure on $\Set$, it
  follows that $(+, \Zero)$ is in fact a coproduct structure on the
  category $[\B,\Set]$ of species, and likewise $(\times, \One)$ is a
  categorical product.
\end{ex}

\begin{ex}
  Take $\Lab = \cat{1}$ (the trivial category with one object and one
  morphism). In this case, functors in $[\cat{1}, \Str]$ are just
  objects of $\Str$, and a lifted monoidal operation is identical
  to the unlifted one.
\end{ex}

\begin{ex}
  Take $\Lab = \disc{\cat{2}}$, the discrete category with two
  objects.  Then a functor $F : \disc{\cat{2}} \to \Str$ is just a
  pair of objects in $\Str$.  For example, if $\Str = \Set$, a functor
  $\disc{\cat{2}} \to \Set$ is a pair of sets.  In this case, taking
  the lifted sum $F + G$ of two functors $F,G : \disc{\cat{2}} \to
  \Set$ corresponds to summing the pairs elementwise, that is, $(S_1,
  T_1) + (S_2, T_2) = (S_1 + S_2, T_1 + T_2)$.  Another way of
  thinking of a functor $\disc{\cat{2}} \to \Set$ is as a single
  collection of elements where each element is tagged with one of two
  tags (``left'' or ``right'', $0$ or $1$, \etc).  From this point of
  view, a lifted sum can be thought of as a tag-preserving disjoint union.

  \todo{picture?}
\end{ex}

\begin{ex}
  As an example in a similar vein, consider $\Lab = \disc{\N}$, the
  discrete category with natural numbers as objects.  Functors
  $\disc{\N} \to \Str$ are countably infinite sequences of objects
  $[S_0, S_1, S_2, \dots]$.  One way to think of this is as a
  collection of $\Str$-objects, one for each natural number
  \emph{size}.  For example, if $\Str = \Set$ then the sequence of
  sets $[S_0, S_1, S_2, \dots]$ can be thought of as a single
  collection of elements with each element tagged by its size. (This
  ``size'' intuition is actually fairly arbitrary at this point---the
  objects of $\disc{\N}$ are in some sense just an arbitrary countably
  infinite set of labels, and there is no particular reason they
  should represent ``sizes''.  However, as we will see, this intuition
  carries through well to subsequent examples.)

  Lifting a monoidal operation to countable sequences of objects
  performs a ``zip'', applying the monoidal operation between matching
  positions in the two lists: \[ [S_1, S_2, S_3, \dots] \oplus [T_1,
  T_2, T_3, \dots] = [S_1 \oplus T_1, S_2 \oplus T_2, S_3 \oplus T_3,
  \dots] \] If $\oplus$ can be thought of as a size-preserving
  operation---for example, disjoint union combines two collections of
  size-$n$ things into one collection of size-$n$ things---then
  lifting $\oplus$ combines entire size-indexed collections in a
  size-preserving way.
  \todo{picture}
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

\section{Day convolution: partitional and arithmetic product}
\label{sec:day}

There is another notion of product for species, the \term{partitional}
or \term{Cauchy} product.  It it is the partitional product, rather
than Cartesian product, which corresponds to the product of generating
functions and which gives rise to the usual notion of product on
algebraic data types.  For these reasons, partitional product is often
simply referred to as ``product'', without any modifier.

There is also another less well-known product, \term{arithmetic
  product} \cite{Maia2008arithmetic}, which can be thought of as a
symmetric form of composition.  These two products arise in an
analogous way, via a categorical construction known as \emph{Day
  convolution}.

\subsection{Partitional/Cauchy product}
\label{sec:partitional-product}


The partitional product $F \sprod G$ of two species $F$
and $G$ consists of paired $F$- and $G$-shapes %, but with a twist:
% instead of being replicated, as in Cartesian product, the labels are
with the labels \emph{partitioned} between the two shapes
(\pref{fig:product}).

\todo{picture of a pair of trees with disjoint labels, or something
  like that.}

  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import SpeciesDiagrams

theDia
  = hcat' (with & sep .~ 1)
    [ struct 5 "F•G"
    , text' 1 "="
    , vcat' (with & sep .~ 0.2)
      [ struct 2 "F"
      , struct 3 "G"
      ]
      # centerY
    ]

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Partitional species product}
    \label{fig:product}
  \end{figure}

\begin{defn}
  The \term{partitional} or \term{Cauchy product} of two species $F$
  and $G$ is the functor defined on objects by \[ (F \sprod G)\ L =
  \biguplus_{L_1,L_2 \vdash L} F\ L_1 \times G\ L_2 \] where
  $\biguplus$ denotes an indexed coproduct of sets, and $L_1,L_2
  \vdash L$ denotes that $L_1$ and $L_2$ constitute a partition of
  $L$, (\ie $L_1 \union L_2 = L$ and $L_1 \intersect L_2 =
  \varnothing$). On bijections, $F \cdot G$ uses the action of $F$ on
  the restriction of the bijections to $L_1$, and similarly for $G$
  and $L_2$.
\end{defn}

The identity for partitional product needs to be some species $\One$
such that \[ (\One \cdot G)\ L = \left(\biguplus_{L_1,L_2 \vdash L}
  \One\ L_1 \times G\ L_2 \right) \iso G\ L. \] The only way for this
isomorphism to hold naturally in $L$ is if $\One\ \varnothing =
\{\star\}$ (yielding a summand of $G\ L$ when $\varnothing+L = L$) and
$\One\ L_1 = \varnothing$ for all other $L_1$ (cancelling all the
other summands).

\begin{defn}
  The unit species, $\One$, is defined by
  \[ \One\ L =
  \begin{cases}
    \{\star\} & L = \varnothing \\
    \varnothing & \text{otherwise}.
  \end{cases}
  \]
\end{defn}

\subsection{Arithmetic product}
\label{sec:arithmetic-product}

\newcommand{\aprod}{\boxtimes}

There is another, more recently discovered monoidal structre on
species known as \emph{arithmetic product} \cite{Maia2008arithmetic}.
The arithmetic product of species $F$ and $G$, written $F \aprod G$,
can intuitively be thought of as an ``$F$-assembly of cloned
$G$-shapes'', that is, an $F$-shape containing multiple copies of a
single $G$-shape (\pref{fig:arithmetic-product}).  Unlike the usual
notion of composition, where the $F$-shape would be allowed to contain
many different $G$-shapes, this notion is symmetric: an $F$-assembly
of cloned $G$-shapes is isomorphic to a $G$-assembly of cloned
$F$-shapes.  Another intuitive way to think of the arithmetic product,
which points out the symmetry more clearly, is to think of a
rectangular matrix of labels, together with an $F$-shape labelled by
the rows of the grid, and a $G$-shape labelled by the columns.

\todo{Give more formal definition and examples.}

\begin{figure}
  \centering
  \begin{diagram}[width=380]
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

grays  = map (\k -> blend k black white) [0, 0.2, 0.8, 1, 0.5]
shapes = [circle 0.2, triangle 0.4, square 0.4]

grid = vcat' (with & sep .~ 0.5)
  [ tree3 (\n -> mkLeaf (circle 0.4 # fc (grays !! (n-1))) n) # translateX 3.4
  , hcat' (with & sep .~ 0.5)
    [ list2 (\n -> (mkLeaf ((shapes !! (n-1)) # rotateBy (1/4) <> circle 0.4) n)) # rotateBy (3/4)
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
  (map (fc white . enrect . (mkLeaf (tree3 (mkLeaf (circle 0.4)) # centerXY # scale 0.5))) [1 .. 3 :: Int])
  <>
  hrule 7 # alignL

enrect d = d <> roundedRect (width d + 0.2) (height d + 0.2) 0.2

tree3 nd
  = maybe mempty (renderTree nd (~~))
  . uniqueXLayout 1 1
  $ sampleBTree5

list2 nd = hcat' (with & sep .~ 1 & catMethod .~ Distrib)
  (map nd [1 :: Int .. 3])
  <>
  hrule 2 # alignL
  where
    aSty = with & arrowHead .~ noHead

dia = frame 0.2 . centerXY . hcat' (with & sep .~ 2) . map centerXY $
  [ grid
  , assembly1 # scale 1.3
  , assembly2
  ]
  # lw 0.05
  \end{diagram}
  \caption{Three views on arithmetic product of species}
  \label{fig:arithmetic-product}
\end{figure}

\bay{How can we say that we are using ``the same'' ``product-like''
  monoidal structure in all these different categories?  Are they
  related by monoidal functors?}

\subsection{Day convolution}
\label{sec:day-convolution}

Just as sum and Cartesian product were seen to arise from the same
construction applied to different monoids, both partitional and
arithmetic product arise from \emph{Day convolution}, applied to
different monoidal structures on $\B$.

The essential idea, first described by Brian
Day~\cite{day-convolution}, is to construct a monoidal structure on a
functor category $[\Lab, \Str]$ based primarily on a monoidal
structure on the \emph{domain} category $\Lab$.  In particular, Day
convolution requires
\begin{itemize}
\item a monoidal structure $\oplus$ on the domain $\Lab$;
\item that $\Lab$ be \emph{enriched over} $\Str$, \ie\ for any two
  objects $L_1,L_2 \in \Lab$ there is a hom-object $\Lab(L_1,L_2) \in
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
  [\Lab, \Str]$ is given by the coend \[ F \oast G = \int^{L_1, L_2}
  F\ L_1 \otimes G\ L_2 \otimes \Lab(-, L_1 \oplus L_2). \]
\end{defn}

\begin{rem}
  Note that $\int^{L_1, L_2} \dots$ is used as an abbrevation for a
  coend over the product category $\Lab \times \Lab$.
\end{rem}

\begin{rem}
  Note that there are only covariant occurrences of $L_1$ and $L_2$ in
  the above definition, which simplifies the definition of the
  coend. \todo{flesh out}
\end{rem}

\begin{rem}
  Since groupoids are self-dual, we may ignore the $-^\op$ in the
  common case that $\Lab$ is a groupoid.
\end{rem}

This operation is associative, and has as a unit $j(I)$ where $I$ is
the unit for $\oplus$ and $j : \Lab \to [\Lab^{\text{op}}, \Str]$ is the Yoneda
embedding, that is, $j(L) = \Lab(-,L)$.

\begin{ex}
  Let's begin by looking at the traditional setting of $\Lab = \B$ and
  $\Str = \Set$.  Though $\B$ does not have coproducts, it does have a
  monoidal structure given by disjoint union.  $\B$ is indeed enriched
  over $\Set$, which is also cocomplete and has a symmetric monoidal
  structure given by Cartesian product.

  Specializing the definition to this case, and expressing the coend
  as a quotient, we obtain
  \begin{align*}
    (F \cdot G)(L) &= \int^{L_1, L_2} F\ L_1 \times G\ L_2 \times
    (L \iso L_1 + L_2) \\
    &= \left( \biguplus_{L_1, L_2} F\ L_1 \times G\ L_2 \times (L \iso L_1
      + L_2) \right) \Big/ \sim
  \end{align*}
  where every pair of bijections $\sigma_i : L_i \iso L_i'$ induces
  equivalences of the form $(L_1, L_2, f, g, i) \sim (L_1', L_2', F\
  \sigma_1\ f, G\ \sigma_2\ g, (\sigma_1 + \sigma_2) \comp i)$.  In
  other words, we ``cannot tell apart'' any two summands related by a
  pair of relabellings.  The only way to tell two summands apart is if
  their respective values of $L_1$ and $L_2$ stand in a different
  relation to $L$, as witnessed by the isomorphism.  Therefore, all
  the equivalence classes can be represented canonically by a
  partition of $L$ into two disjoint subsets, giving rise to the
  earlier definition: \[ (F \sprod G)\ L =
  \biguplus_{L_1,L_2 \vdash L} F\ L_1 \times G\ L_2. \]

  Also, in this case, the identity element is $j(I) = j(\varnothing) =
  \B(-,\varnothing)$, that is, the species which takes as input a
  label set $L$ and constructs the set of bijections between $L$ and
  the empty set.  Clearly there is exactly one such bijection when $L
  = \varnothing$, and none otherwise: as expected, this is the species
  $\One$ defined in the previous section.
\end{ex}

\begin{ex}
  \todo{edit this. Monoidal structure on $\P$??}
  Although $\B$ and $\P$ are equivalent, it is still instructive
  to work out the general definition in the case of $\P$.  In this
  case, we have a monoidal structure on $\P$ given by addition, with
  $f + g : \Fin (m + n) \iso \Fin (m + n)$ defined in the evident way,
  with $f$ acting on the first $m$ values of $\Fin (m+n)$ and $g$ on
  the last $n$.

  Specializing the definition, \[ (F \sprod G)_n \defeq \int^{n_1,
    n_2} F_{n_1} \times G_{n_2} \times (\Fin n \iso \Fin {n_1} + \Fin {n_2})  \] that is, an
  $(F \sprod G)$-shape of size $n$ consists of an $F$-shape of size
  $n_1$ and a $G$-shape of size $n_2$, where $n_1 + n_2 = n$.
  Indexing by labels is a generalization (a \emph{categorification},
  in fact) of this size-indexing scheme, where we replace natural
  numbers with finite types, addition with coproduct, and
  multiplication with product.
\end{ex}

\begin{ex}
  There is another monoidal structure on $\B$ corresponding to the
  Cartesian product of sets. If we instantiate the framework of Day
  convolution with this product-like monoidal structure ---but
  keep everything else the same, in particular continuing to use
  products on $\Set$---we obtain the arithmetic product.
\end{ex}

\begin{ex}
  Let's examine this in detail in the case of $[\P,\Set]$.  The
  monoidal structure on $\P$ is defined on objects as $m \otimes n =
  mn$.  On morphisms, given $f : \fin m \bij \fin m$ and $g : \fin n
  \bij \fin n$, we have $f \otimes g : \fin{mn} \bij \fin{mn}$ defined
  by \todo{finish}.

  Instantiating the definition of Day convolution yields
  \begin{align*}
    (F \boxtimes G)\ n &= \int^{n_1,n_2} F\ n_1 \times G\ n_2 \times
    \P(n, n_1n_2) \\
    &= \int^{n_1,n_2} F\ n_1 \times G\ n_2 \times (\fin n \bij \fin
    {n_1 n_2}) \\
    &= ? \\
    &= \biguplus_{d \mid n} F\ d \times G\ (n/d)
  \end{align*}

  \todo{Finish. where $\otimes$ denotes the product monoidal structure
    on $\B$.  We cannot write this quite as nicely as partitional
    product, since there is no canonical way to decompose}
\end{ex}

\begin{ex}
  It remains to verify that $\BT$ and $\Type$ have the right properties.
  \begin{itemize}
  \item Like $\B$, there are monoidal structures on $\BT$
    corresponding to the coproduct and product of types. It is worth
    noting, however, that there are \emph{many} monoidal structures
    corresponding to each. A monoidal operation on $\BT$ does not
    simply combine two types into their coproduct or product, but also
    combines their finiteness evidence into corresponding evidence for
    the combined type, and there are many ways to accomplish this.
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

  Given $F,G \in [\BT,\Type]$, we can instantiate the definition
  of Day convolution to get
  \[ (F \cdot G)\ L = \sum_{L_1, L_2} F\ L_1 \times G\ L_2 \times (L
  \iso L_1 + L_2), \] and similarly for generalized arithmetic
  product.

\end{ex}

\section{Composition}
\label{sec:composition}

\section{Closed monoidal structures and elimination}
\label{sec:closed}

\paragraph{Cartesian closed}  If $\Lab$ is small and $\Str$ is complete and
Cartesian closed, then $[\Lab,\Str]$ is also complete and Cartesian
closed. (cite:
\url{mathoverflow.net/questions/104152/exponentials-in-functor-categories/104178#104178})
In particular the exponential of $F,G : \Lab \to \Str$ is given by \[
G^F (L) = \int_{K \in \Lab} \prod_{\Lab(L,K)} G(K)^{F(K)}. \] Note
that neither $\B$ nor $\BT$ is small, since the class of all finite
sets or types is too large; however, their skeletons $\P$ and $\PT$
are small.  Since $\Set$ and $\Type$ are both complete and
Cartesian closed, we conclude that both the skeletonized category
$[\P,\Set]$ of traditional species and its type-theoretic counterpart
$[\PT, \Type]$ are complete and Cartesian closed as well.

\todo{Note, here we don't need parametric polymorphism over $\forall
  (n : \N)$ since there are no arrows between different $n$ to
  preserve.  Should unpack this somewhere, and use a different
  notation below.}

Let's unpack this result a bit in the specific case of $[\PT,
\Type]$.  Ends in $\Type$ are given by (parametric) universal
quantification, and indexed products are $\Pi$-types; hence, we
have
\begin{align*}
(H^G)_n &= \int_{m \in \PT} \prod_{\PT(m,n)} (H_n)^{G_n} \\
       &= \forall (m : \N). (\Fin m \iso \Fin n) \to G_n \to H_n \\
       &\iso (\Fin n \iso \Fin n) \to G_n \to H_n
\end{align*}
where the final isomorphism follows since $(\Fin m \iso \Fin n)$ is
only inhabited when $m = n$.

Being Cartesian closed means there is an adjunction $- \times G \vdash
-^G$ between products and exponentials, which yields a natural
isomorphism \[ [\PT,\Type](F \times G, H) \iso [\PT,\Type](F,H^G) \]
Expanding morphisms of the functor category $[\PT, \Type]$ as natural
transformations and the definition of $H^G$ derived above, this
yields \[ \left( \forall n. (F \times G)_n \to H_n\right) \iso \left(
  \forall n. F_n \to (\Fin n \iso \Fin n) \to G_n \to H_n\right). \]
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
%% xymatrix{ \{\star\} \ar[r]^{!} & 1 \ar[r]^\eta & A. } \]
One can check that $\otimes$ inherits monoidal structure from
$A$. \todo{Finish this proof.}

\todo{Show that this gives the usual notion of weighted species.}

\todo{Show that this construction preserves the properties we care
  about.}

\todo{Give some examples.}

\section{$\L$-species}
