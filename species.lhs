%% -*- mode: LaTeX; compile-command: "mk" -*-

%include thesis.fmt

\chapter{Combinatorial species}
\label{chap:species}

\todo{edit, dumped here from proposal}

The theory of species is a unified theory of \emph{structures}, or as
a programmer might say, \emph{containers}. By a \emph{structure} we
mean some sort of ``shape'' containing \emph{locations} (or
\emph{positions}). \pref{fig:example-structures} shows two different
structures, each with eight locations.

\begin{figure}
\centering
\begin{diagram}[width=250]
import Diagrams
dia = (octo [0..7] |||||| strutX 4 |||||| tree # centerXY)
    # centerXY
    # pad 1.1
\end{diagram}
\caption{Example structures} \label{fig:example-structures}
\end{figure}

It is very important to note that we are talking about structures with
\emph{labeled locations}; the numbers in \pref{fig:example-structures}
are not data being stored in the structures, but \emph{names}
or \emph{labels} for the locations.  To talk about a \emph{data
  structure} (\ie\ a structure filled with data), we must also
specify a mapping from locations to data, like $\{ 0 \mapsto
\texttt{'s'}, 1 \mapsto \texttt{'p'}, 2 \mapsto \texttt{'e'} \dots
\}$, as shown in~\pref{fig:shape-data}.  This will be made more
precise in~\pref{sec:species-types}.

\begin{figure}
\centering
\begin{diagram}[width=200]
import Diagrams
dia = shapePlusData # centerXY # pad 1.1

shapePlusData = octo [0..7]
  |||||| strutX 2
  |||||| (text "+" # fontSize 3 <> phantom (square 1 :: D R2))
  |||||| strutX 2
  |||||| mapping
  |||||| strutX 2

mapping = centerXY . vcat' (with & sep .~ 0.2) . map mapsto $ zip [0..7] "species!"
mapsto (l,x) = lab l ||-|| mkArrow 3 mempty ||-|| elt x
x ||-|| y = x |||||| strutX 0.5 |||||| y
-- arr = (hrule 3 # alignR # lw 0.03)
--          <> (eqTriangle 0.5 # rotateBy (-1/4) # fc black # scaleY 0.7)
\end{diagram}
%$
\caption{Data structure = shape + data} \label{fig:shape-data}
\end{figure}

One useful intuition is to think of the labels as \emph{memory
  addresses}, which point off to some location where a data value is
stored. This intuition has some particularly interesting consequences
when it comes to operations like Cartesian product and functor
composition---explained in~\pref{sec:operations}---since it gives us a
way to model sharing (albeit in limited ways).

Why have labels at all? In the tree shown
in~\pref{fig:example-structures}, we can uniquely identify each
location by a path from the root of the tree, without referencing
labels at all. Hence we can unambiguously separate a tree from its
data by storing a simple unlabeled tree shape (with unit values at all
the locations) along with a list of values.  However, the structure on
the left illustrates one reason labels are needed. The circle is
supposed to indicate that the structure has \emph{rotational
  symmetry}, so there would be no way to uniquely refer to any
location except by giving them labels.

\subsection{Definition}
\label{sec:species-definition}

We want to think of each labeled structure as \emph{indexed by} its
set of labels (or, more generally, by the \emph{size} of the set of
labels).  We can accomplish this by a mapping from label sets to all
the structures built from them, with some extra properties to
guarantee that we really do get the same family of structures no
matter what set of labels we happen to choose.

\begin{defn}
A \term{species} $F$ is a pair of mappings which
\begin{itemize}
\item sends any finite set $U$ (of \term{labels}) to a finite set
  $F[U]$ (of \term{structures}), and
\item sends any bijection on finite sets $\sigma : U \bij V$ (a
  \term{relabeling}) to a function $F[\sigma] : F[U] \to F[V]$
  (illustrated in \pref{fig:relabeling}),
\end{itemize}
satisfying the following functoriality conditions:
\begin{itemize}
\item $F[id_U] = id_{F[U]}$, and
\item $F[\sigma \circ \tau] = F[\sigma] \circ F[\tau]$.
\end{itemize}

This definition is due to Joyal \citep{joyal}, as described in BLL
\citep{bll}.
\end{defn}

\begin{figure}
  \centering
  \includegraphics{relabeling}
  \caption{Relabeling}
  \label{fig:relabeling}
\end{figure}
\todo{redraw this with diagrams}

Using the language of category theory, this definition can be pithily
summed up by saying that ``a species is a functor from $\B$ to
$\FinSet$'', where $\B$ is the category of finite sets whose morphisms are
bijections, and $\FinSet$ is the category of finite sets whose morphisms
are arbitrary (total) functions.

We call $F[U]$ the set of ``$F$-structures with
labels drawn from $U$'', or simply ``$F$-structures on $U$'', or even
(when $U$ is clear from context) just ``$F$-structures''.  $F[\sigma]$
is called the ``transport of $\sigma$ along $F$'', or sometimes the
``relabeling of $F$-structures by $\sigma$''.

To make this more concrete, consider a few examples:
\begin{itemize}
\item The species $\L$ of \emph{lists} (or \emph{linear orderings})
  sends every set of labels (of size $n$) to the set of all sequences
  (of size $n!$) containing each label exactly once
  (\pref{fig:lists}).

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
  , enRect listStructures
  ]
  # centerXY
  # pad 1.1

drawList = hcat . intersperse (mkArrow 0.4 mempty) . map labT

listStructures =
    hcat' (with & sep .~ 0.7)
  . map (vcat' (with & sep .~ 0.5))
  . chunksOf 2
  . map drawList
  . permutations
  $ [0..2]
    \end{diagram}
    \caption{The species $\L$ of lists}
    \label{fig:lists}
    %$
  \end{figure}

\item The species of \emph{(rooted, ordered) binary trees} sends every
  set of labels to the set of all binary trees built over those labels
  (\pref{fig:binary-trees}).
  \begin{figure}
    \centering
    \begin{diagram}[width=400]
import SpeciesDiagrams
import Data.Tree
import Diagrams.TwoD.Layout.Tree
import Control.Arrow (first, second)

dia =
  hcat' (with & sep .~ 0.5)
  [ unord (map labT [0..2])
  , mkArrow 2 (txt "T")
  , enRect treeStructures
  ]
  # centerXY
  # pad 1.1

drawTreeStruct = renderTree id (~~) . symmLayout . fmap labT

trees []   = []
trees [x]  = [ Node x [] ]
trees xxs  = [ Node x [l,r]
             || (x,xs) <- select xxs
             , (ys, zs) <- subsets xs
             , l <- trees ys
             , r <- trees zs
             ]

select []     = []
select (x:xs) = (x,xs) : (map . second) (x:) (select xs)

subsets []     = [ ([],[]) ]
subsets (x:xs) = (map . first) (x:) ss ++ (map . second) (x:) ss
  where ss = subsets xs

treeStructures =
    hcat' (with & sep .~ 0.5)
  . map drawTreeStruct
  . trees
  $ [0..2]
    \end{diagram}
    \caption{The species $\T$ of binary trees}
    \label{fig:binary-trees}
    %$
  \end{figure}

% \item The species of \emph{permutations} \todo{finish}

\end{itemize}

The functoriality of relabeling means that the actual labels used
don't matter; we get ``the same structures'', up to relabeling, for
any label sets of the same size.  We might say that species are
\term{parametric} in the label sets of a given size. In particular,
$F$'s action on all label sets of size $n$ is determined by its action
on any particular such set: if $||U_1|| = ||U_2||$ and we know
$F[U_1]$, we can determine $F[U_2]$ by lifting an arbitrary
bijection between $U_1$ and $U_2$.  So we often take the finite set of
natural numbers $[n] = \{0, \dots, n-1\}$ as \emph{the}
canonical label set of size $n$, and write $F[n]$ (instead of
$F[[n]]$) for the set of $F$-structures built from this set.

% It's not hard to show that functors preserve isomorphisms, so although
% the definition only says that a species $F$ sends a bijection $\sigma
% : U \bij V$ to a \emph{function} $F[\sigma] : F[U] \to F[V]$, in fact,
% by functoriality every such function must be a bijection. \todo{is
%   this really important to say?}

\todo{edit}

Species are defined as functors $\B \to \Set$ \citep{bll}.
Intuitively, the action of a species on objects takes a finite set of
``labels'' to a set of ``structures''; the action on morphisms
requires the action on objects to be ``invariant under relabelling''.

This is a simple and convenient definition, but there are several
reasons that compel us to generalize it.  First, \B and \Set enjoy
many special properties as categories (for example, \Set is
cartesian closed, has all limits and colimits, and so on).  It is
enlightening to see precisely which properties are required in which
situations, and we miss this entirely if we start with the kitchen
sink.

More subtly, we wish to work in a constructive, computational setting,
and the specific categories \B and \Set are
inappropriate. \todo{reference stuff from finiteness section
  previously.}  We will wish to work with more computationally
concrete categories based in type theory, such as $\BT$, but in order
to do so we need to show that they have the right properties.

\todo{Note we will often use the intuition of ``sets of labels'' but
  of course in more general settings the objects of the category
  $\Lab$ might not ``have elements'' at all. More generally we can
  just think of structures indexed by objects of $\Lab$, rather that
  structures ``containing labels''.}

\section{Species from scratch}
\label{sec:species-scratch}

The idea is to start ``from scratch'' and build up a generic notion of
species which supports the operations we want.  Along the way, we will
also get a much clearer picture of where the operations ``come from''.

\todo{cite ``Operads of J.P. May'', ``Cartesian Closed Bicategory of
  Generalised Species of Structure'', ``Monoidal Functors, Species, and
  Hopf Algebras''}

We begin by considering functor categories in general.  Given two
categories $\Lab$ and $\Str$, what can we say about functors $\Lab \to
\Str$, and more generally about the functor category $[\Lab, \Str]$?
Of course, there is no point in calling functors $\Lab \to \Str$
``species'' for just any old categories $\Lab$ and $\Str$.  But what
properties must $\Lab$ and $\Str$ possess to make this interesting and
worthwhile?

\todo{should talk about motivation from memory locations and structures.}

In each of the following sections we will discuss some specific
constructions on species (considered as functors $\B \to \Set$), and
then generalize to arbitrary functor categories to see what properties
are needed in order to define them---\ie\ where the constructions
``come from''---and give some specific examples.

\section{Sum}
\label{sec:sum}

One of the simplest operations on species is the \emph{sum} of two
species.
\begin{defn}
  Given species $F, G : \B \to \Set$, we may form their sum $F + G$,
  defined on objects by \[ (F + G)\ L \defeq F\ L + G\ L, \] where the
  $+$ on the right hand side denotes disjoint union of sets.
\end{defn}
That
is, a labelled $(F + G)$-shape is either a labelled $F$-shape or a
labelled $G$-shape (\pref{fig:sum}). \todo{Say something about action
  on arrows/functoriality.}

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
      , text' 1 "+"
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
  We may also define the \term{zero} or \term{empty} species,
  $\Zero$, as the unique species with no shapes whatsoever, that is,
  \begin{equation*}
    \Zero\ L \defeq \varnothing
  \end{equation*}
\end{defn}

% As a simple example, the species $\One + \X$ corresponds to the
% familiar |Maybe| type from Haskell, with $\lab{\inl} \lab{\One}$
% playing the role of |Nothing| and $\lab{\inr} \comp \lab{\cons{x}}$
% playing the role of |Just|.  Note that $\LStr {\One + \X} L A$ is
% only inhabited for certain $L$ (those of size $0$ or $1$), and moreover that
% this size restriction determines the possible structure of an
% inhabitant.
%
% Note, can't include the above if we haven't talked about 1 or X
% yet.  And I now think a better way to organize things is by talking
% about each fundamental monoidal construction along with its unit.
% As for introduction forms, it's pretty trivial.

It's not hard to check that $(+,\Zero)$ forms a commutative monoid
structure on species (up to isomorphism).  Stepping back a bit, we can
see that this monoidal structure on species arises from a
corresponding monoidal structure on sets in an entirely
straightforward way: the sum of two functors is defined as the
pointwise sum of their outputs, and likewise \Zero, the identity for
the sum of species, is defined as the functor which constantly, \ie
pointwise, returns $\varnothing$, the identity for the sum of sets.

This generalizes straightforwardly: any monoidal structure on a
category $\Str$ lifts pointwise to a corresponding monoidal structure
on the functor category $[\Lab, \Str]$. \todo{find a reference for
  proof?} (Note that this is exactly the same idea as the standard
Haskell type class instance
\begin{spec}
instance Monoid a => Monoid (e -> a) where
  mempty         = \ _ -> mempty
  f `mappend` g  = \a -> f a `mappend` g a
\end{spec}
but quite a bit more general.)  Moreover, this lifting preserves
commutativity, and products and coproducts on a category $\Str$ lift
to products and coproducts on $[\Lab, \Str]$.  Since $(+,\varnothing)$
is a coproduct structure on $\Set$, it follows that $(+, \Zero)$ is in
fact a coproduct structure on the category of species.

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

\section{Cartesian/Hadamard product}
\label{sec:cartesian}

Disjoint union is not the only monoidal structure on $\Set$. In
addition to coproducts $\Set$ also has products, where the product of
two sets $S$ and $T$ is given by the Cartesian product, $S \times T =
\{ (s,t) \mid s \in S, t \in T \}$, with any one-element set as the
identity (for convenience, we may suppose there is some canonical
choice of one-element set, $\{\star\}$).
\begin{defn}
  By the discussion of the previous section, this automatically lifts
  to a pointwise product structure on species, known as the
  \term{Cartesian} or \term{Hadamard product}: \[ (F \times G)\ L = F\
  L \times G\ L. \]
\end{defn}
In the same way that an $(F + G)$-shape is either an
$F$-shape \emph{or} a $G$-shape on a given set of labels, an $(F
\times G)$-shape is both an $F$-shape \emph{and} a $G$-shape, on
\emph{the same set of labels} (\pref{fig:Cartesian-product}).
\begin{figure}
  \centering
  \todo{Make a diagram.}
  \caption{Cartesian species product}
  \label{fig:Cartesian-product}
\end{figure}

\begin{defn}
  Lifting the identity element pointwise gives the species \[ \E\ L =
  \{\star\}, \] usually called the \term{species of sets}, which is the
  identity for Cartesian product of species.
\end{defn}
\begin{rem}
  It is called the species of sets since there is exactly one
  structure on any set of labels, which can intuitively be thought of
  as the set of labels itself, with no additional structure.  In fact,
  since all one-element sets are isomorphic, we may as well define \[
  \E\ L = \{L\}. \]
\end{rem}

Cartesian product can produce structures with multiple copies of each
label.  Insofar as we view labels as pointers or names for memory
locations, this allows \emph{explicitly} modelling value-level
sharing---this is explored more in \pref{sec:sharing}.

Of course, since Cartesian product is the categorical product in \Set,
Cartesian/Hadamard product is also the product in the category of
species.  Interestingly, there is a different notion of species
product (though not a categorical product) which is in some sense more
natural/useful than Cartesian product, even though it is more
complicated; it will be explored in the next section.

\todo{Forward reference to material on closedness?}

\todo{give some examples with other categories.}

\todo{\Set is distributive, in the sense that the canonical morphism
  $X \times Y + X \times Z \to X \times (Y + Z)$ is an isomorphism.
  Is $[\B, \Set]$ distributive in the same way?  If so, does lifting
  monoids always preserve distributivity? Answers: yes, and yes.}

\section{Partitional/Cauchy product}
\label{sec:product}

There is another notion of product for species, the \term{partitional}
or \term{Cauchy} product, which is more generally useful than
Cartesian product, even though it is much more complex to define.  In
particular, when species are extended to labelled structures
(\pref{chap:labelled}) it is the partitional product, rather than
Cartesian, which gives rise to the usual notion of product on
algebraic data types.  For this reason partitional product is
often simply referred to as ``product'', without any modifier,
although as we have seen it is Cartesian product, rather than
partitional product, which is actually a categorical product.

\begin{defn}
  The partitional product $F \sprod G$ of two species $F$ and $G$
  consists of paired $F$- and $G$-shapes, but with a twist: instead of
  being replicated, as in Cartesian product, the labels are
  \emph{partitioned} between the two shapes (\pref{fig:product}).
\end{defn}
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

%%% XXX remove me
\newcommand{\under}[1]{\floor{#1}}
\newcommand{\lift}[1]{\ceil{#1}}
\newcommand{\lab}[1]{\langle #1 \rangle}
\newcommand{\LStr}[3]{#1 #2 #3}

\begin{equation*}
  (F \sprod G)\ L = \sum_{L_1 \uplus L_2 = L} F\ L_1 \times G\ L_2
\end{equation*}
The intuition behind partitioning the labels in this way is that each
label represents a unique ``location'' which can hold a data value, so
the locations in the two paired shapes should be disjoint.

Generalizing partitional product over arbitrary functor categories is
much more complex than generalizing sum and Cartesian product, and
requires turning to a construction known as \term{Day convolution}.

\section{Day convolution}
\label{sec:day-convolution}

The essential idea of Day convolution, first described by Brian
Day~\cite{day-convolution}, is to construct a monoidal structure on a
functor category $[\Lab, \Str]$ out of a monoidal structure on the
\emph{domain} category $\Lab$.  In particular, Day convolution
requires
\begin{itemize}
\item a monoidal structure $\oplus$ on $\Lab$;
\item that $\Lab$ be \emph{enriched over} $\Str$, \ie there is a way
  to interpret morphisms in $\Lab$ as objects in $\Str$;
\item a symmetric monoidal structure $\otimes$ on $\Str$;
\item that $\Str$ be \todo{(finitely?)} cocomplete, and in particular
  have coends.
\end{itemize}

\bay{Maybe don't use same letter $L$ for generic definition as we do for $L
  \in \B$?}
\begin{defn}
  Given the above conditions, the Day convolution product of $F, G \in
  [\Lab, \Str]$ is given by \[ (F \oast G)\ L = \int^{L_1, L_2} F\ L_1
  \otimes G\ L_2 \otimes \Lab(L_1 \oplus L_2, L). \]
\end{defn}
\todo{Make sure I got all of this right.}

\todo{Explain.  Give some intuition.}

\todo{Instantiate with $\B$ and $\Set$, show they have the right
  properties, and show where partitional product comes from.}

\todo{Turn the following paragraph into an example with different
  categories}

Another
good way to gain intuition is to imagine indexing species not by label
types, but by natural number sizes.  Then it is easy to see that we
would have \[ (F \sprod G)_n \defeq \sum_{n_1, n_2 : \N} (n_1 + n_2 = n)
\times F_{n_1} \times G_{n_2}, \] that is, an $(F \sprod G)$-shape of
size $n$ consists of an $F$-shape of size $n_1$ and a $G$-shape of
size $n_2$, where $n_1 + n_2 = n$.  Indexing by labels is a
generalization (a \emph{categorification}, in fact) of this
size-indexing scheme, where we replace natural numbers with finite
types, addition with coproduct, and multiplication with product.

\todo{Do example with $\P$.}

\todo{Show that $\BT/\PT$ along with \Type\ have the right properties,
instantiate framework to show how it comes out.}

\section{Arithmetic product}
\label{sec:arithmetic-product}

There is another monoidal structure on $\B$ (and similarly on $\P$ and
$\N$) corresponding to the \emph{product} of sets/natural numbers.
What happens if we instantiate the framework of Day convolution with
this product-like monoidal structure instead of the coproduct-like
structure used to define partitional product?

\bay{How can we say that we are using ``the same'' ``product-like''
  monoidal structure in all these different categories?  Are they
  related by monoidal functors?}

Beginning with a simple example, \todo{example using $\N$}

Using the standard formulation of the category of species as $[\B,
\Set]$, we get \todo{finish. This is called \term{arithmetic product},
and was recently described by (XXX cite), although they say nothing
about Day convolution.}

\todo{pictures, intuition.}

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
are small.  Since $\Set$ and $\Type$ are both complete \todo{check: is
  $\Type$ complete?  What does this mean, type-theoretically?}  and
Cartesian closed, we conclude that both the skeletonized category
$[\P,\Set]$ of traditional species and its type-theoretic counterpart
$[\PT, \Type]$ are complete and Cartesian closed as well.

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
-^G$ between products and exponentials, which gives us a natural
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

\todo{picture.  Two cases with identical shapes but ``interacting''
  differently.}

Practically speaking, this result tells us how to express an
eliminator for $(F \times G)$-shapes. \todo{Elaborate on this.}

Note that $[\B, \Set]$ \emph{is} actually Cartesian closed, since it
is isomorphic to $[\P, \Set]$.  \todo{Check this for sure.}  The above
derivations can be carried out in the context of $[\B, \Set]$ as well,
with similar results.  Intuitively, $\B$ ``appears to be too big on
the surface'', but is saved by virtue of being isomorphic to a small
category.  In a sense, $\P$ is what is ``really going on''; $\B$ is
like $\P$ with lots of ``extra junk'' thrown in because it's
convenient to talk about \emph{sets} of labels rather than having to
work with the canonical set $\{0, \dots, n-1\}$ all the time.  This is
quite a special property of $\B$; for example, $\Set$ is certainly not
isomorphic to any small categories. The same argument shows that
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
\todo{$\Str/A$ inherits coproducts.} \todo{Can define a product
  structure on $\Str/A$ if $A$ is a ring object (???)  Note according
  to \url{http://ncatlab.org/nlab/show/internalization} we just need
  finite products to internalize the notion of a ring.}

\section{Virtual species}
\label{sec:virtual}

\todo{Do virtual species fit too?}