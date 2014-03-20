%% -*- mode: LaTeX; compile-command: "mk" -*-

%include thesis.fmt

\chapter{Combinatorial species}
\label{chap:species}

\todo{Gentler introduction, with some more intuition (and examples?),
  explanation of the diagrams, and pointers to further reading.}

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
species.  Given species $F, G : \B \to \Set$, we may form their sum $F
+ G$, defined on objects by \[ (F + G)\ L \defeq F\ L + G\ L, \] where
the $+$ on the right hand side denotes disjoint union of sets.  That
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

We may also define the \term{zero} or \term{empty} species, $\Zero$,
as the unique species with no shapes whatsoever, that is,

\begin{equation*}
  \Zero\ L \defeq \varnothing
\end{equation*}

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

\todo{Give some examples other than $\B \to \Set$.  $\PT \to
  \Type$. Simpler things.}

\section{Cartesian/Hadamard product}
\label{sec:cartesian}

Disjoint union is not the only monoidal structure on $\Set$. In
addition to coproducts $\Set$ also has products, where the product of
two sets $S$ and $T$ is given by the Cartesian product, $S \times T =
\{ (s,t) \mid s \in S, t \in T \}$, with any one-element set as the
identity.  By the discussion of the previous section, this
automatically lifts to a pointwise product structure on species, known
as the Cartesian or Hadamard product: \[ (F \times G)\ L = F\ L \times
G\ L. \]  In the same way that an $(F + G)$-shape is either an
$F$-shape \emph{or} a $G$-shape on a given set of labels, an $(F
\times G)$-shape is both an $F$-shape \emph{and} a $G$-shape, on
\emph{the same set of labels}.

Lifting the identity element pointwise gives the species $\E\ L =
\{\star\}$, usually called the species of sets, which is the identity
for Cartesian product of species. \todo{Give more intuition here.}

Cartesian product can produce structures with multiple copies of each
label.  Insofar as we view labels as pointers or names for memory
locations, this allows \emph{explicitly} modelling value-level
sharing---this is explored more in \pref{sec:sharing}.

Of course, since Cartesian product is the categorical product in \Set,
Cartesian/Hadamard product is also the product in the category of
species.  Interestingly, there is a different notion of species
product (though not a categorical product) which is in some sense more
natural/useful than Cartesian product, even though it is much more
complicated; it will be explored in the next section.

In addition to having products, \Set is Cartesian closed. However,
lifting does not necessarily preserve closedness.  In particular, the
category $[\B, \Set]$ of species is not Cartesian closed---we cannot
(in general) model function types with species. \todo{Though we can in
  some specific situations---see ...?}

\todo{give some examples with other categories.}

\todo{\Set is distributive, in the sense that the canonical morphism
  $X \times Y + X \times Z \to X \times (Y + Z)$ is an isomorphism.
  Is $[\B, \Set]$ distributive in the same way?  If so, does lifting
  monoids always preserve distributivity? Answers: yes, and yes.}

\section{Partitional/Cauchy product}
\label{sec:product}

\section{Day convolution}
\label{sec:day-convolution}

\section{Arithmetic product}
\label{sec:arithmetic-product}

\section{Composition}
\label{sec:composition}

\section{Differentiation}
\label{sec:differentiation}
