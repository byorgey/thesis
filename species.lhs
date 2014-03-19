%% -*- mode: LaTeX; compile-command: "mk" -*-

%include polycode.fmt

\chapter{Combinatorial species}
\label{chap:species}

\todo{Gentler introduction, with some more intuition (and examples?),
  and pointers to further reading.}

Species are defined as functors $\B \to \Set$ \citep{bll}.
Intuitively, the action of a species on objects takes a finite set of
``labels'' to a set of ``structures''; the action on morphisms
requires the action on objects to be ``invariant under relabelling''.

This is a simple and convenient definition, but there are several
reasons that compel us to generalize it.  First, $\B$ and $\Set$ enjoy
many special properties as categories (for example, $\Set$ is
cartesian closed, has all limits and colimits, and so on).  It is
enlightening to see precisely which properties are required in which
situations, and we miss this entirely if we start with the kitchen
sink.

More subtly, we wish to work in a constructive, computational setting,
and the specific categories $\B$ and $\Set$ are
inappropriate. \todo{reference stuff from finiteness section
  previously.}  We will wish to work with more computationally
concrete categories based in type theory, such as $\BT$, but in order
to do so we need to show that they have the right properties.

\section{Species from scratch}
\label{sec:species-scratch}

The idea is to start ``from scratch'' and build up a generic notion of
species which supports the operations we want.  Along the way, we will
also get a much clearer picture of where the operations ``come from''.

\newcommand{\Lab}{\bbb{L}}
\newcommand{\Str}{\bbb{S}}

We begin by considering functor categories in general.  Given two
categories $\Lab$ and $\Str$, what can we say about functors $\Lab \to
\Str$, and more generally about the functor category $[\Lab, \Str]$?
Of course, there is no point in calling functors $\Lab \to \Str$
``species'' for just any old categories $\Lab$ and $\Str$.  But what
properties must $\Lab$ and $\Str$ possess to make this interesting and
worthwhile?

\todo{should talk about motivation from memory locations and structures.}

\section{Products and coproducts}
\label{sec:prod-coprod}

Our first observation is that if $\Str$ has a monoidal structure, it
is straightforward to lift it to a monoidal structure on $[\Lab,
\Str]$, where the definitions are all pointwise. (This is exactly the
same idea as the Haskell type class instance |Monoid a => Monoid (e ->
a)|, but quite a bit more general.)  Moreover, products and coproducts
on $\Str$ lift to products and coproducts on $[\Lab, \Str]$.

Concretely, consider $\Str = \Set$, which has both products and
coproducts.  Lifting coproducts on \Set\ pointwise to $[\B,\Set]$
yields a coproduct operation on species: \todo{Writing here}

\begin{itemize}
\item Develop more general definitions along the way.  Applies not
  just to \Set\ but also to category of types and functions, etc.
\item Lifting monoidal structure from $C$: sum, Cartesian/Hadamard product.
\item Day convolution.  Cauchy product.  Arithmetic product.
\item Composition.
\end{itemize}
