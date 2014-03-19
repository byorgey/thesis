%% -*- mode: LaTeX; compile-command: "mk" -*-

%include polycode.fmt

\chapter{Combinatorial species}
\label{chap:species}

Denote by $\B$ the category whose objects are finite sets and whose
morphisms are bijections between finite sets.  Species are then
defined as functors $\B \to \Set$ \citep{bll}.  Intuitively, the action
of a species on objects takes a finite set of ``labels'' to a set of
``structures''; the action on morphisms requires the action on objects
to be ``invariant under relabelling''.

This is a simple and convenient definition, but there are several
reasons that compel us to generalize it.  First, $\B$ and $\Set$ enjoy
many special properties as categories (for example, $\Set$ is
cartesian closed, has all limits and colimits, and so on).  It is
enlightening to see precisely which properties are required in which
situations, and we miss this entirely if we start with the kitchen
sink.

More subtly, we wish to work in a constructive, computational setting,
and the specific categories $\B$ and $\Set$ are inappropriate.  Before
returning to generalize species, we must take a small detour to see
one reason why $\B$ is inappropriate in a computational setting, and
the definitions of some more appropriate tools.

\section{Species from scratch}
\label{sec:species-scratch}

\begin{itemize}
\item Motivate application of the theory of species by starting
  (mostly) ``from scratch'' and building up the pieces of the theory
  we need.
\item Develop more general definitions along the way.  Applies not
  just to \Set\ but also to category of types and functions, etc.
\item Lifting monoidal structure from $C$: sum, Cartesian/Hadamard product.
\item Day convolution.  Cauchy product.  Arithmetic product.
\item Composition.
\end{itemize}
