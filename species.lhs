%% -*- mode: LaTeX; compile-command: "mk" -*-

%include polycode.fmt

\chapter{Combinatorial species}
\label{chap:species}

\begin{itemize}
\item Motivate application of the theory of species by starting
  (mostly) ``from scratch'' and building up the pieces of the theory
  we need.
\end{itemize}

\begin{itemize}
\item Develop more general definitions along the way.  Applies not
  just to \Set\ but also to category of types and functions, etc.
\item Lifting monoidal structure from $C$: sum, Cartesian/Hadamard product.
\item Day convolution.  Cauchy product.  Arithmetic product.
\end{itemize}

\section{Foundations}
\label{sec:foo}

Denote by $\B$ the category whose objects are finite sets and whose
morphisms are bijections between finite sets.  Species are then
defined as functors $\B \to \Set$.  Intuitively, the action of a
species on objects takes a finite set of ``labels'' to a set of
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
and the specific categories $\B$ and $\Set$ are inappropriate. As an
example XXX

Let $[n] = \{0, \dots n-1\}$ be the set of the first $n$ natural
numbers.  Denote by $\P$ the category whose objects are natural
numbers and whose morphisms $n \to n$ are bijections $[n] \bij [n]$
(with no morphisms $m \to n$ for $m \neq n$).  Often it is noted as a
triviality not requiring proof that $\P$ is equivalent to (in fact, a
skeleton of) $\B$ and hence we are justified in working with $\P$
rather than $\B$ when convenient.

However, upon digging a bit deeper it is not quite so trivial: in
particular, showing that $\P$ and $\B$ are (strongly) equivalent
requires the axiom of choice.  In more detail, it is easy to define a
functor $[-] : \P \to \B$ which sends $n$ to $[n]$ and preserves
morphisms.  Defining an inverse functor $\B \to \P$ is more
problematic. Clearly we must send each set $S$ to its size
$\#S$. However, a morphism $S \bij T$ must be sent to some bijection
$[\#S] \bij [\#T]$, and intuitively we have no way to pick one: we
would need to decide on a way to match up the elements of each set $S$
with the set of natural numbers $[\#S]$.  In a sense it ``does not
matter'' what choice we make, since the results will be isomorphic in
any case, and this is precisely where the axiom of choice comes in.

Note that HoTT can express several variants on AC.  Some are
inherently non-constructive so we do not want to assert them.  Note
there is one variant which is simply provable, but in order to apply
it we need to already have evidence of a correspondence between
arbitrary finite sets and canonical finite sets of the same size.

This leads us to the need for \emph{computational evidence of
  finiteness}.  (Even the phrase ``send each set $S$ to its size
$\#S$'' should have been suspect before.  Where does this size
actually come from?)

First, we define $\P_H$ to be the category whose objects are natural
numbers (in HoTT, that is, values of type $\N$) and whose morphisms
are of the form $\Fin n \iso \Fin n$.

\newcommand{\tygrpd}[1]{\ensuremath{\mathbf{G}(#1)}}

We now note the general principle that any type $T$ gives rise to a
groupoid $\tygrpd{T}$ where the objects are values $a : T$, and
$\tygrpd{T}(a,b) \defeq a = b$, that is, morphisms from $a$ to $b$ are
paths $p : a = b$.  As a first try at defining a constructive
counterpart to $\B$, we define $\B_H' \defeq \tygrpd{\FinType'}$, where
\[ \FinType' \defeq (A : \Type) \times (n : \N) \times (\Fin n \iso
A). \] However, this does not work.  XXX explain why.

We could also try defining \[ \FinType \defeq (A : \Type) \times (n :
\N) \times \ptrunc{\Fin n \iso A} \] \todo{finish}

\bay{Does $\tygrpd{\FinType}$ actually work?  We can prove it is
  equivalent to $\P_H$, if we state equivalence of categories as a
  mere proposition.  However, we can't actually define a functor
  $\tygrpd{\FinType} \to \P_H$ (except internally to the proof),
  because it needs the isos in a computationally relevant way.  The
  other thing we could do is define a groupoid whose objects are
  values of $\FinType'$, but where a morphism $(A,m,i) \to (B,n,j)$ is
  a path $A = B$ (or an equivalence $A \iso B$).  There would still be
  some work to prove these functors form a (strong) equivalence of
  categories.}

