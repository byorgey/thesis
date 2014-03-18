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
$\size S$. However, a morphism $S \bij T$ must be sent to some bijection
$[\size S] \bij [\size T]$, and intuitively we have no way to pick one: we
would need to decide on a way to match up the elements of each set $S$
with the set of natural numbers $[\size S]$.  In a sense it ``does not
matter'' what choice we make, since the results will be isomorphic in
any case, and this is precisely where the axiom of choice comes in.

\todo{Note that HoTT can express several variants on AC.  Some are
inherently non-constructive so we do not want to assert them.  Note
there is one variant which is simply provable, but in order to apply
it we need to already have evidence of a correspondence between
arbitrary finite sets and canonical finite sets of the same size.}

This leads us to the need for \emph{computational evidence of
  finiteness}.  (Even the phrase ``send each set $S$ to its size
$\size S$'' should have been suspect before.  Where does this size
actually come from?)

First, we define a counterpart to $\P$ in type theory:
\begin{defn}
  $\P_H$ is the groupoid where
  \begin{itemize}
  \item the objects are natural numbers, that is, values of type $\N$, and
  \item the morphisms $n \to n$ are equivalences of type $\Fin n \iso
    \Fin n$.
  \end{itemize}
\end{defn}

\newcommand{\tygrpd}[1]{\ensuremath{\mathbf{G}(#1)}}

We now note the general principle that any type $T$ gives rise to a
groupoid $\tygrpd{T}$ where the objects are values $a : T$, and
$\tygrpd{T}(a,b) \defeq a = b$, that is, morphisms from $a$ to $b$ are
paths $p : a = b$.  As a first try at defining a constructive
counterpart to $\B$, we consider $\tygrpd{\FinType}$, where
\[ \FinType \defeq (A : \Type) \times (n : \N) \times (\Fin n \iso
A). \] However, this does not work: the explicit evidence of
finiteness is too strong, and interferes with the groupoid
structure. \todo{Explain why.  Can show there is at most one
  inhabitant of $A = B$ for $A, B : \FinTypeT$.  Use triangle
  picture.}

The next thing to try is thus $\tygrpd{\FinTypeT}$, where \[ \FinTypeT
\defeq (A : \Type) \times (n : \N) \times \ptrunc{\Fin n \iso A} \]
This does give us the right groupoid structure, and we can prove that
it is equivalent to $\P_H$---as long as equivalence of categories is a
mere proposition! \todo{explain why} Equivalence as a mere proposition
is not all that useful, however. We want to define a functor
$\tygrpd{\FinTypeT} \to \P_H$ that we can actually compute with, but
we cannot since it needs the equivalences in a computationally
relevant way.

In the end, we are forced to give up on constructing a groupoid via
$\tygrpd{-}$, and define $\B_H$ as follows.

\begin{defn}
$\B_H$ is the groupoid where
\begin{itemize}
\item the objects are values of type $\FinType \defeq (A : \Type) \times (n : \N)
\times (\Fin n \iso A)$, and
\item morphisms $(A,m,i) \to (B,n,j)$ are equivalences $A \iso B$.
\end{itemize}
\end{defn}

That is, morphisms simply ignore the equivalences contained in
objects.

\todo{Note we can easily show sizes must be equal.}

\begin{rem}
  \bay{We're in a funny situation where we have to add a lot of
    computational evidence to avoid using the axiom of choice---but
    then the next minute we turn around and say that it's irrelevant
    after all.  The way to think about it is ???}
\end{rem}

\begin{prop}
  There is a functor $\size - : \B_H \to \P_H$ which together with
  $[-] : \P_H \to \B_H$ defines a (strong) equivalence.

\begin{proof}
  \todo{prove it.}
\end{proof}
\end{prop}
