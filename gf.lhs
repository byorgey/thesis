%% -*- mode: LaTeX; compile-command: "mk" -*-

\chapter{Generating functions}
\label{chap:gfs}

\bay{Whether this chapter will actually end up being included depends
  on available time, how much other material there is, etc.  At any
  rate it would still need a bunch more work.  I certainly plan to
  flesh this out and publish it at some point, whether or not it goes
  in my thesis.}

\setcounter{section}{-1}
\section{Introduction and motivation}
\label{sec:motivation}

Show some example Haskell code for \emph{e.g.} enumerating values of
algebraic data types, or \emph{e.g.} for computing isomorphism with
$\N$.  Question: how do we extend this to certain types of non-regular
structures involving composition (\emph{e.g.} permutations = nonempty
sets of cycles?).  Give some intuition why this is nonobvious and
hard.

Corresponds to the observation that ogfs/egfs do not preserve
composition for non-regular species.  In combinatorics, solved by
generalizing both to \emph{cycle index series}.  Idea: give
a framework for interpreting generating functions computationally, and
show how to extend it all the way to cycle index series.  Then the
algorithms we want will just ``fall out'' (at least, that is the hope!).

\section{Semirings}
\label{sec:intro}

For the purposes of this note, a \emph{semiring} $(S,+,0,\cdot,1)$ is
a type $S$ equipped with binary operations $+$ and $\cdot$ such that
$(S,+,0)$ is a commutative monoid, $(S,\cdot,1)$ is a monoid, $0 \cdot
a = a \cdot 0 = 0$, and $\cdot$ distributes over $+$.  As usual, we
will often abuse notation and denote a semiring simply by its carrier
type $S$ when the operations are clear from context.  We also
sometimes omit $\cdot$ and denote multiplication by juxtaposition, $a
\cdot b = ab$.

Examples of semirings (some of which will play an important role later)
include:
\begin{itemize}
\item Booleans under disjunction and conjunction, $(\B, \lor, \False,
  \land, \True)$.
\item Natural numbers under addition and multiplication,
  $(\N,+,0,\cdot,1)$.
\item Integers under addition and multiplication, $(\Z,+,0,\cdot,1)$.
\item The integers (or naturals), adjoined with $-\infty$, under
  maximum and addition, $(\Z \cup \{-\infty\},\max,-\infty,+,0)$.
\item Finite sets under disjoint union and cartesian product,
  $(\FinSet, \uplus, \varnothing, \times, \{\star\})$.  (Note
  that the laws hold only up to isomorphism of sets.)
\end{itemize}

By a semiring \emph{homomorphism} $\phi : S \to T$ we mean simply a
function $S \to T$ which preserves all the semiring structure, that
is, $\phi(0_S) = 0_T$, $\phi(1_S) = 1_T$, $\phi(a + b) = \phi(a) +
\phi(b)$, and $\phi(ab) = \phi(a)\phi(b)$.  Observe, for
example, that we have the sequence of semiring homomorphisms
\[
\xymatrix{
  (\FinSet, \uplus, \varnothing, \times, \{\star\})
  \ar[d]^{||\param||} \\
  (\N,+,0,\cdot,1)
  \ar[d]^{> 0} \\
  (\B, \lor, \False, \land, \True)
}
\]
going from a set $S$, to its size $||S||$, to its inhabitation $||S||>0$.

\section{Formal power series}
\label{sec:power-series}

In connection with the theory of species, we typically consider formal
power series with coefficients taken from some numeric type like
natural numbers or integers.  However, there is nothing particularly
special about numbers in this context.  As is well-known, given any
semiring $S$ we may form the semiring $S[[x]]$ of formal power series
with coefficients in $S$, with addition and multiplication defined in
the usual way. In particular, $S[[x]]$ can be viewed as what we get by
adjoining a new distinguished element $x$ to $S$, and then taking the
completion to form a semiring over the resulting set.  Note also that
any semiring homomorphism $\phi : S \to T$ induces a homomorphism over
the associated semirings of formal power series, which we notate as
$\phi[[x]] : S[[x]] \to T[[x]]$ (that is, $\param [[x]]$ is an
endofunctor on the category of semirings).

In what follows, it will be useful to keep in mind a different (but
equivalent) formulation of formal power series: we view the formal
power series $S[[x]]$ as a \emph{function} $S[[x]] : \N \to S$, giving
the coefficient at each power of $x$.

\section{Ordinary generating functions and unlabelled species}
\label{sec:ogf}

To each species $F$ we associate an \term{ordinary generating
  function} (ogf), $\unl{F}(x)$, defined by \[ \unl{F}(x) = \sum_{n
  \geq 0} \unl{f}_n x^n, \] where $\unl{f}_n$ denotes the number of
\term{unlabelled $F$-structures} of size $n$, that is, the number of
equivalence classes of $F$-structures under relabelling.  This mapping
from species to ogfs is a semiring homomorphism, that is,
$(\unl{F+G})(x) = \unl F(x) + \unl G(x)$ and $(\unl{F \cdot G})(x) =
\unl F(x) \cdot \unl G(x)$.

The standard definition of a species is a functor $\B \to \FinSet$,
where $\B$ is the category of finite sets with bijections as
morphisms.  Unlabelled structures are equivalence classes of
(labelled) species structures.  Can view ``unlabelled species'' as
functors from discrete category $\N$ (the skeleton of $\B$)

\[
\xymatrix{
\B \ar[r] \ar[d]_{||\param||} & \FinSet \ar[d] \\
\N \ar[r] & \FinSet
}
\]

View species definition itself, $\B \to \FinSet$, as a generating
function $\N \to \FinSet$ with canonically-labeled structures.  (Can
recover action on all of $\B$ from action on $\N$, since $\N$ as
discrete category is the skeleton of $\B$.) (Q: are these naturally
isomorphic as functors?) Then the well-known mapping to ogfs arises as
the semiring homomorphism on formal power series induced by the
semiring homomorphism on the coefficients, $||\param|| : (\FinSet,
\uplus, \times, \varnothing, \{\star\}) \to (\N,+,\cdot,0,1)$. (Is
this quite right?  There's a factor of $n!$ to deal with somewhere.)

We then consider other semiring homomorphisms to and from $\FinSet$,
and discover we can churn out algorithms to compute things about
unlabelled species simply by designing the proper semiring +
homomorphism and transporting the species-expression-as-ogf along the
induced ogf homomorphism. (Many of these algorithms are well-known
and/or ``obvious''.) Exhibit some Haskell code.

However, this only works for ogfs. (Can we use theory of semiring
homomorphisms etc. to show why ogfs break down when trying to handle
unlabelled non-regular species?) The idea is to generalize this
entire analysis from ogfs to egfs and cycle index series, which
requires generalizing the notion of semiring.

\section{Sized semirings}
\label{sec:indexed-semirings}

\emph{Sized semirings} are a generalization of semirings where the
elements have types indexed by a natural number (their ``size'').  In
particular, a sized semiring consists of
\begin{itemize}
\item A type family $S : \N \to \universe$ (where \universe\ denotes
  the universe of types). We use subscripts to denote applications of
  $S$, as in $S_n$.
\item A binary operation $\_ + \_ : \dep{n:\N} S_n \to S_n \to S_n$.
  We usually omit the size argument when it is clear from context.
\item A distinguished family of elements $0 : \dep{n:\N} S_n$.  We
  write $0_n$ when we wish to be explicit about the size, but usually
  omit it.
\item A binary operation $\_ \cdot \_ : \dep{m, n : \N} S_m \to S_n \to
  S_{m+n}$.  We usually omit the size arguments.
\item A distinguished element $1 : S_0$.
\end{itemize}
Moreover, these are subject to laws analogous to the laws of a
semiring, listed below.  Sizes are indicated by subscripts; all free
variables (including sizes) are implicitly universally quantfied.
\begin{itemize}
\item $0_n + s_n = s_n + 0_n = s_n$ \hfill ($0$ is an
  identity for $+$)
\item $(s_n + t_n) + u_n = s_n + (t_n + u_n)$ \hfill (Associativity of $+$)
\item $s_n + t_n = t_n + s_n$ \hfill
  (Commutativity of $+$)
\item $0_m \cdot s_n = s_n \cdot 0_m =
  0_{m+n}$ \hfill ($0$ is an annihilator for $\cdot$)
\item $1 \cdot s_n = s_n \cdot 1 = s_n$ \hfill ($1$ is an identity for
  $\cdot$)
\item $(s_m \cdot t_n) \cdot u_p = s_m \cdot (t_n \cdot
  u_p)$ \hfill (Associativity of $\cdot$)
\item $s_m \cdot (t_n + u_n)
  = s_m \cdot t_n + s_m \cdot u_n$ \hfill (Left distributivity)
\item $(t_n + u_n) \cdot s_m
  = t_n \cdot s_m + u_n \cdot s_m$ \hfill (Right distributivity)
\end{itemize}

We can make any semiring $S$ into a sized semiring $R$ by putting a
copy of $S$ at every size, that is, by defining $R_n \defeq S$, and
taking the binary operations of $R$ to be those of $S$, ignoring the
sizes.  In fact, we can see semirings as precisely those sized
semirings where $+$, $\cdot$, and $0$ are defined uniformly over all
sizes.

For a more interesting example of a sized semiring, consider the
following definition of the \term{binomial semiring}, $B$. We begin
with a copy of the natural numbers at each size, $B_n \defeq \N$, and
take the usual $0$, $1$, and $+$, defined uniformly for all sizes. For
the product operation, however, we define \[ \cdot_B = \fun {m, n :
  \N} \fun {a : B_m} \fun {b : B_n} \binom{m+n}{m} \cdot a \cdot b \]
where the product operations on the right-hand side are the usual
product of natural numbers.  For example, $4_2 \cdot_B 7_3 =
\binom{5}{2} 28 = 280$.  It is not hard to show that this satisfies
the sized semiring laws.

The analogue of generating functions over a sized semiring $S$ are
dependent functions $\dep{n:\N} S_n$ (instead of $\N \to S$ for
semirings).  The type of such generating functions over a sized
semiring $S$ is also denoted $S[[x]]$; this should not cause confusion
since it will usually be clear whether $S$ denotes a usual or a sized
semiring.

\section{Exponential generating functions}
\label{sec:egfs}

Exponential generating functions (egfs) represent a sequence $f_0,
f_1, f_2, \dots$ by an infinite polynomial \[ F(x) = \sum_{n \geq 0}
f_n \frac{x^n}{n!}. \] Given the previous developments, we can now
view egfs as elements of the semiring $B[[x]]$ of formal power series
over the (sized) binomial semiring $B$.  To see this, it suffices to
note that
\begin{align*}
  F(x) G(x)
    &= \left(\sum_{n \geq 0} f_n \frac{x^n}{n!}\right) \left(\sum_{n \geq 0}
      g_n \frac{x^n}{n!}\right) \\
    &= \sum_{n \geq 0} \sum_{0 \leq k \leq n} \frac{f_k}{k!}
    \frac{g_{n-k}}{(n-k)!} x^n \\
    &= \sum_{n \geq 0} \left(\sum_{0 \leq k \leq n} \binom{n}{k} f_k
      g_{n-k} \right) \frac{x^n}{n!} \\
    &= \sum_{n \geq 0} \left(\sum_{0 \leq k \leq n} f_k \cdot_B
      g_{n-k} \right) \frac{x^n}{n!}
\end{align*}

Exhibit the sized semiring homomorphism
$\FinSet \to B$ which induces the homomorphism from species to egfs.
Talk about other homomorphisms, algorithms on labelled species, etc.

However, we still can't handle unlabelled species in all generality
(Q: can we show why using this framework?).  For that we have to
generalize to cycle index series.

\section{Indexed semirings}
\label{sec:gen-indexed-semirings}

\term{Indexed semirings} represent a further generalization of sized
semirings.  Instead of indexing by a natural number size, we index by
an arbitrary monoid.  In detail, an indexed semiring consists of
\begin{itemize}
\item A monoid $(\I, \oplus, \varepsilon)$.  Elements $i,j \in \I$ are
  called \term{indices}.
\item A type family $S : \I \to \universe$, where applications of $S$
  are again denoted using subscripts, $S_i$.
\item A binary operation $\_ + \_ : \dep{i:\I} S_i \to S_i \to S_i$.
\item A distinguished family of elements $0 : \dep{i:\I} S_i$.
\item A binary operation $\_ \cdot \_ : \dep{i,j:\I} S_i \to S_j \to
  S_{i \oplus j}$.
\item A distinguished element $1 : S_\varepsilon$.
\end{itemize}
In addition, indexed semirings are subject to laws exactly parallel to
those for sized semirings, in such a way that every sized semiring is
automatically an indexed semiring indexed by $(\N,+,0)$.

Use this to do the appropriate thing for cycle index series, indexed
by\dots integer partitions (???)

The hope is that some non-obvious algorithms will ``fall out'' of
this, for e.g. enumerating unlabelled non-regular species.

\section{Questions}
\label{sec:questions}

Questions for further consideration:

\begin{itemize}
\item It seems like weighted species ought to fit nicely into this
  framework.  Do they?  What are the details?
\item Can we fit Boltzmann sampling into this framework too?
  \emph{e.g.} do Boltzmann samplers have a semigroup structure?
\end{itemize}

\section{Test}

\begin{equation}
  \label{eq:foo}
  4 = 2 + 2
\end{equation}

Blah blah \pageref{eq:foo}.