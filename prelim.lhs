%% -*- mode: LaTeX; compile-command: "mk" -*-

%include polycode.fmt

\chapter{Preliminaries}
\label{chap:prelim}

The main content of this dissertation builds upon a great deal of
mathematical formalism, particularly from set theory, category theory,
and type theory.  To say that this chapter attempts to make the
dissertation ``self-contained'' would be ludicrous, not to mention
disheartening to those readers who find there are still gaps between
this document's assumptions and their background knowledge.  Rather,
the purpose of this chapter is to provide a brief overview of the
necessary technical background, giving definitions, important
intuitions, and references for further reading.  Readers who merely
need to fill in a few gaps may find such brief treatments sufficient;
it is hoped that readers with less background will find it a useful
framework and source of intuition for furthering their own learning,
making use of the provided references to read about things not covered
here.

The material in \pref{sec:basic}, \pref{sec:HoTT}, and
\pref{sec:category-theory}, though by no means basic, is fairly
standard, so readers with a good background in the subjects covered
may safely skip them without too many surprises.  Even those readers
who are not familiar with some of the material may find it more
productive to begin reading \pref{chap:species} and refer back to this
chapter as needed. On the other hand, the material in
\Sect\Sect\ref{sec:AC}--\ref{sec:finiteness} is somewhat less
standard, and it is hoped that all readers, even experts, will gain
something from them.

\section{Basic notations}
\label{sec:basic}

The set of \term{natural numbers} is denoted $\N = \{0, 1, 2,
\dots\}$.  The \term{size} or \term{cardinality} of a finite set $X$,
a natural number, is denoted $\size X$ (rather than the more
traditional $||X||$, since that notation is used as the introduction
form for propositional truncation; see \pref{sec:HoTT}). Given a
natural number $n \in \N$, the canonical size-$n$ prefix of the
natural numbers is denoted $\fin n = \{0, \dots, n-1\}$.

Given a function $f : A \to B$, an element $b \in B$, and subsets $X
\subseteq A$ and $Y \subseteq B$,
\begin{itemize}
\item $f(X) = \{ f(a) \mid a \in X \}$ denotes the image of $X$
under $f$;
\item $f^{-1}(b) = \{ a \in A \mid f(a) = b \}$ denotes the preimage or
  inverse image of $b$;
\item $f^{-1}(Y) = \Union_{b \in Y} f^{-1}(b) = \{ a \in A \mid f(a) \in Y
  \}$ likewise denotes the preimage of an entire set.
\end{itemize}

Metavariable conventions used throughout this dissertation include:
\begin{itemize}
\item Metavariables $f$, $g$, $h$ range over functions.
\item Greek metavariables (especially $\alpha$, $\beta$, $\sigma$,
  $\tau$, $\phi$, $\psi$) often range over bijections.
\item Blackboard bold metavariables (\eg $\C$, $\D$, $\E$) range over
  categories.
\item Names of specific categories use boldface ($\Set$, $\Cat$,
  $\Spe$, $\B$, $\P$).
\item Names of certain type-theoretic constructs or categories use a
  calligraphic font ($\Type$, $\BT$, $\PT$).
\item Metavariables $K$, $L$ range over sets of labels (or, more generally, label
  objects).
\item Metavariables $F$, $G$, $H$ range over functors (and in particular
  over species).
\item Names of specific species use a sans-serif font ($\X$, $\Bag$,
  $\List$, $\Cyc$).
\end{itemize}

\section{Homotopy type theory}
\label{sec:HoTT}

\term{Homotopy Type Theory} (HoTT) is a recent variant of Martin-L\"of
type theory~\citep{martin1975intuitionistic, martin1984intuitionistic}
arising out of Vladimir Voevodsky's Univalent Foundations
program~\citep{voevodskyFoundations}.  There is not space to give a
full description here; in any case, given the existence of the
excellent HoTT Book~\citep{hottbook}, such a description would be
superfluous.  Instead, it will suffice to give a brief description of
the relevant parts of the theory, and explain the particular benefits
of carrying out this work in the context of HoTT.

Homotopy type theory, I will argue, is the \emph{right} framework in
which to carry out the work in this dissertation.  Intuitively, this
is because the theory of species is based centrally around groupoids
and isomorphism---and these are topics central to homotopy type theory
as well.  In a sense, HoTT is what results when one begins with
Martin-L\"of type theory (MLTT) and then takes issues of equality and
isomorphism---and in particular the principle of equivalence---very
seriously.

In more detail, some of the specific ways that the use of HoTT
benefits this work, to be explored in more detail later, include:
\begin{itemize}
\item HoTT gives a convenient framework for making formal the idea of
  ``transport'': using an isomorphism $\sigma : L_1 \bij L_2$ to
  functorially convert objects built from $L_1$ to ones built from
  $L_2$.  This is a fundamental operation in HoTT, and is also central
  to the definition of species (\pref{sec:species-definition}).  In
  fact, when constructing species with HoTT as a foundation, transport
  simply comes ``for free''---in contrast to using set theory as a
  foundation, in which case transport must be tediously defined (and
  proved correct) for each new species.
\item The \term{univalence axiom} and \term{higher inductive types}
  make for a rich notion of propositional equality, over which the
  ``user'' has a relatively high degree of control.  For example,
  using higher inductive types, it is easy to define various sorts of
  \emph{quotient types} which would be tedious to define and work with
  in MLTT.  For example, one particular manifestation of this general
  idea is the fact that \term{coends} in HoTT are just $\Sigma$-types
  (\pref{sec:ct-hott}).
\item \term{Propositional truncation} (explained below) is an
  important tool for properly modelling concepts from classical
  mathematics in a constructive setting.  In particular we use it to
  model the concept of \emph{finiteness} (\pref{sec:finiteness}).
\item Homotopy type theory allows doing category theory without using
  the axiom of choice (\pref{sec:AC}, \pref{sec:ct-hott}), which is
  important in a constructive or computational setting.
\end{itemize}

Although not the main goal of this work, I hope that it can serve
as a good example of the ``practical'' application of HoTT and its
benefits for programming.  Much of the work on HoTT has so far been
aimed at mathematicians---appropriately so, since they need more
convincing---but new foundations for constructive mathematics must
almost by necessity have profound implications for the foundations of
programming as well~\cite{martin1982constructive}.

We begin our brief tour of HoTT with its syntax.

\paragraph{Terms and types}

The theory includes standard constructions such as:
\begin{itemize}
\item an empty type \TyZero, with no inhabitants;
\item a unit type \TyOne, with inhabitant $\unit$;
\item sum types $A + B$, with constructors $\inl : A \to A + B$ and
  $\inr : B \to A + B$, as well as a $\cons{case}$ construct for doing
  case analysis;
\item dependent pairs $(x:A) \times B(x)$, with constructor $\pair -
  -$ and projection functions $\pi_1 : (x:A) \times B(x) \to A$ and
  $\pi_2 : (p : (x:A) \times B(x)) \to B(\pi_1 p)$;
\item dependent functions $(x:A) \to B(x)$; and
\item a hierarchy of type universes $\Type_0$, $\Type_1$,
  $\Type_2$\dots.
\end{itemize}
Following standard practice, universe level subscripts will usually be
omitted, with $\Type$ being understood to represent whatever universe
level is appropriate.

HoTT also allows inductive definitions.  For example, $\N :
\Type_0$ denotes the inductively-defined type of natural numbers, with
constructors $\zero : \N$ and $\suc : \N \to \N$, and $\Fin : \N \to
\Type_0$ denotes the usual indexed type of canonical finite sets, with
constructors $\fzero : \Fin (\suc n)$ and $\fsuc : \Fin n \to \Fin
(\suc n)$.

Although Agda notation~\cite{Agda} is mostly used for dependent pairs
and functions, the traditional notations $\sum_{x : A} B(x)$ and
$\prod_{x:A} B(x)$ (instead of $(x:A) \times B(x)$ and $(x:A) \to
B(x)$, respectively) are sometimes used for emphasis. As usual, the
abbreviations $A \times B$ and $A \to B$ denote non-dependent (\ie
when $x$ does not appear free in $B$) pair and function types,
respectively. \later{implicit quantification? Do we need this? Also,
  to reduce clutter, we sometimes make use of implicit quantification:
  free type variables in a type---like $A$ and $B$ in $A \times (B \to
  \N)$---are implicitly universally quantified, like $(A : \Type) \to
  (B : \Type) \to A \times (B \to \N)$.}

\paragraph{Equality}

HoTT distinguishes between two different types of equality:
\later{reference ``On the meanings of the logical constants'' or some
  other suitable thing talking about judgments vs propositions?}
\begin{itemize}
\item \term{Judgmental} equality, denoted $x \equiv y$, is defined via
  a collection of judgments stating when things are equal to one
  another, and encompasses things like basic rules of computation. For
  example, the application of a lambda term to an argument is
  judgmentally equal to its $\beta$-reduction.  Judgmental equality is
  reflexive, symmetric, and transitive as one would expect.
  Judgmental equality is a meta-property of the system; it is not
  possible to reason about or to prove judgmental equalities
  internally to HoTT.
\item \term{Propositional} equality.  Given $x, y : A$, we write $x
  =_A y$ for the proposition that $x$ and $y$ are equal (at the type
  $A$).  The $A$ subscript may also be omitted, $x = y$, when it is
  clear from the context. Unlike judgmental equality, where $x \equiv
  y$ is a \term{judgment}, the propositional equality $x = y$ is a
  \emph{type} whose inhabitants are evidence or \emph{proofs} of the
  equality of $A$ and $B$.  Thus propositional equalities can be
  constructed and reasoned about \emph{within} HoTT.  Inhabitants of
  $x = y$ are often called \term{paths} from $x$ to $y$; the
  intuition, taken from homotopy theory, is to think of paths between
  points in a topological space.

  Note that it is possible (and often useful!) to have nontrivial
  higher-order paths, \ie paths between paths, paths between paths
  between paths, and so on.
\end{itemize}

The structure of HoTT guarantees that functions are always functorial
with respect to propositional equality. That is, if $e : x = y$ is a
path between $x$ and $y$, and $f$ is a function of an appropriate
type, then it is possible to construct a proof that $f(x) = f(y)$ (or
a suitable analogue in the case that $f$ has a dependent type).  Given
$e : x = y$ we also have $P(x) \to P(y)$ for any type family $P$,
called the \term{transport} of $P(x)$ along $e$ and denoted
$\transport{P}{e}$, or simply $e_*$ when $P$ is clear from context.
For example, if $e : A = B$ then $\transport{X \mapsto X \times (X \to
  C)}{e} : A \times (A \to C) \to B \times (B \to C)$.

\paragraph{Equivalence and univalence}

There is also a third sort of equality, namely, \term{equivalence}.
An equivalence between $A$ and $B$, written $A \iso B$ is
(essentially) a pair of functions $f : A \to B$ and $g : B \to A$,
along with a proof that $f$ and $g$ are inverse.\footnote{The precise
  details are more subtle \cite[chap.  4]{hottbook}, but unimportant
  for the purposes of this work.  The key takeaway is that $A \iso B$
  both implies and is implied by the existence of an inverse pair of
  functions, although this does not make a good \emph{definition} of
  equivalence because of problems with coherence of higher paths.}
$\id$ and $\comp$ denote the identity equivalence and equivalence
composition, respectively.  As a notational shortcut, equivalences of
type $A \iso B$ can be used as functions $A \to B$ where it does not
cause confusion.

HoTT's main novel feature is the \emph{univalence axiom}, which states
that equivalence is equivalent to propositional equality, that is, $(A
\iso B) \iso (A = B)$. One direction, $(A = B) \to (A \iso B)$,
follows easily from the properties of equality; the interesting
direction, which must be taken as an axiom, is $\ua : (A \iso B) \to
(A = B)$, which formally encodes the \emph{principle of
  equivalence}~\cite{principle-of-equivalence}, namely, that sensible
properties of mathematical objects must be invariant under
equivalence.  Putting univalence together with transport means that
equivalent values are completely interchangeable.

Propositional equality thus takes on a meaning richer than the usual
conception of equality.  In particular, $A = B$ does not mean that $A$
and $B$ are \emph{identical}, but that they can be used
interchangeably---and moreover, interchanging them may require some
work, computationally speaking.  Thus an equality $e : A = B$ can have
nontrivial computational content, particularly if it is the result of
applying $\ua$ to some equivalence.

As of yet, univalence has no direct computational
interpretation\footnote{Though as of this writing there seems to be
  some good progress on this front via the theory of \term{cubical
    sets}~\cite{bezem2014model}.}, so using it to give a computational
interpretation of species may seem suspect. Note, however, that $\ua$
satisfies the $\beta$-like law \mbox{$\transport{X \mapsto X}{\ua(f)}
  = f$}. So univalence introduces no computational problems as long as
applications of $\ua$ are only ultimately used via
$\mathsf{transport}$.  In particular, sticking to this restricted
usage of $\ua$ still allows a convenient shorthand: packaging up an
equivalence into a path and then transporting along that path results
in ``automatically'' inserting the equivalence and its inverse in all
the necessary places throughout the term. For example, let $P(X)
\defeq X \times (X \to C)$ as in the previous example, and suppose $e
: A \iso B$, so $\ua\ e : A = B$.  Then $\transport P {\ua(e)} : P(A)
\to P(B)$, and in particular $\transport P {\ua(e)} \pair a g = \pair
{e(a)}{g \comp e^{-1}}$, which can be derived mechanically by
induction on the shape of $P$.

\paragraph{Propositions, sets, and $n$-types}

As noted previously, it is possible to have arbitrary higher-order
path structure: paths between paths, paths between paths between
paths, and so on.  This offers great flexibility but also introduces
many complications.  It is therefore useful to have a vocabulary for
explicitly talking about types with limited higher-order structure.

\begin{defn}
  A \term{proposition}, or \term{$(-1)$-type}, is a type for which any two inhabitants are
  propositionally equal.
\end{defn}

Intuitively, the only interesting thing that can be said about a
proposition is whether it is inhabited or not. Although it may have
many \emph{syntactically} different inhabitants, they are all equal
and hence internally indistinguishable.  Such types are called
``propositions'' since they model the way one usually thinks of
propositions in, say, first-order logic. There is no value in
distinguishing the different possible proofs of a proposition; what
counts is only whether or not the proposition is provable at all.

\begin{defn}
  A type $A$ is a \term{set}, or \term{$0$-type}, if there is (up to
  propositional equality) at most one path between any two elements;
  that is, more formally, for any $x, y : A$ and $p, q : x = y$, there
  is a path $p = q$.  Put another way, for any $x, y : A$, the type $x
  = y$ is a proposition.
\end{defn}
Most ``standard'' inductive types, \eg \N, \Fin n, and so on, are
sets, which can be proved via their induction principles.

As noted above, propositions and sets are also called, respectively,
$(-1)$-types and $0$-types.  As these names suggest, there is an
infinite hierarchy of $n$-types (beginning at $n = -2$ for historical
reasons) which have no interesting higher-order path structure above
level $n$.  As an example of a $1$-type, consider the type of all
sets, \[ \msf{Set} \defeq (A : \Type) \times \isSet(A), \] where
$\isSet(A) \defeq (x,y:A) \to (p,q:x = y) \to (p = q)$ is the
proposition that $A$ is a set.  Given two elements $A, B : \msf{Set}$
it is not the case that all paths $A = B$ are equal; such paths
correspond to bijections between $A$ and $B$, and there may be many
such bijections.

\paragraph{Truncation}

The last important concept from HoTT to touch upon is
\term{propositional truncation}.  If $A$ is a type, then $\ptrunc{A}$
is also a type, with an introduction form $\ptruncI - : A \to
\ptrunc{A}$ that allows injecting values of $A$ into $\ptrunc{A}$.
The crucial difference is that in addition to being able to construct
\emph{values} of $\ptrunc A$, there is also a way to construct
\emph{paths} between them: in particular, for any two values $x, y :
\ptrunc A$, there is a path $x =_{\ptrunc A} y$.  Thus, $\ptrunc A$ is
a copy of $A$ but with all values considered equal.  This is called
the \term{propositional truncation} of $A$ since it evidently turns
$A$ into a proposition, which can intuitively be thought of as the
proposition ``$A$ is inhabited''. If we have an inhabitant of $\ptrunc
A$, we know there must exist some inhabitant of $A$, but without
necessarily being able to tell what it is.

One of the most interesting aspects of propositional truncation is its
recursion principle: to construct a function $\ptrunc A \to P$, it
suffices to give a function $A \to P$, but \emph{only if $P$ is a
  proposition}.  In other words, one is allowed to ``look at'' the
value of type $A$ hidden inside a value of $\ptrunc A$, as long as one
``promises not to reveal the secret''.  Producing an inhabitant of a
proposition $P$ counts as such a promise, because it cannot ``leak''
any information about the precise inhabitant $a : A$. This is because,
up to propositional equality, there is at most one inhabitant of $P$,
and hence no opportunity to convey information.

Propositional truncation is also known as $(-1)$-truncation, and is
the bottom rung on a ladder of $n$-truncation operations.  The
$n$-truncation $\ptrunc{A}_n$ adds all paths at level $n$, effectively
``killing'' all higher-order path structure above that level and
turning $A$ into an $n$-type.  For example, the $0$-truncation
$\ptrunc{A}_0$ turns $A$ into a set, by adding paths not between
elements $a, b : A$, but between all pairs of parallel paths $p,q : a
= b$.

\section{Category theory}
\label{sec:category-theory}

This dissertation makes extensive use of category theory, which is the
natural language in which to explore species and related concepts.  A
full understanding of the contents of this dissertation requires an
intermediate-level background in category theory, but a grasp of the
basics should suffice to understand much of it.  In particular, a
quick introduction to necessary concepts beyond the bare fundamentals
is presented here, with useful intuition and references for further
reading.  It is hoped that this section can serve as a useful guide
for ``bootstrapping'' one's knowledge of category theory, for those
readers who are so inclined.

This section presents traditional category theory as founded on set
theory, to make it easy for readers to correlate it with existing
literature.  However, as explained in \pref{sec:ct-hott} and as
evidenced throughout this work, HoTT makes a much better foundation
for category theory than set theory does! \pref{sec:ct-hott}
highlights the most significant differences and advantages of
HoTT-based category theory; most of the other definitions and
inutition carry over essentially unchanged.

\subsection{Category theory fundamentals}
\label{sec:ct-fundamentals}

At a bare minimum, an understanding of the foundational trinity of
category theory (categories, functors, and natural transformations) is
assumed, along with some standard universal constructions such as
terminal and initial objects, products, and coproducts. For an
introduction to these concepts (and a much more leisurely introduction
to those sketched below), the reader should consult one of the many
excellent references on the subject \citep{lawvere2009conceptual,
  awodey2006category, pierce1991basic, barr1990category,
  mac1998categories}.

\paragraph{Standard categories}

We begin by listing some standard categories which will appear
throughout this work.
\begin{itemize}
\item $\cat{1} = \bullet$, the trivial category with a single object
  and only the required identity morphism.
\item $\cat{2} = \bullet \to \bullet$, the category with two objects
  and one nontrivial morphism between them (as well as the required
  identity morphisms).
\item $\disc{\cat{2}} = \bullet \phantom{\to} \bullet$, the discrete
  category with two objects and only identity morphisms. A
  \term{discrete} category is a category with only identity morphisms;
  $\disc{\C}$ denotes the discrete category with the objects of $\C$.
  Also, any set can be treated as a discrete category.
\item $\Set$, the category with sets as objects and (total) functions
  as morphisms.
\item $\FinSet$, like $\Set$ but with only finite sets as objects.
\item $\Cat$, the category of all small categories (a category is
  \term{small} if its objects and morphisms both form \emph{sets}, as
  opposed to proper classes; considering the category of \emph{all}
  categories gets us in trouble with Russell).  Note that $\cat{1}$ is
  the terminal object in $\Cat$.
\end{itemize}

\paragraph{Bifunctors}

The concept of \term{bifunctors} can be formalized as a two-argument
analogue of functors; bifunctors thus map from \emph{two} categories
to a single category.  However, the obvious definition of a bifunctor
$B : \C,\D \to \E$ turns out to be equivalent to a regular
(one-argument) functor $B : \C \times \D \to \E$, where $\C \times \D$
denotes the \term{product category} of $\C$ with $\D$.  Product
categories are given by the usual universal product construction in
$\Cat$, the category of all (small) categories; objects in $\C \times
\D$ are pairs of objects from $\C$ and $\D$, and likewise morphisms in
$\C \times \D$ are pairs of morphisms from $\C$ and
$\D$. One place that bifunctors come up often is in the context of
monoidal categories; see~\pref{sec:monoids}.

\paragraph{Natural transformations}

The notation $\eta : \all {A} {F A \to G A}$ will often be used to
denote a natural transformation $\eta : \nt F G$; this notation meshes
well with the intuition of Haskell programmers, since naturality
corresponds to \emph{parametricity}, a property enjoyed by polymorphic
types in Haskell~\citep{reynolds1983types, wadler1989free}.  It is
also more convenient when the functors $F$ and $G$ do not already have
names but can be readily specified by expressions, especially when
those expressions involve $A$ more than once or in awkward
positions\footnote{As Haskell programmers are well aware, writing
  everything in point-free style does not necessarily improve
  readability!}---for example, $\all {A} {A \otimes A \to \C(B, H
  A)}$.  This notation can be rigorously justified using \emph{ends};
see \pref{sec:ends-coends}.

\paragraph{Hom sets}

\todo{Use a different notation for exponents and powers?  Also, decide
re: notation for functor categories.}
In a similar vein, the set of morphisms between objects $A$ and $B$ in
a category $\C$ is usually denoted $\C(A,B)$ or
$\mathrm{Hom}_\C(A,B)$, but I will also occasionally use the notation
$A \to B$, or $A \to_\C B$ when the category $\C$ should be explicitly
indicated.  The same notation will be used for exponentials
(\pref{sec:monoids}) and powers (\pref{sec:enriched}).  While this
certainly has the potential to introduce ambiguity and confusion, it
has the decided benefit of playing to the intuition of Haskell
programmers, and often makes the structure of calculations more
apparent.  For example, the traditional notation \[ \int_{b} H
b^{\C(a,G b)} \] can be instead written as the Haskell-like \[
\eend{b} {(a \to G b) \to H b}, \] where the end
(\pref{sec:ends-coends}) has been written using $\forall$, and both
the hom set $\C(a, G b)$ and the power $H b^{\C(\dots)}$ using $\to$.
It should be emphasized that this notation is perfectly rigorous, and
not just an ``approximation'' in Haskell.

\paragraph{Slice categories}

Given a category $\C$ and an object $X \in \C$, the \term{slice
  category} $\C/X$ has as its objects diagrams $C
\stackrel{f}{\longrightarrow} X$, that is, pairs $(C,f)$ where $C \in
\C$ and $f$ is a morphism from $C$ to $X$.  Morphisms $(C_1,f_1) \to
(C_2,f_2)$ in $\C/X$ are morphisms $g : C_1 \to C_2$ of $\C$ which
make the relevant diagram commute:
\[ \xymatrix{
  C_1 \ar[rr]^g \ar[dr]_{f_1} && C_2 \ar[dl]^{f_2} \\
  & X }
\]
A good intuition is to think of the morphism $f : C \to X$ as giving a
``weight'' or ``label'' to $C$.  The slice category $\C/X$ thus
represents objects of $\C$ ``weighted'' or ``labelled'' by $X$, with
``weight/label-preserving maps'' as morphisms.  For example, objects
of $\Set/\R$ are sets where each element has been assigned a real
number weight; morphisms in $\Set/\R$ are weight-preserving functions.

% There is also a dual notion of \term{coslice} categories $X/\C$, but
% they are not needed in this dissertation.

\paragraph{Functor categories}

Given two categories $\C$ and $\D$, the collection of functors from
$\C$ to $\D$ forms a category (a \term{functor category}), with
natural transformations as morphisms.  This category is denoted by
both of the notations $[\C,\D]$ and $\D^\C$, as convenient.  The
notation $\D^\C$ is often helpful since intuition for exponents
carries over to functor categories; for example, $\C^{\D + \E} \iso
\C^\D \times \C^\E$, $(\C \times \D)^\E \iso \C^\E \times \D^\E$, and
so on. (In fact, this is not specific to functor categories; the same
sorts of isomorphisms hold in any bicartesian closed category.)

Given a set $X$, the functor category $\Set^X$ (considering $X$ as a
discrete category) is equivalent to the slice category $\Set / X$. In
particular, a functor $X \to \Set$ is an $X$-indexed collection of
sets, whereas an object of $\Set / X$ is a set $S$ with a function $f
: S \to X$ labelling each element of $S$ by some $x \in X$. Taking the
preimage or \term{fiber} $f^{-1}(x)$ of each $x \in X$ recovers an
$X$-indexed collection of sets; conversely, given an $X$-indexed
collection of sets we may take their disjoint union and construct a
function assigning each element of the disjoint union its
corresponding element of $X$. \pref{fig:discrete-slice} illustrates
the situation for $X = \{\mathrm{red}, \mathrm{blue}, \mathrm{green},
\mathrm{purple}\}$.  Following the arrows from bottom to top, the
diagram represents a functor $X \to \Set$, with each element of $X$
mapped to a set.  Following the arrows from top to bottom, the diagram
represents an object in $\Set/X$ consisting of a set of 12 elements
and an assignment of a color to each.

\begin{figure}
  \centering
  \begin{diagram}[width=200]
import SpeciesDiagrams

fiber elts i
  = map (\e -> text [e] <> circle 1 # lw 0.06 # lc (colors !! i)) elts
    # vcat' (with & sep .~ 0.5)
    # tag 0
    # named (i :: Int)

fibers =
  zipWith fiber
    [ "ACG"
    , "FH"
    , "DBI"
    , "LEKJ"
    ]
    [0..]
    # map centerXY
    # hcat' (with & sep .~ 1)
    # tag 0

x = tag 0 (hcat' (with & sep .~ 0.5) namedDots)
  where
    dots      = zipWith fc colors (repeat (circle 1))
    namedDots = zipWith named ['a' .. 'd'] dots

dia =
  vcat' (with & sep .~ 2) [ fibers, x ]
  # applyAll (zipWith (connectOutside' aOpts) [0 :: Int .. 3] "abcd")
  # frame 0.5

aOpts = with & headSize .~ 0.7 & arrowTail .~ dart' & tailSize .~ 0.7
  \end{diagram}
  \caption{An element of $\Set^X$ or $\Set/X$}
  \label{fig:discrete-slice}
\end{figure}

\paragraph{Equivalence of categories}

In category theory founded in set theory, there are quite a few
different definitions of equivalence between categories.  Ultimately,
this comes down to the fact, alluded to earlier, that set theory does
not make a very good foundation for category theory.  In particular,
when working in set theory, one has to work hard to maintain the
principle of equivalence.
\begin{defn} \label{defn:cat-iso}
  Two categories $\C$ and $\D$ are said to be \term{isomorphic} if
  there are inverse functors $\BackForth \C F G \D$, \ie with $GF =
  1_\C$ and $FG = 1_\D$.
\end{defn}
Unfortunately, this definition violates the principle of equivalence,
since, for example, $GF$ might be \emph{isomorphic} to $1_\C$ without
being \emph{equal} to it.  Isomorphism of categories is thus not a
very useful concept; usually the following concept is used instead:
\begin{defn} \label{defn:cat-equiv}
  An \term{equivalence} between $\C$
  and $\D$ is given by functors $\BackForth \C F G \D$ which are
  inverse up to natural isomorphism, that is, $GF \cong 1_\C$ and $FG
  \cong 1_\D$.
\end{defn}

In set theory, a function has an inverse if it is both injective and
surjective.  By analogy, another definition of equivalence is often
given, which for the sake of clarity we will refer to as
\term{one-sided equivalence}:

\begin{defn} \label{defn:cat-one-sided-equiv}
  $\C$ is \term{one-sided equivalent} to $\D$ if there is a functor $F
  : \C \to \D$ which is full and faithful (\ie a bijection on each
  hom-set) as well as \term{essentially surjective}, that is, for
  every object $D \in \D$ there exists some object $C \in \C$ such
  that $F(C) \cong D$.
\end{defn}

It is not hard to show that every equivalence is a one-sided
equivalence.  However, showing that a one-sided equivalence is an
equivalence requires the axiom of choice; intuitively, the problem is
that there is no canonical way to choose the action of the inverse
functor $G$. A much fuller discussion is given in \pref{sec:AC}, but
it's worth mentioning one of the punchlines now: in category theory
founded in HoTT rather than in set theory, the three definitions given
above are all simply equivalent, without violating the principle of
equivalence and without any need for AC!

\paragraph{Adjunctions}

The topic of \term{adjunctions} is much too large to adequately cover
here.  For the purposes of this dissertation, the most important form
of the definition to keep in mind is that a functor $F : \C \to \D$ is
\term{left adjoint} to $G : \D \to \C$ (and $G$ \term{right adjoint}
to $F$), notated $F \adj G$, if and only if \[ \Hom[\D]{F A}{B} \cong
\Hom[\C]{A}{G B}, \] that is, if there is some natural isomorphism
matching morphisms $F A \to B$ in the category $\D$ with morphisms $A
\to G B$ in $\C$.

One example familiar to functional programmers is \emph{currying}: \[
(A \times B \to C) \cong (A \to (B \to C)) \] This corresponds to the
adjunction \[ (- \times B) \adj (B \to -). \]

\subsection{Monoidal categories}
\label{sec:monoids}

Recall that a \term{monoid} is a set $S$ equipped with an associative
binary operation $\mappend : S \times S \to S$ and a distinguished
element $\mempty : S$ which is an identity for $\mappend$.  A
\term{monoidal category} is one with a ``monoid on objects'', that is,
a binary operation on objects and an identity object, with the
associativity and identity laws expressed via natural isomorphisms.
\begin{defn}
  A \term{monoidal category} is a category $\C$ equipped with
  \begin{itemize}
  \item a bifunctor $\otimes : \C \times \C \to \C$;
  \item a distinguished object $I \in \C$;
  \item a natural isomorphism $\alpha : \all{ABC}{(A \otimes B)
      \otimes C \cong A \otimes (B \otimes C)}$; and
  \item natural isomorphisms $\lambda : \all{A}{I \otimes A \cong
      A}$ and $\rho : \all{A}{A \otimes I \cong A}$.
  \end{itemize}
  $\alpha$, $\lambda$, and $\rho$ must additionally satisfy some
  ``coherence axioms'', which ensure that parallel isomorphisms
  constructed from $\alpha$, $\lambda$, and $\rho$ are always equal.

  We often write $(\C,\otimes,I)$ when we wish to emphasize the choice
  of a monoidal functor and identity object for a monoidal category $\C$.
\end{defn}

Note that $\otimes$ is not just a function on objects, but a
\emph{bifunctor}, so there must also be a way to combine morphisms $f
: \mor {A_1} {A_2}$ and $g : \mor {B_1} {B_2}$ into a morphism $f
\otimes g : \mor {A_1 \otimes B_1} {A_2 \otimes B_2}$ which respects
identities and composition.

Note also that a category can be monoidal in more than one way.  In
fact, as we will see in \pref{chap:species}, the category of species
is monoidal in at least six different ways!  Another example is
$\Set$, which has both Cartesian product and disjoint union as
monoidal structures.  More generally, categories with products
(together with a terminal object) and/or coproducts (together with an
initial object) are always monoidal.

There are many variants on the basic theme of monoidal categories; a
few of the most important, for the purposes of this dissertation, are
given here:

\begin{defn}
  A monoidal category is \term{symmetric} if there is additionally a
  natural isomorphism $\gamma : \all{AB}{A \otimes B \cong B \otimes
    A}$.
\end{defn}

For example, $\Set$ is symmetric monoidal under both Cartesian product
and disjoint union. As an example of a non-symmetric monoidal
category, consider the functor category $[\C,\C]$, with the monoid given
by composition of functors.

\begin{defn}
  A monoidal category $\C$ is \term{closed} if there some bifunctor $[-,-]
  : \C^\op \times \C \to \C$ such that there is a natural
  isomorphism \[ \all{ABC}{\Hom {A \otimes B} C \cong \Hom A
    {[B,C]}}, \] that is, $- \otimes B$ is left adjoint to $[B,-]$.
\end{defn}

$(\Set, \times)$ is closed: $[B,C]$ is defined as the set of functions
from $B$ to $C$, and the required isomorphism is currying.
Categories, like $\Set$, which are closed with respect to the
categorical product are called \term{Cartesian closed}.  Intuitively,
Cartesian closed categories are those which can ``internalize''
arrows, with objects that ``act like'' sets of morphisms.  Put another
way, Cartesian closed categories are those with ``first-class
morphisms''.  Functional programmers are familiar with this idea: in a
language with first-class functions, the class of functions
(morphisms) between two given types (objects) is itself a type
(object).

\begin{defn}
  A \term{strict} monoidal category is one in which $\alpha$,
  $\lambda$, and $\rho$ are \emph{equalities} rather than natural
  isomorphisms.  It is often remarked that every monoidal category is
  equivalent to some strict one (for example, using the theory of
  cliques~\cite{joyal1991geometry}, explained in \pref{sec:cliques}),
  which is used to justify the pretense that every monoidal category
  is strict; however, proving this requires the axiom of choice.
\end{defn}

\later{How can we say that we are using ``the same'' ``product-like''
  monoidal structure in all these different categories?  Are they
  related by monoidal functors?}

\subsection{Ends, coends, and Yoneda}
\label{sec:ends-coends}

\todo{Define/give intuition for ends and coends.  (Co)ends as
(co)equializers.  Talk about connection between natural
transformations and polymorphic functions, specific ways it plays out
in a dependent type theory---e.g. can we assume parametricity for
functions that abstract over things classified by |*|? Cite Bernardy
et al.}

\todo{Use notation $\forall$ and $\exists$ for ends and coends?}

\paragraph{Ends}

\todo{natural transformations as ends.  Justifies $\forall$ notation.}

\paragraph{The Yoneda lemma}

\todo{Yoneda.}

\paragraph{Coends}

\todo{fix notation}

Given a functor $T : \C^\op \times \C \to \D$, a \term{coend} over
$T$, denoted $\int^C T(C,C)$ or just $\int^\C T$, is an object of $\D$
together with some (di)naturality conditions.  In the specific case
when the objects of $\D$ can be thought of as sets or types with
``elements'', the coend $\int^C T(C,C)$ is given by a quotient of an
indexed coproduct $\left( \sum_{C \in \C} T(C,C) \right) / \sim$.
Elements of the indexed coproduct look like pairs $(C, t)$ where $C
\in \C$ and $t \in T(C,C)$. The idea behind the quotient is that we
want to consider two pairs $(C,t)$ and $(C', t')$ equivalent if they
are related by the functoriality of $T$.  In particular, for each
arrow $f : C \to C'$ in $\C$ and each $x \in T(C',C)$, we set $(C,
T(f,1)\ x) \sim (C', T(1,f)\ x)$.  That is, we can always ``swap out
$(C,t)$ for $(C',t')$'' as long as we have some way to map from $C$ to
$C'$ and the associated values $t$ and $t'$ are related by the same
mapping.

Intuitively, the functor $T$ can be thought of as an ``interface'';
$(C,t)$ is then a ``module'' with ``representation type'' $C$ and
``implementation'' $t$.  Indeed, in Haskell, the coend of $T$ is given
by the type \texttt{exists c.\ T c c} (or rather, by an isomorphic
encoding, since \texttt{exists} is not actually valid Haskell snytax)
\cite{kmett2008kan}. $T$ is required to be a functor from $\C^\op
\times \C$ since the representation type may occur both co- and
contravariantly in the interface.

The definition of a coend can be made precise in full generality
(without requiring the objects of $\D$ to have ``elements'') using a
\emph{coequalizer}.  \todo{Finish.  Give formal definition in terms of
  coequalizer.}

\begin{rem}
  Note that $\int^{L_1, L_2} \dots$ is used as an abbrevation for a
  coend over the product category $\Lab \times \Lab$. \todo{Given
    suitable assumptions it is also equivalent to an iterated coend
    (cite MacLane).}
\end{rem}

\subsection{Groupoids}
\label{sec:groupoids}

A \term{groupoid} is a category in which all morphisms are invertible,
that is, for each morphism $f$ there is another morphism $f^{-1}$ for
which $f \comp f^{-1} = id$ and $f^{-1} \comp f = id$.  Groupoids play
a prominent role in \todo{finish; cite groupoids and stuff; HoTT;
  etc.}

Some examples of groupoids include:

\begin{ex}
  Any group can be thought of as a groupoid with a single element,
  just as a monoid can be thought of as a one-object
  category. Conversely, groupoids can be thought of as ``groups with
  types'', where elements can only be composed if their types match
  (in contrast to a group, where any two elements can always be
  composed).
\end{ex}

\begin{ex}
  The groupoid whose objects are natural numbers, and whose morphisms
  $\mor m n$ are the invertible $m \times n$ matrices over some field,
  with composition given by matrix multiplication. (Hence there are no
  morphisms when $m \neq n$.)
\end{ex}

\begin{defn}
  $\B$ is the groupoid whose objects are finite sets and whose
  morphisms are bijections between finite sets.
\end{defn}

In fact, $\B$ is an instance of a more general phenomenon:

\begin{defn}
  Any category $\C$ gives rise to a groupoid $\core \C$, called the
  \term{core} of $\C$, whose objects are the objects of $\C$ and whose
  morphisms are the isomorphisms in $\C$.
\end{defn}

Checking that $\core \C$ is indeed a groupoid is left as an easy
exercise.  Note in particular that $\B = \core{\FinSet}$.

\begin{defn}
  The \term{symmetric groupoid} $\P$ is defined as the groupoid whose
  objects are natural numbers and whose morphisms $\mor m n$ are
  bijections $\fin m \bij \fin n$.
\end{defn}

\begin{defn}
  The type of permutations on a set $S$, that is, bijections from $S$
  to itself, is denoted $\perm S$.
\end{defn}

\begin{rem}
  Note that the set of morphisms $\mor m n$ is empty unless $m = n$,
  and morphisms $\mor n n$ are permutations $\perm{\fin n}$.

  $\P$ is called the \term{symmetric groupoid} since it is isomorphic
  to an infinite coproduct $\coprod_{n \geq 0} \S_n$, where $\S_n$
  denotes the symmetric \emph{group} of all permutations on $n$
  elements, considered as a one-object groupoid.  In other words, $\P$
  consists of a collection of non-interacting ``islands'', one for
  each natural number. \todo{picture?}  In particular, this means that
  any functor $F : \P \to \C$ is equivalent to a collection of
  independent functors $\prod_{n \geq 0} \S_n \to \C$, one for each
  natural number.  Each functor $\S_n \to \C$ is entirely independent
  of the others, since there are no morphisms between different $\S_n$
  to introduce constraints.
\end{rem}

There is a close relationship between $\B$ and $\P$.  In the presence
of the axiom of choice, they are equivalent; intuitively, $\P$ is what
we get by noting that any two sets of the same size are isomorphic, so
we ``might as well'' just forget about the elements of finite sets and
work directly with their sizes.  However, if the axiom of choice is
rejected, the details become much more subtle; this is addressed
in~\pref{sec:finiteness}.

$\B$ (and $\P$) do not have products or coproducts. For example, to
see that $\B$ does not have coproducts, let $A, B \in \B$ be arbitrary
finite sets, and suppose they have some coproduct $A+B$. By definition
this comes with a diagram $\xymatrix{A \ar[r]^-{\iota_1} & A+B & B
  \ar[l]_-{\iota_2}}$ in $\B$. Since morphisms in $\B$ are bijections,
this would imply that $A$ and $B$ are in bijection, but since $A$ and
$B$ were arbitrary finite sets, this is absurd.  A similar argument
applies in the case of products.  More generally, any category with
all products or coproducts is necessarily \term{connected}, \ie has
some zig-zag sequence of arrows connecting any two objects, and this
is clearly not true of $\B$.

$\B$ does, however, have monoidal structures given by Cartesian
product and disjoint union of finite sets, even though these are not a
categorical product or coproduct. In particular, two bijections
$\sigma_1 : S_1 \bij T_1$ and $\sigma_2 : S_2 \bij T_2$ naturally give
rise to a bijection $(S_1 \times S_2) \bij (T_1 \times T_2)$, which
sends $(s_1, s_2)$ to $(\sigma_1(s_1), \sigma_2(s_2))$, as well as a
bijection $(S_1 \uplus S_2) \bij (T_1 \uplus T_2)$ which sends $\inl\
s_1$ to $\inl(\sigma_1(s_1))$ and $\inr\ s_2$ to $\inr(
\sigma_2(s_2))$. \later{picture?} In fact, something more general is
true:

\begin{prop}
  Any monoid $(\otimes,1)$ on a category $\C$ restricts to a monoid
  $(\otimes^*,1)$ on the groupoid $\C^*$.
\end{prop}
\begin{proof}
  There is a forgetful functor $U : \C^* \to \C$ which is the identity
  on both objects and morphisms.  Given $X,Y \in \C^*$, we may define
  \[ X \otimes^* Y = U X \otimes U Y; \] this may be considered as an
  object of $\C^*$ since $\C$ and $\C^*$ have the same objects.  Given
  morphisms $\sigma$ and $\tau$ of $\C^*$, we also define \[ \sigma
  \otimes^* \tau = U \sigma \otimes U \tau, \] and note that the
  result must be an isomorphism in $\C$---hence a morphism in $\C^*$---since
  all functors (here, $U$ and $\otimes$ in particular) preserve
  isomorphisms.

  The fact that $1$ is an identity for $\otimes^*$, associativity, and
  the coherence conditions all follow readily from the definitions.
\end{proof}

\subsection{Enriched categories}
\label{sec:enriched}

\todo{Write me.  Basic definitions; powers and copowers.}

\section{The axiom of choice (and how to avoid it)}
\label{sec:AC}

The (in)famous \emph{axiom of choice} (hereafter, AC) plays a central
role in much of modern mathematics.  In a constructive setting,
however, it is problematic.  Much effort has been expended trying to
avoid it \citep{makkai, FOLDS, voevodsky}; in a sense, this can be
seen as one of the goals of the univalent foundations program.
In \label{sec:anafunctors-hott} we will see how HoTT indeed provides
an excellent AC-free foundation for the mathematics we want to do.
First, however, we give an introduction to AC and related issues in
set theory.

The axiom of choice can be formulated in a number of equivalent ways.
Perhaps the most well-known is
\begin{equation}
  \label{eq:ac1} \tag{AC}
  \text{The Cartesian product of any collection of non-empty sets is non-empty.}
\end{equation}
Given a family of sets $\{X_i \mid i \in I\}$, an element of their
Cartesian product is some $I$-indexed tuple $\{x_i \mid i \in I\}$
where $x_i \in X_i$ for each $i$. Such a tuple can be thought of as a
function (called a \emph{choice function}) which picks out some
particular $x_i$ from each $X_i$.  This can be visualized (for a
particularly small and decidedly finite case) as shown
in~\pref{fig:ac-example}.

\begin{figure}
  \centering
  \begin{diagram}[width=200]
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ParallelListComp          #-}
{-# LANGUAGE TemplateHaskell           #-}

import           Control.Lens                   (makeLenses, (^.))
import           Data.Default.Class

import           Data.Colour.Palette.BrewerSet

data SetOpts = SetOpts
  { _setSize   :: Int
  , _eltShape  :: Diagram B R2
  , _highlight :: Maybe Int
  , _eltColors :: [Colour Double]
  , _setName   :: Name
  }

makeLenses ''SetOpts

instance Default SetOpts where
  def = SetOpts { _setSize = 3, _eltShape = circle 0.5, _highlight = Nothing, _eltColors = [black], _setName = toName () }

drawSet :: SetOpts -> Diagram B R2
drawSet opts
  = vcat' (with & catMethod .~ Distrib & sep .~ 1.5) elts
    # enclose 0.5 1
    # centerY
  where
    elts = zipWith3 mkElt [0..] (cycle (opts ^. eltColors)) (replicate (opts ^. setSize) (opts ^. eltShape))
    mkElt i c shp
      || Just i == opts ^. highlight = base # lw 0.2 # lc black
      || otherwise                   = base
      where
        base = shp # fc c # named ((opts ^. setName) .> i)

colors :: [Kolor]
colors = brewerSet Set1 9

zipWith4 :: (a -> b -> c -> d -> e) -> [a] -> [b] -> [c] -> [d] -> [e]
zipWith4 _ [] _ _ _ = []
zipWith4 _ _ [] _ _ = []
zipWith4 _ _ _ [] _ = []
zipWith4 _ _ _ _ [] = []
zipWith4 f (a:as) (b:bs) (c:cs) (d:ds) = f a b c d : zipWith4 f as bs cs ds

sets :: [SetOpts]
sets = zipWith4 mkSet
  [0..]
  [2,5,4,6,1]
  shapes
  selections

shapes :: [Double -> Diagram B R2]
shapes = [circle, triangle, pentagon, hexagon, (\d -> square d # rotateBy (1/8))]

selections :: [Maybe Int]
selections = (map Just [0,2,3,1,0])

mkSet :: Int -> Int -> (Double -> Diagram B R2) -> Maybe Int -> SetOpts
mkSet nm n shp hi =
  def
  & setSize .~ n
  & eltColors .~ colors
  & eltShape .~ (shp 1 # sized (Width 1))
  & highlight .~ hi
  & setName .~ toName nm

collection :: Diagram B R2
collection = (hcat' (with & sep .~ 1) $ map drawSet sets) # centerX  -- $

choice :: Diagram B R2
choice = (hcat' (with & sep .~ 0.5) $ zipWith3 mkSel [0::Int ..] shapes selections) # enclose 0.5 1 -- $
  where
    mkSel i shp (Just j) = shp 1 # sized (Width 1) # fc (cycle colors !! j) # centerXY # named ("b" .> i .> j)
    mkSel _ _ _ = mempty

dia = frame 1 $   -- $
  vcat' (with & sep .~ 2)
    [ collection
    , choice
    ]
    # applyAll
      [ connectOutside' aOpts (mkNm i j) ("b" .> mkNm i j)
      || i      <- [0..5]
      || Just j <- selections
      ]

aOpts = with & shaftStyle %~ lc grey & headColor .~ grey & headGap .~ 0.5 & headSize .~ 0.7

mkNm :: Int -> Int -> Name
mkNm i j = i .> j
  \end{diagram}
  \caption{The axiom of choice}
  \label{fig:ac-example}
\end{figure}

Note that AC is \emph{independent} of the usual set theory foundations
(the so-called \emph{Zermelo-Fraenkel axioms}, or ZF), in the sense
that it is consistent to add either AC or its negation to ZF.  In
particular this means that neither AC nor its negation can be proved
from the axioms of ZF (since then adding the other would lead to
inconsistency).  It is somewhat controversial since it has some
strange consequences, \eg the Banach-Tarski
paradox~\cite{banach-tarski}.  However, most mathematicians have come
to accept it, and work (in principle) within ZF extended with AC,
known as ZFC.

Consider how to express AC in type theory.  First, we assume we have
some type $I$ which indexes the collection of sets; that is, there
will be one set for each value of type $I$.  Given some type $A$, we
can define a subset of the values of type $A$ using a
\emph{predicate}, that is, a function $P : A \to \Type$.  For some
particular $a : A$, applying $P$ to $a$ yields a type, which can be
thought of as the type of evidence that $a$ is in the subset $P$; $a$
is in the subset if and only if $P(a)$ is inhabited.  An $I$-indexed
collection of subsets of $A$ can then be expressed as a function $C :
I \to A \to \Type$. In particular, $C(i,a)$ is the type of evidence
that $a$ is in the subset indexed by $i$.  (Note that we could also
make $A$ into a family of types indexed by $I$, that is, $A : I \to
\star$, which makes the encoding more expressive but doesn't
ultimately affect the subsequent discussion.)

A set is nonempty if it has at least one element, so the fact that all
the sets in $C$ are nonempty can be modeled by a dependent function
which yields an element of $A$ for each index, along with a proof
that it is contained in the corresponding subset:
\[ (i : I) \to (a : A) \times C(i,a). \] An element of the Cartesian
product of $C$ can be expressed as a function $I \to A$ that picks out
an element for each $I$ (the choice function), together with a proof
that the chosen elements are in the appropriate sets:
\[ (g : I \to A) \times ((i : I) \to C(i, g(i))). \] Putting these
together, apparently the axiom of choice can be modelled by the type
\[ ((i : I) \to (a : A) \times C(i,a)) \to (g : I \to A) \times ((i : I)
\to C(i, g(i))). \]
Converting to $\Pi$ and $\Sigma$ notation and squinting actually
gives some good insight into what is going on:
\[ \left( \prod_{i : I} \sum_{a : A} C(i,a) \right) \to \left( \sum_{g
    : I \to A} \prod_{i : I} C(i, g(i)) \right) \] Essentially, this
says that we can ``turn a (dependent) product of sums into a
(dependent) sum of products''.  This sounds a lot like distributivity,
and indeed, the strange thing is that this is simply \emph{true}:
implementing a function of this type is a simple exercise!  The
intuitive idea can be grasped by implementing a non-dependent
analogue, say, a Haskell function of type |(i -> (a,c)) -> (i -> a, i
-> c)|.  This is quite easy to implement, and the dependent version is
essentially no harder; only the types that get more complicated, not
the implementation.  So what's going on here?  Why is AC so
controversial if it is simply \emph{true} in type theory?

The problem, it turns out, is that we've modelled the axiom of choice
improperly, and it all boils down to how ``non-empty'' is defined.
When a mathematician says ``$S$ is non-empty'', they typically don't
actually mean ``\dots and here is an element of $S$ to prove it''.
Instead, they literally mean ``it is *not the case* that $S$ is
empty'', that is, assuming $S$ is empty leads to a contradiction.
(Actually, there is something yet more subtle going on, to be
discussed below, but this is a good first approximation.)  In
classical logic, these viewpoints are equivalent; in constructive
logic, however, they are very different!  In constructive logic,
knowing that it is a contradiction for $S$ to be empty does not
actually help you find an element of $S$.  We modelled the statement
``this is a collection of non-empty sets'' essentially by saying
``here is an element in each set'', but in constructive logic that is
a much \emph{stronger} statement than simply saying that each set is
not empty.

From this point of view, we can see why the ``axiom of choice'' in the
previous section was easy to implement: it had to produce a function
choosing a bunch of elements, but it was given a bunch of elements to
start. All it had to do was shuffle them around a bit.  The ``real''
AC, on the other hand, has a much harder job: it is told some sets are
non-empty, but without any actual elements being mentioned, and it
then has to manufacture a bunch of elements out of thin air.  This
already doesn't seem to fit very well in a constructive/computational
context; but even more to the point, it turns out that the axiom of
choice implies the law of excluded middle \citep{diaconescu1975axiom,
  goodman1978choice}, \citep[Theorem 10.1.14]{hottbook}!  Working as
we are in a type theory based on intuitionistic logic, we must
therefore reject the axiom of choice.

It is worth noting that within HoTT, the notion of a ``non-empty'' set
can be defined in a more nuanced way.  The best way to model what
classical mathematicians mean when they say ``$S$ is non-empty'' is
probably not with a negation, but instead with the \emph{propositional
  truncation} of the statement that $S$ contains an
element~\cite[Chapter 3]{hottbook}.  This more faithfully mirrors the
way mathematicians use it, for example, in reasoning such as ``$S$ is
non-empty, so let $s \in S$ \dots''.  Non-emptiness does in fact imply
an inhabitant, but such an inhabitant can only be used to prove
propositions, not to construct values.

\subsection{Unique isomorphism and generalized ``the''}
\label{sec:generalized-the}

In category theory, one is typically interested in specifying objects
only \emph{up to unique isomorphism}.  In fact, definitions which make
use of actual \emph{equality} on objects are sometimes referred to
(half-jokingly) as \emph{evil}.  More positively, the principle of
equivalence states that properties of mathematical structures should
be invariant under equivalence.  This principle leads naturally to
speaking of ``the'' object having some property, when in fact there
may be many objects with the given property, but all such objects are
uniquely isomorphic; this cannot cause confusion if the principle of
equivalence is in effect.

\later{Rewrite this a bit based on feedback from blog post comments.}
This phenomenon should be familiar to anyone who has seen simple
universal constructions such as terminal objects or categorical
products.  For example, an object $1 \in \C$ is called \term{terminal}
if there is a unique morphism $\mor A 1$ from each object $A \in
\C$. In general, there may be many objects satisfying this
criterion; for example, in \Set, every singleton set is terminal.
However, it is not hard to show that any two terminal objects must be
uniquely isomorphic.  Thus it ``does not matter'' which terminal
object we use---they all have the same properties, as long as we don't
do anything ``evil''---and one therefore speaks of ``the'' terminal
object of $\C$.  As another example, a \term{product} of two objects
$A,B \in \C$ is a diagram $\xymatrix{A & C \ar[l]_{\pi_1}
  \ar[r]^{\pi_2} & B}$ with the universal property that any other $C'$
with morphisms to $A$ and $B$ uniquely factors through $C$.  Again,
there may be multiple such products, but they are all uniquely
isomorphic, and one speaks of ``the'' product $A \times B$.

Note that in some cases, there may be a canonical choice among
isomorphic objects.  For example, this is the case with products in
$\Set$, where we may always pick the Cartesian product $\{(a,b) \mid a
\in A, b \in B\}$ as a canonical product of $A$ and $B$.  In such
cases use of ``the'', as in ``the product of $A$ and $B$'', is even
more strongly justified, since we may take it to mean ``the
\emph{canonical} product of $A$ and $B$''. However, in many cases (for
example, with terminal objects in $\Set$), there is no canonical
choice, and ``the terminal object'' simply means something like ``some
terminal object, it doesn't matter which''.

Beneath this seemingly innocuous use of ``the'' (often referred to as
\term{generalized ``the''}), however, lurks the axiom of choice!  For
example, if a category $\C$ has all products, we can define a functor
$P : \C \times \C \to \C$\footnote{Note that we have made use here of
  ``the'' product category $\C \times \C$---fortunately $\Cat$, like
  $\Set$, has a suitably \emph{canonical} notion of products.} which
picks out ``the'' product of any two objects $A$ and $B$---indeed, $P$
may be taken as the \emph{definition} of the product of $A$ and
$B$.  But how is $P$ to be defined?  Consider $\{ \mathrm{Prod}(A,B)
\mid A,B \in \C \}$, where $\mathrm{Prod}(A,B)$ denotes the set of all
possible products of $A$ and $B$, \ie all suitable diagrams
$\xymatrix{A & C \ar[l]_{\pi_1} \ar[r]^{\pi_2} & B}$ in $\C$.  Since
$\C$ has all products, this is a collection of nonempty sets;
therefore we may invoke AC to obtain a choice function, which is
precisely $P_0$, the action of $P$ on objects.  The action of $P$ on
morphisms may then be defined straightforwardly.

The axiom of choice really is necessary to construct $P$: as has
already been noted, there is, in general, no way to make some
canonical choice of object from each equivalence class.  On the other
hand, this seems like a fairly ``benign'' use of AC.  If we have a
collection of equivalence classes, where the elements in each class
are all uniquely isomorphic, then using AC to pick one representative
from each really ``does not matter'', in the sense that we cannot tell
the difference between different choices (as long as we refrain from
evil).  Unfortunately, even such ``benign'' use of AC still poses a
problem for computation.

\subsection{AC and equivalence of categories}
\label{sec:AC-equivalence}

Another place AC shows up in category theory, as hinted in
\pref{sec:ct-fundamentals}, is in relation to equivalence of
categories.  Recall the two different notions of equivalence:

\begin{repdefn}{defn:cat-equiv}
  An \term{equivalence} between $\C$
  and $\D$ is given by functors $\BackForth \C F G \D$ which are
  inverse up to natural isomorphism, that is, $GF \cong 1_\C$ and $FG
  \cong 1_\D$.
\end{repdefn}

\begin{repdefn}{defn:cat-one-sided-equiv}
  $\C$ is \term{one-sided equivalent} to $\D$ if there is a functor $F
  : \C \to \D$ which is full and faithful (\ie a bijection on each
  hom-set) as well as \term{essentially surjective}, that is, for
  every object $D \in \D$ there exists some object $C \in \C$ such
  that $F(C) \cong D$.
\end{repdefn}

Every equivalence is a one-sided equivalence, but to prove every
one-sided equivalence is an equivalence requires AC.  In more detail,
suppose $F : \C \to \D$ is fully faithful and essentially surjective.
To construct an equivalence between $\C$ and $\D$, we must define a
functor $G : \D \to \C$ and show it is inverse to $F$ (up to natural
isomorphism).  However, to define $G$ we must give its action on each
object $D \in \D$, that is, a function $\Ob \D \to \Ob \C$.  We know
that for each $D \in \D$ there \emph{exists} some object $C \in \C$
with $F\ C \cong D$; that is, $\{ \{ C \in \C \mid F\ C \cong D \}
\mid D \in \D \}$ is a collection of nonempty sets.  However, in a
non-constructive logic, knowing these sets are nonempty does not
actually give us any objects; we must use the axiom of choice to yield
a choice function $\Ob \D \to \Ob \C$, which we can use as the object
mapping of the functor $G$.  In fact, the association goes deeper yet:
it turns out that the statement
\begin{equation}
  \text{every fully faithful, essentially surjective functor is an
    equivalence} \tag{FFES} \label{eq:ffes-eqv}
\end{equation}
not only requires AC, but is \emph{equivalent} to it
\citep{cat-equivalence-AC}!

In theory, this poses no particular problems; if we want to avoid AC
we can just stick to the inverse-functors definition of equivalence.
In practice, however, it is often much easier to define a single
functor and prove it has the right properties than it is to produce a
pair of inverse functors. It would be a shame to lose \eqref{eq:ffes-eqv} as a
tool for constructing equivalences, especially since it seems like it
really ``ought to'' work---in the sense that the use of AC is
``benign'', as discussed previously.

One may therefore ask whether there is a slightly different framework
in which we may recover (something like) \eqref{eq:ffes-eqv}, without
requiring AC.  There are two main approaches.  The first is to
generalize functors, using either cliques (\pref{sec:cliqes}) or
anafunctors (\pref{sec:anafunctors}).  The second, to be explored
later, is to generalize the notion of equality---this is the approach
taken by HoTT.

The theory of \term{cliques} is presented first---cliques come close
to being a way around AC, and although they don't completely surmount
the problem in the end, they offer some good intuition for
understanding \term{anafunctors}, presented in
\pref{sec:anafunctors}.  Later, \pref{sec:anafunctors-hott} will
present these concepts as they arise in HoTT.

\subsection{Cliques}
\label{sec:cliques}

A clique is a formal way of representing the informal notion of
``equivalence class of uniquely isomorphic objects''.

\begin{defn}
  A \term{clique} $(I,A,u)$ in a category
  $\C$ is given by
  \begin{itemize}
  \item a collection of objects $A = \{A_i \mid i \in I\}$, indexed by
    some collection $I$, and
  \item a collection of morphisms $u = \{\xymatrix{A_i \ar[r]^{u_{ij}} &
      A_j} \mid i,j \in I\}$,
  \end{itemize}
  such that for all $i,j,k \in I$,
  \begin{itemize}
  \item $u_{ii} = \id_{A_i}$, and
  \item $u_{ij} \then u_{jk} = u_{ik}$.
  \end{itemize}
\end{defn}

\begin{rem}
  Note that the last two conditions together imply $u_{ij} =
  u_{ji}^{-1}$, since $u_{ij} \then u_{ji} = u_{ii} = id$.
\end{rem}

A clique can thus be visualized as an actual clique in a directed
graph, with a unique morphism between any two objects: \[
\xymatrix{ A_1 \ar@@<.2em>[d] \ar@@<.4em>[r]
  \ar@@<.2em>[dr]
  & A_2 \ar[l] \ar@@<.2em>[d] \ar@@<.2em>[dl] \\
  A_3 \ar@@<.2em>[u] \ar[r] \ar@@<.2em>[ur] &
  A_4 \ar@@<.4em>[l] \ar@@<.2em>[u] \ar@@<.2em>[ul] }
\]

Thus, a clique represents a collection of objects in $\C$ which are
all isomorphic, with a single chosen isomorphism between any two.

\begin{defn}
  A morphism between two cliques $(I,A,u)$ and $(J,B,v)$
  is given by a collection of arrows \[ \{ \xymatrix{A_i \ar[r]^f_{ij}
    & B_j} \mid i \in I, j \in J \} \] such that \[ \xymatrix{ A_i
    \ar[r]^{f_{ij}} \ar[d]_{u_{ik}} & B_j \ar[d]^{v_{jl}} \\ A_{k}
    \ar[r]_{f_{kl}} & B_{l}} \] commutes for all $i,k \in I$ and
  $j,l \in J$.
\end{defn}

Thus a morphism of cliques is a way to map an entire class of uniquely
isomorphic objects to another---in particular, a way to map any
representative of the first class to any representative of the
second---in a way that preserves the unique isomorphisms.

In fact, the class of cliques and clique morphisms in a category $\C$
itself forms a category $\clq \C$.  It is easy to imagine what the
identity morphism of cliques must be---the one which maps each $A_i$
to $A_j$ via $u_{ij}$.  However, a surprise awaits us when we define
composition of clique morphisms.  Suppose we have three cliques with
morphisms $\xymatrix{(I,A,u) \ar[r]^f & (J,B,v) \ar[r]^g & (K,C,q)}$.
We need to define a collection of morphisms $\xymatrix{A_i
  \ar[r]^{h_{ik}} & C_k}$.  For any given $A_i$ and $C_k$, we have
morphisms from $A_i$ to each of the $B_j$, and from each of the $B_j$
to $C_k$:
\[ \xymatrixrowsep{1pc}
  \xymatrix{
    & B_1 \ar@@<.2em>[dd] \ar@@<.4em>[r] \ar[drr] \ar@@<.2em>[ddr]
    & B_2 \ar[l] \ar@@<.2em>[dd] \ar[dr]^{g_{2k}} \ar@@<.2em>[ddl] \\
  A_i \ar[ur]^{f_{i1}} \ar[dr]_{f_{i3}} \ar[urr] \ar[drr] &     &     & C_k \\
    & B_3 \ar@@<.2em>[uu] \ar@@<-.4em>[r] \ar[urr] \ar@@<.2em>[uur]
    & B_4 \ar[l] \ar@@<.2em>[uu] \ar[ur]_{g_{4k}} \ar@@<.2em>[uul]
  }
\]
If we pick some particular $B_j$, we can define $h_{ik} = f_{ij} \then
g_{jk}$; and it's not hard to show that the result will be the same no
matter which $B_j$ we pick, since everything in sight commutes.  But
which $B_j$ should we pick?  In fact, we have to use the axiom of
choice!  Again, this use of AC is ``benign'', but it is a use
nonetheless.

In any case, the idea is now to replace functors $\C \to \D$ with
functors $\C \to \clq \D$, which map objects of $\C$ to entire
equivalence classes of objects in $\D$, instead of arbitrarily picking
some object from each equivalence class.  For example, instead of a
functor $\C \times \C \to \C$ giving ``the'' product of any two
objects of $\C$, there is a functor $\C \times \C \to \clq \C$: given
any two objects $A,B \in \C$, it constructs the clique whose objects
are all possible products of $A$ and $B$, and whose morphisms are the
unique isomorphisms $u_{ij}$ between products: \[ \xymatrix{ & C_i
  \ar[dl] \ar[dd]^{u_{ij}} \ar[dr] & \\ A & & B \\ & C_j \ar[ul]
  \ar[ur] & } \]

This gets rid of the need for AC in defining such functors.  However,
we have only succeeded in postponing the problem a bit, since defining
composition in $\clq \D$ requires AC.  It is also somewhat cumbersome
to replace $\D$ by $\clq \D$ in this way.  To make it tenable, one
would define a new notion of ``clique functor'' $F : \C
\stackrel{\clq{}}{\to} \D$ given by a regular functor $\C \to \clq
\D$, and show that these clique functors ``act like'' functors in
suitable ways.  For example, it is easy to see that any regular
functor $\C \to \D$ can be made into a trivial functor $\C \to \clq
\D$, by sending each $C \in \C$ to the singleton clique containing
only $F(C)$.  One can also show that clique functors can be composed,
have a suitable notion of natural transformations between them,
and so on\footnote{In fact, $\clq{-}$ turns out to be a (2-)monad, and the
  category of clique functors is its Kleisli category
  \citep{nlab-clique}.}. However, there is an alternative, equivalent
formuation of ``clique functors'', namely, \term{anafunctors}, which
do not require AC to define.

\subsection{Anafunctors}
\label{sec:anafunctors}

\todo{Prove/explain relationship with cliques?}

As an intuition for anafunctors it is helpful to keep in mind the
equivalent concept of functors $\C \to \clq \D$---both represent
functors whose ``values are specified only up to unique isomorphsim''.
Such functors represent a many-to-many relationship between objects of
$\C$ and objects of $\D$.  Normal functors may map multiple objects of
$\C$ to the same object in $\D$; the novel aspect is the ability to
have a single object of $\C$ correspond to multiple objects of $\D$.
The key idea is to add a class of ``specifications'' which mediate the
relationship between objects in the source and target categories, in
exactly the same way that a ``junction table'' must be added to
support a many-to-many relationship in a database schema.  This is
illustrated in \pref{fig:junction-table}. On the left is a
many-to-many relation between a set of shapes and a set of numbers.
On the right, this relation has been mediated by a ``junction table''
containing a set of ``specifications''---in this case, each
specification is simply a pair of a shape and a number---together with
two mappings (one-to-many relations) from the specifications to both of
the original sets, such that a specification maps to a shape $s$ and
number $n$ if and only if $s$ and $n$ were originally related.

\begin{figure}
  \centering
  \begin{diagram}[width=300]
import           Control.Arrow                  ((&&&))
import           Data.Maybe                     (fromMaybe)

drawTable :: IsName n => [(n, Diagram B R2)] -> Diagram B R2
drawTable = centerY . vcat . map (\(l, d) -> enbox d # named l)

enbox :: Diagram B R2 -> Diagram B R2
enbox d = d # centerXY # sizedAs r # scale 0.6 <> r
  where
    r :: Diagram B R2
    r = rect 1.618 1

table1 = zip ["A","B","C"]
  [ circle 1
  , triangle 1
  , square 1
  ]

table2 = map ((id &&& ((<> square 1 # lw 0) . text)) . show) [1..4]

relation =
  [ ("A", "1")
  , ("A", "2")
  , ("B", "1")
  , ("B", "2")
  , ("B", "3")
  , ("C", "4")
  ]

drawRelation t1 t2 rel
  = hcat' (with & sep .~ 2.5) [drawTable t1, drawTable t2]
  # applyAll
    [connectOutside a b || (a,b) <- rel]

drawJunction t1 t2 rel
  = hcat' (with & sep .~ 2.5) [drawTable t1, drawTable junction, drawTable t2]
  # applyAll
    ([connectOutside r (fst r) || r <- rel] ++ [connectOutside r (snd r) || r <- rel])
  where
    junction = [ (r, junctionDia r) || r <- rel ]
    junctionDia (a,b)
      = hcat' (with & sep .~ 0.5) [lookup' a t1 # centerXY # sized (Dims 1 1), lookup' b t2 # centerXY # sized (Dims 1 1)]
    lookup' x y = fromMaybe mempty (lookup x y)

dia =
  hcat' (with & sep .~ 4)
    [ drawRelation table1 table2 relation
    , drawJunction table1 table2 relation
    ]
  # frame 0.5
  \end{diagram}
  \caption{Representing a many-to-many relationship via a junction table}
  \label{fig:junction-table}
\end{figure}

\begin{defn} \label{defn:anafunctor}
  An \term{anafunctor} $F : \C \to \D$ is defined as follows.
  \begin{itemize}
  \item There is a class $S$ of \term{specifications}.
  \item There are two functions $\Span {\Ob \C} {\lana{F}} {S}
    {\rana{F}} {\Ob \D}$ mapping specifications to objects of $\C$ and
    $\D$.
  \end{itemize}
  $S$, $\lana{F}$, and $\rana{F}$ together define a many-to-many
  relationship between objects of $\C$ and objects of $\D$.
  $D \in \D$ is called a \term{specified value of $F$ at $C$} if there
  is some specification $s \in S$ such that $\lana{F}(s) = C$ and
  $\rana{F}(s) = D$, in which case we write $F_s(C) = D$.  Moreover, $D$
  is \term{a value of $F$ at $C$} (not necessarily a \emph{specified}
  one) if there is some $s$ for which $D \cong F_s(C)$.

  The idea now is to impose additional conditions which ensure that
  $F$ ``acts like'' a regular functor $\C \to \D$.
  \begin{itemize}
  \item Functors are defined on all objects; so we require each object
    of $\C$ to have at least one specification $s$ which corresponds
    to it---that is, $\lana{F}$ must be surjective.
  \item Functors transport morphisms as well as objects.  For each
    $s,t \in S$ and each $f : \lana{F}(s) \to \lana{F}(t)$ in $\C$,
    there must be a morphism $F_{s,t}(f) : F_s(\lana{F}(s)) \to
    F_t(\lana{F}(t))$ in $\D$:
    \begin{center}
      \begin{diagram}[width=150]
import SpeciesDiagrams

dia =
  hcat' (with & sep .~ 2)
    [ objs "CD"
    , objs "st"
    , objs "PQ"
    ]
  # applyAll [ connectOutside' aOpts x y || [x,y] <- ["CD", "PQ", "sC", "sP", "tD", "tQ"] ]
  # frame 0.5

aOpts = with & gap .~ 0.2
      \end{diagram}
    \end{center}
  \item Functors preserve identities: for each $s \in S$ we should
    have $F_{s,s}(\id_{\lana{F}(s)}) = \id_{\rana{F}(s)}$.
  \item Finally, functors preserve composition: for all $s,t,u \in
    S$, $f : \lana{F}(s) \to \lana{F}(t)$, and $g : \lana{F}(t) \to
    \lana{F}(u)$, it must be the case that $F_{s,u}(f \then g) =
    F_{s,t}(f) \then F_{t,u}(g)$:
    \begin{center}
      \begin{diagram}[width=150]
import SpeciesDiagrams

dia =
  hcat' (with & sep .~ 2)
    [ objs "CDE"
    , objs "stu"
    , objs "PQR"
    ]
  # applyAll [ connectOutside' aOpts x y || [x,y] <- ["CD", "DE", "PQ", "QR", "sC", "sP", "tD", "tQ", "uE", "uR"] ]
  # frame 0.5

aOpts = with & gap .~ 0.2
      \end{diagram}
    \end{center}
  \end{itemize}
\end{defn}

\begin{rem}
  Our initial intuition was that an anafunctor should map objects of
  $\C$ to equivalence classes of objects in $\D$.  This may not be
  immediately apparent from the definition, but is in fact the
  case. In particular, the identity morphism $\id_C$ maps to
  isomorphisms between specified values of $C$; that is, under the
  action of an anafunctor, an object $C$ together with its identity
  morphism ``blow up'' into a clique.  To see this, let $s,t \in S$ be
  two different specifications corresponding to $C$, that is,
  $\lana{F}(s) = \lana{F}(t) = C$. Then by preservation of composition
  and identities, we have \[ F_{s,t}(\id_C) \then F_{t,s}(\id_C) =
  F_{s,s}(\id_C \then \id_C) = F_{s,s}(\id_C) = \id_{\rana{F}(s)}, \] so
  $F_{s,t}(\id_C)$ and $F_{t,s}(\id_C)$ constitute an isomorphism
  between $F_S(C)$ and $F_t(C)$.
\end{rem}

There is an alternative, equivalent definition of anafunctors, which
is somewhat less intuitive but usually more convenient to work with.

\begin{defn} \label{defn:anafunctor-span} An anafunctor $F : \C \to
  \D$ is a category $\Spec$ together with a span of \emph{functors}
  $\Span \C {\lana{F}} {\Spec} {\rana{F}} \D$ where $\lana{F}$ is
  fully faithful, and (strictly) surjective on objects.
\end{defn}

\begin{rem}
  Note that in this definition, $\lana{F}$ must be \emph{strictly}
  (as opposed to \emph{essentially}) surjective on objects, that is,
  for every $C \in \C$ there is some $S \in \Spec$ such that
  $\lana{F}(S) = C$, rather than only requiring $\lana{F}(S) \cong
  C$.  Given this strict surjectivity on objects, it is equivalent to
  require $\lana F$ to be full, as in the definition above, or to be
  (strictly) surjective on the class of all morphisms.
\end{rem}

We are punning on notation a bit here: in the original definition of
anafunctor, $S$ is a set and $\lana{F}$ and $\rana{F}$ are functions on
objects, whereas in this more abstract definition $\Spec$ is a
category and $\lana{F}$ and $\rana{F}$ are functors.  Of course, the two
are closely related: given a span of functors $\Span \C {\lana{F}}
{\Spec} {\rana{F}} \D$, we may simply take the objects of
$\Spec$ as the class of specifications $S$, and the actions of the
functors $\lana{F}$ and $\rana{F}$ on objects as the functions
from specifications to objects of $\C$ and $\D$.  Conversely, given a
class of specifications $S$ and functions $\lana{F}$ and $\rana{F}$, we
may construct the category $\Spec$ with $\Ob \Spec = S$ and with
morphisms $\lana{F}(s) \to \lana{F}(t)$ in $\C$ acting as morphisms $s
\to t$ in $\Spec$.  From $\Spec$ to $\C$, we construct the functor given by $\lana{F}$ on
objects and the identity on morphisms, and the other functor maps $f :
s \to t$ in $\Spec$ to $F_{s,t}(f) : \rana{F}(s) \to \rana{F}(t)$ in $\D$.

Every functor $F : \C \to \D$ can be trivially turned into an
anafunctor \[ \Span \C \Id \C F \D. \] Anafunctors also compose:
given anafunctors $F : \C \to \D$ and $G : \D \to \E$, the key idea is
to take a suitable \emph{product} of their specifications.  In
particular, \todo{finish.  Reference Makkai.}  The same thing can be
defined at a higher level in terms of spans: \[
\xymatrix@@dr{ {} \ar[d]_{\lana F'} \ar[r]^{\rana G'} & \bbb{T} \ar[d]_{\lana G}
  \ar[r]^{\rana G} & \E \\ \Spec \ar[d]_{\lana F} \ar[r]^{\rana F} &
  \D \\ \C } \] $\Cat$ is cocomplete, and in particular has pullbacks,
so we may construct a new anafunctor from $\C$ to $\E$ by taking a
pullback of $\rana F$ and $\lana G$ and then composing appropriately,
as illustrated in the diagram. \todo{Prove this works.}

One is therefore justified in ``mixing and matching'' functors and
anafunctors as convenient, but discussing them all as if they were
regular functors (except when defining a particular anafunctor).  Such
usage can be formalized by turning everything into an anafunctor, and
translating functor operations and properties into corresponding
operations and properties of anafunctors.  However, as we will see, if
we found everything in HoTT, this becomes unnecessary.

\section{Category theory in HoTT}
\label{sec:ct-hott}

\todo{Add explanation of ``\hott{foo}'' terminology.}

\todo{Basic overview of relevant material from Chapter 9 of the HoTT
  book.}

\begin{defn}
  Any $1$-type $T$ gives rise to an \hott{groupoid} $\tygrpd{T}$ where the
  objects are values $a : T$, and $\hom_{\tygrpd{T}}(a,b) \defeq a = b$, that
  is, morphisms from $a$ to $b$ are paths $p : a = b$. \todo{Prove
    this is a groupoid.}
\end{defn}

\subsection{Coends in HoTT}
\label{sec:coends-hott}

\todo{Write me.}

\subsection{Anafunctors in HoTT}
\label{sec:anafunctors-hott}

\todo{Cliques in HoTT too?}

We first \todo{XXX}

One might na\"ively expect the definition of equivalence

\begin{defn}[foo]

\end{defn}

\begin{defn}
  A functor $F : \C \to \D$ is an \term{(adjoint) equivalence} when it
  is left adjoint to a functor $G : \D \to \C$, and
\end{defn}

\todo{(Adjoint) equivalence of categories.}

\todo{Fully faithful and essentially surjective functors are
  equivalent to (adjoint) equivalence of categories, without AC.}

Recall the concise definition of an anafunctor given in
\pref{sec:anafunctors}:

\begin{repdefn}{defn:anafunctor-span}
 \todo{fill me in again}
\end{repdefn}

Porting this definition to HoTT is straightforward.  However, because
of hom-univalence, there is no difference between a \emph{strictly}
surjective functor and an \emph{essentially} surjective one.  Strict
surjectivity of a functor $F : \C \to \D$ on objects requires that for
every $D : \D$ there is some $C : \C$ such that $F\ C = D$, whereas
essential surjectivity requires $F\ C \cong D$; in the presence of
hom-univalence these are equivalent.  So in HoTT we may equivalently
define:
\begin{defn} \label{defn:anafunctor-hott} An \hott{anafunctor} $F : \C
  \to \D$ is a category $\Spec$ together with a span of functors
  $\Span \C {\lana{F}} {\Spec} {\rana{F}} \D$, where $\lana{F}$ is
  fully faithful and essentially surjective.
\end{defn}

However, recall that in HoTT, a fully faithful and essentially
surjective functor automatically gives rise to an equivalence of
categories.  So there is some functor $\lana{F}^{-1}$ which can be
composed with $\rana{F}$, yielding a functor between $\C$ and $\D$. In
fact, the concept of anafunctor is technically unnecessary in HoTT,
made precise as follows:
\begin{prop}
  \hott{functors} and \hott{anafunctors} are equivalent; that is, if
  $\Fun(\C,\D)$ denotes the type of functors from $\C$ to $\D$, and
  $\Ana(\C,\D)$ the type of anafunctors, then \[ \Fun(\C,\D) \iso
  \Ana(\C,\D). \]
\end{prop}
\begin{proof}
  We must define functions in both directions, and show they are
  inverse.

  ($\Longrightarrow$) The functor $F : \C \to \D$ is sent to the span
  $\Span \C {1_\C} \C F \D$. Clearly $1_\C$ is fully faithful and
  essentially surjective, so this is a valid anafunctor.

  ($\Longleftarrow$) The anafunctor $\Span \C {\lana{F}} {\Spec} {\rana{F}} \D$
  is sent to the functor $\lana{F}^{-1} \then \rana{F} : \C \to \D$.

  Round-tripping a functor through an anafunctor is clearly the
  identity; the interesting direction is to show that \[ \Span \C
  {\lana{F}} {\Spec} {\rana{F}} \D \] is equal to \[ \Span \C {1_\C} \C
  {\lana{F}^{-1} \then \rana{F}} \D. \] First, $\Spec = \C$ since $\lana{F}$
  is an equivalence, and equivalent categories are equal \todo{cite}.
  Next, we need to show equality of the functors involved, \emph{when
    appropriately transported by the path $\Spec = \C$}, which in this
  case is ultimately constructed from the equivalence $\lana{F}$.
  Transporting the domain of a functor by an equivalence of categories
  is given by precomposition with the inverse of the equivalence, so
  $\lana{F}_*(\lana{F}) = \lana{F}^{-1} \then \lana{F} = 1_\C$ and
  $\lana{F}_*(\rana{F}) = \lana{F}^{-1} \then \rana{F}$ as desired.
\end{proof}

Although anafunctors are thus technically superfluous, they can still
be a useful tool for getting a handle on certain equivalences, as
shown in the following section.

\todo{Give a very simple example of equivalent categories where it's
  not obvious how to define a functor, and go through anafunctor construction?}

\section{Finiteness}
\label{sec:finiteness}

Finally, we assemble the foregoing material on anafunctors and
category theory in HoTT into a coherent story about representing
evidence of finiteness.

\todo{We start by telling the story in set theory.}

Recall that $\B$ denotes the groupoid of finite sets and bijections,
and $\P$ the groupoid of natural numbers and permutations.  We begin
by discussing the relationship between $\B$ and $\P$, which is more
interesting than it may first seem.

In classical category theory, $\P$ is a \term{skeleton} of
$\B$---roughly, we may think of it as the result of replacing each
equivalence class of isomorphic objects in $\B$ with a single object.
In this case, we can identify each equivalence class of isomorphic
finite sets with a \emph{size}, the only property of sets which is
invariant under isomorphism.

It is a simple result in classical category theory that every category
is equivalent to its skeletons.  However, after the foregoing
discussion of cliques and anafunctors, the idea of quotienting out by
equivalences classes of isomorphic objects ought to make us
squeamish---and, indeed, a proof that $\B$ and $\P$ are equivalent
requires AC.

In more detail, it is easy to define a functor $\fin - : \P \to \B$
which sends $n$ to $\fin n$ and preserves morphisms; defining an
inverse functor $\size - : \B \to \P$ is more problematic. We can send
each set $S$ to its size $\size S$, but we must send a bijection $S
\bij T$ to a bijection $\fin{\size S} \bij \fin{\size T}$, and there
is no obvious way to pick one.  If we use AC, we can pick an arbitrary
bijection $\varphi_S : S \bij \fin{\size S}$ for each finite set $S$,
matching up $S$ with a canonical set of size $\size S$.  Given $\alpha
: S \bij T$ we can then construct $\xymatrix{ \fin{\size S}
  \ar[r]^-{\varphi_S^{-1}} & S \ar[r]^\alpha & T \ar[r]^-{\varphi_T} &
  \fin{\size T}}$.  Again, this use of AC is ``benign'' in the sense
that any two sets of choices yield equivalent functors \todo{need to
  double-check this, maybe add a bit more explanation}.

\todo{Explain how to avoid AC using well-ordering of hereditarily
  finite sets.  But this does not have a natural counterpart in a
  structural set theory or in type theory.}

We can avoid the use of AC by constructing an anafunctor $\size - : \B
\to \P$ instead of a functor.  In particular, as the class of
specifications $||\size{}||$, we choose the class of all bijections
$\sum_{T \in \B} (T \bij \fin{\size T})$.  The function $\sigma :
||\size{}|| \to \Ob \B$ simply forgets the chosen bijection,
$\sigma(T,\varphi) = T$, and $\tau : ||\size{}|| \to \Ob \P$ sends
finite sets to their size, $\tau(T,\varphi) = \size T$.  Note that
both $\sigma$ and $\tau$ ignore $\varphi$, which is instead needed to
define the action of $\size{}$ on morphisms.  In particular, given
$\alpha : S \bij T$ in $\B$, we define $\sizesymb_{(S,\varphi_S),
  (T,\varphi_T)}(\alpha) = \varphi_S^{-1} \then \alpha \then
\varphi_T$, which can be visualized as
\[
\xymatrix{S \ar[d]_\alpha & \fin{\size S} \ar[l]_-{\varphi_S^{-1}}
  \ar@@{.>}[d]^{\size \alpha} \\
  T \ar[r]_-{\varphi_T} & \fin{\size T} }.
\]
Proof that $\size{}$ preserves identities and composition is given by
the following diagrams:
\[
   \vcenter{
   \xymatrix{
     S \ar[d]_\id &
     \fin{\size S} \ar[l]_-{\varphi_S^{-1}} \ar@@{.>}[d]^{\size \id}
   \\
   S \ar[r]_-{\varphi_S}
   & \fin{\size S}
   }
   }
   \qquad\qquad
   \vcenter{
   \xymatrix{
     S \ar[d]_\alpha &
     \fin{\size S} \ar[l]_-{\varphi_S^{-1}} \ar@@{.>}[d]^{\size \alpha}
   \\
     T \ar[d]_\beta \ar@@<.2em>[r]^-{\varphi_T} &
     \fin{\size T} \ar@@<.2em>[l]^-{\varphi_T^{-1}}
     \ar@@{.>}[d]^{\size \beta}
   \\
     U \ar[r]^-{\varphi_U} &
     \fin{\size U}
   }
   }
   =
   \vcenter{
     \xymatrix{
       S \ar[d]_{\alpha \then \beta} &
       \fin{\size S} \ar[l]_-{\varphi_S^{-1}} \ar@@{.>}[d]^{\size
         (\alpha \then \beta)}
     \\
       U \ar[r]^-{\varphi_U} &
       \fin{\size U}
     }
   }
\]
The left-hand diagram represents the definition of $\size \id$, in
which $\varphi_S$ and its inverse cancel, resulting in the identity.
The center diagram shows the result of composing $\size \alpha$ and
$\size \beta$; because $\varphi_T$ cancels with $\varphi_T^{-1}$ it is
the same as the definition of $\size (\alpha \then \beta)$ (the
right-hand diagram).

We now turn to developing counterparts to the groupoids $\P$ and $\B$
in type theory.  First, a necessary lemma:
\begin{lem} \label{lem:equiv-pres-set}
  Equivalence preserves sets, that is, if $A$ and
  $B$ are sets, then so is $A \iso B$.
\end{lem}
\begin{proof}
  $(A \iso B) \iso ((f : A \to B) \times
  \cons{isequiv}(f))$, where $\cons{isequiv}(f)$ is a mere proposition
  expressing the fact that $f$ is an equivalence (\ie has a suitable
  inverse).  This is a set since $\cons{isequiv}(f)$ is a mere
  proposition and hence a set (\todo{cite}), $A \to B$ is a set
  whenever $B$ is (\todo{cite}), and $\times$ takes sets to sets
  (\todo{cite}).
\end{proof}

\begin{cor}
  If $A$ and $B$ are sets, then so is $A = B$.
\end{cor}
\begin{proof}
  Immediate from univalence and \pref{lem:equiv-pres-set}.
\end{proof}

Constructing a type-theoretic counterpart to $\P$ is
now straightforward.
\begin{defn}
  $\PT$ is the \hott{groupoid} where
  \begin{itemize}
  \item the objects are values of type $\N$, and
  \item the morphisms $\mor m n$ are equivalences of type $\Fin m \iso
    \Fin n$.
  \end{itemize}
\end{defn}
It is easy to check that this satisfies the axioms for an
\hott{category}, the salient points being that $\Fin m \iso \Fin n$ is
a set by \pref{lem:equiv-pres-set}, and hom-univalence is just
univalence.

Developing a counterpart to $\B$ is more subtle.  The first order of
business is to decide how to port the concept of a ``finite set''.
Generally, ``a set with property X'' ports to type theory as ``a type
paired with constructive evidence of property X'' (or perhaps ``a
$0$-type paired with evidence of X'', depending how seriously we want
to take the word \emph{set}); so what is constructive evidence of
finiteness? This is not \latin{a priori} clear, and indeed, there are
several possible answers \citep{finite}. However, the discussion
above, where bijections $S \bij \fin{\size S}$ played a prominent
role, suggests that we adopt the simplest option,
\term{cardinal-finiteness}.
\begin{defn}
  A set (type) $A$ is \term{cardinal-finite} iff there exists some $n
  \in \N$ and a bijection $A \bij \fin n$; $n$ is called the size or
  cardinality of $A$.
\end{defn}
Our first try at encoding this in type theory is
\[ \FinType \defeq (A : \Type) \times (n : \N) \times (A \iso \Fin n). \]

We would like to build a groupoid having such finite types as objects,
and equivalences between them as morphisms.  Recall that given some
$1$-type $A$, the groupoid $\tygrpd{A}$ has values $(a : A)$ as its
objects and paths $a = b$ as its morphisms.  For this to be
applicable, we must check that $\FinType$ is a $1$-type. In fact, it
turns out that it is a $0$-type, \ie a set---but this won't do,
because the resulting groupoid is therefore \emph{discrete}, with at
most one morphism between each pair of objects. $\B$, of course, has
$n!$ distinct morphisms between any two sets of size $n$.
Intuitively, the problem is that paths between objects in
$\tygrpd{\FinType}$ involve not just the types in question but also
the evidence of their finiteness, so that a path between two finite
types requires them to be not just equivalent as types, but also
``finite in the same way''.

The situation can be pictured as shown in \pref{fig:fin-equiv}. The elements
of types $A_1$ and $A_2$ are shown on the sides; the evidence of their
finiteness is represented by bijections between their elements and the
elements of $\Fin n$, shown along the bottom.  The catch is that the diagram
necessarily contains only triangles: corresponding elements of $A_1$ and $A_2$
must correspond to the same element of $\Fin n$ on the bottom row.  Therefore,
there are only two degrees of freedom. Once the evidence of finiteness is
determined, there is only one valid correspondence between $A_1$ and
$A_2$---but there ought to be $n!$ such correspondences.
\begin{figure}
  \centering
  \begin{diagram}[width=150]
import           Data.Bits                      (xor)
import           SpeciesDiagrams

mkList n d f = hcat' (with & sep .~ 2 & catMethod .~ Distrib)
  (zipWith named (map f [0::Int ..]) (replicate n d))

n :: Int
n = 8

dia = decorateLocatedTrail (triangle (fromIntegral (n+2)) # rotateBy (1/2))
      [ "l1"  ||> (l1 # rotateBy (-1/3))
      , "fin" ||> fin
      , "l2"  ||> (l2 # rotateBy (1/3))
      ]
      # mkConnections
      # centerXY # pad 1.2
      # flip appends
        [ (unit_Y                  , text' 4 "Fin n")
        , (unit_Y # rotateBy (-1/3), text' 4 "L₁"   )
        , (unit_Y # rotateBy (1/3) , text' 4 "L₂"   )
        ]
  where
    fin = mkList n dot (`xor` 1) # centerXY
    l1  = mkList n dot id # centerXY
    l2  = mkList n dot ((n-1) -) # centerXY
    dot = circle 0.5 # fc grey
    mkConnections = applyAll
      [  withNames [a .> i, b .> i] $ \[p,q] -> atop (location p ~~ location q)
      || (a,b) <- take 3 . (zip <*> tail) . cycle $ ["l1", "fin", "l2"]
      ,  i <- [0 .. (n-1)]
      ]
  \end{diagram}
  \caption{A path between inhabitants of $\FinType$ contains only
    triangles}
  \label{fig:fin-equiv}
\end{figure}

\begin{prop}
  $\FinType$ is a set, that is, for any $X, Y : \FinType$,
  if $p_1, p_2 : X = Y$ then $p_1 = p_2$.
\end{prop}

\begin{proof}[Proof (sketch)]
  A path $(A_1, n_1, e_1) = (A_2, n_2, e_2)$ is equivalent to $(p :
  A_1 = A_2) \times (q : n_1 = n_2) \times (q_*(p_*(e_1)) = e_2)$.
  The transport of $e_1$ by $p$ is given by the composition $e_1 \comp
  (\ua^{-1}(p))^{-1}$, but this essentially means that $p$ is uniquely
  determined by $e_1$ and $e_2$.
\end{proof}

The underlying problem is that $\FinType$ does not actually do a very
good job at encoding what classical mathematicians usually mean by
``finite set''.  Saying that a set $A$ is finite with size $n$ does
not typically imply there is some specific, chosen bijection $A \bij
\fin n$, but merely that $A$ \emph{can be put} in bijection with $\fin
n$, with no mention of a specific bijection.  This is justified by the
fact that, up to isomorphism, any bijection $A \bij \fin n$ is just as
good as any other.

This suggests a better encoding of finiteness in type theory, with a
first attempt given by \[ \FinTypeT' \defeq (A : \Type) \times
\ptrunc{(n : \N) \times (A \iso \Fin n)}, \] making use of
propositional truncation to encode the fact that there \emph{merely
  exists} some size $n$ and an equivalence between $A$ and $\Fin n$,
but without exposing a precise choice.  The finiteness evidence is now
irrelevant to paths in $\FinTypeT'$, since there is always a path
between any two elements of a truncated type.  We also note the
following:
\begin{prop}
  For any type $A$, \[ \ptrunc{(n : \N) \times (A \iso \Fin n)} \iso
  (n : \N) \times \ptrunc{A \iso \Fin n}. \]
\end{prop}
This says that the size $n$ of a finite type may be freely moved in
and out of the propositional truncation.  Practically, this means we
may freely refer to the size of a finite type without worrying about
how it is being used (in contrast, the value of the equivalence $A
\iso \Fin n$ may only be used in constructing mere propositions).
The proof hinges on the fact that $(n : \N) \times \ptrunc{A \iso \Fin
  n}$ is a mere proposition; intuitively, if a type is finite at all,
there is only one possible size it can have, so putting $n$ inside the
truncation does not really hide anything.
\begin{proof}
  We must exhibit a pair of inverse functions between the given types.
  A function from right to left is given by \[ f(n, \ptruncI e) =
  \ptruncI{(n,e)}, \] where pattern matching on $\ptruncI e :
  \ptrunc{A \iso \Fin n}$ is shorthand for an application of the
  recursion principle for propositional truncation.  Recall that this
  recursion principle only applies in the case that the result is a
  mere proposition; in this case, the result is itself a propositional
  truncation which is a mere proposition by construction.

  In the other direction, define \[ g(\ptruncI{(n, e)}) = (n,\ptruncI
  e), \] which is clearly inverse to $f$.  It remains only to show
  that the implicit use of recursion for propositional truncation is
  justified, \ie that $(n : \N) \times \ptrunc{A
    \iso \Fin n}$ is a mere proposition.

  We must show that any two values $(n_1, e_1), (n_2, e_2) : (n : \N)
  \times \ptrunc{A \iso \Fin n}$ are propositionally equal.  Since
  $e_1$ and $e_2$ are mere propositions, it suffices to show that $n_1
  = n_2$.  This equality is itself a mere proposition ($\N$ is a set,
  which follows from its induction principle), so we may apply the
  recursion principle for propositional truncation to $e_1$ and $e_2$,
  giving us equivalences $A \iso \Fin n_1$ and $A \iso \Fin n_2$ to
  work with.  By symmetry and transitivity, $\Fin n_1 \iso \Fin n_2$.
  This implies $n_1 = n_2$, by double induction on $n_1$ and $n_2$:
  \begin{itemize}
  \item If both $n_1$ and $n_2$ are zero, the result is immediate.
  \item The case when one is zero and the other a successor is
    impossible.  In particular, taking the
    equivalence in the appropriate direction gives a function $\Fin
    (\suc \dots) \to \Fin \zero$, which can be used to produce an
    element of $\Fin \zero = \bot$, from which anything follows.
  \item In the case when both are a successor, we have
    $\Fin{(\suc{n_1'})} \iso \Fin{(\suc{n_2'})}$, which is equivalent
    to $\top + \Fin{n_1'} \iso \top + \Fin{n_2'}$.  If we can conclude
    that $\Fin{n_1'} \iso \Fin{n_2'}$, the inductive hypothesis then
    yields $n_1' = n_2'$, from which $\suc{n_1'} = \suc{n_2}'$ follows
    immediately.  The implication $(\top + \Fin{n_1'} \iso \top +
    \Fin{n_2'}) \to (\Fin{n_1'} \iso \Fin{n_2'})$ is true, but not
    quite as straightforward to show as one might think! In
    particular, the equivalence may not match the $\top$ values with
    each other, so some nontrivial shuffling must be done to construct
    a matching between the elements of $\Fin{n_1'}$ and $\Fin{n_2'}$.
    This may be accomplished via the \term{Gordon complementary
      bijection principle}. \todo{more on which later??}
  \end{itemize}
\end{proof}

There is still one remaining problem, which is that $\FinTypeT'$ is
not a $1$-type, and hence $\tygrpd{-}$ does not apply. To solve this
we may simply restrict to $0$-types $A$. This yields our final
definition:

\begin{defn}
  The type of finite sets is given by \[ \FinTypeT \defeq (A : \Type)
  \times \isSet(A) \times \isFinite(A), \] where \[ \isFinite(A)
  \defeq \ptrunc{(n : \N) \times (A \iso \Fin n)}. \]
\end{defn}
We will often abuse notation and write $A : \FinTypeT$ instead of
$(A,s,f) : \FinTypeT$ where $s : \isSet(A)$ and $f : \isFinite(A)$.
Since $\isSet(A)$ and $\isFinite(A)$ are mere propositions, paths
between $\FinTypeT$ values are characterized by paths between their
underlying types. Since those types must be sets, \ie $0$-types,
$\FinTypeT$ is consequently a $1$-type.

\begin{defn}
  $\BT$ is defined by \[ \BT \defeq \tygrpd{\FinTypeT}, \] the
  groupoid of cardinal-finite types and paths bewteen them.
\end{defn}

\begin{defn}
  We can easily define a functor $\fin - : \PT \to \BT$: on objects,
  it sends $n$ to $\Fin n$, along with proofs that it is a set and
  finite (using the identity equivalence for the latter).  On
  morphisms, it sends $f : \Fin m \iso \Fin n$ to $\ua\ f : \Fin m =
  \Fin n$.
\end{defn}

However, it is not at all obvious how to directly define a functor
$\size - : \BT \to \PT$. Just as with $\B \to \P$, defining its action
on morphisms requires a specific choice of equivalence $A \iso \Fin
n$. The objects of $\BT$ contain such equivalences, in the proofs of
finiteness, but they are propositionally truncated; the type of
functors $\BT \to \PT$ is decidedly not a mere proposition, so it
seems the recursion principle for truncation does not apply.

We can, however, define an anafunctor $\size - : \BT \to \PT$,
similarly to $\size - : \B \to \P$\footnote{We overload $\size{}$ to
  serve as the name of both anafunctors (as well as set cardinality);
  this should not cause confusion as they are never used in similar
  contexts.}.
\todo{Redo this to use the span definition.}
\begin{defn}
  The anafunctor $\size - : \BT \to \PT$ is given by:
  \begin{itemize}
  \item the class of specifications $\FinType$;
  \item a function $\sigma : \FinType \to \BT$ which ``forgets'' the
    equivalences by injecting them into the propositional truncation,
    \ie \[ \sigma(S,m,\varphi) = (S, m, \ptruncI{\varphi}); \]
  \item a function $\tau : \FinType \to \PT$ which projects out the
    size, \[ \tau(S,m,\varphi) = m; \]
  \item and, for $f : \mor {(S,m,\psi_S)} {(T,n,\psi_T)}$, that is, $f
    : S \iso T$,
    \[ \sizesymb_{(S,m,\varphi_S),(T,n,\varphi_T)}(f) =
    \varphi_S^{-1} \then f \then \varphi_T. \]
  \end{itemize}
  The proof that this is a valid anafunctor is analogous to the proof
  for the anafunctor $\B \to \P$. \todo{Or do we get this for free?}
\end{defn}

\begin{prop}
  The pair of (ana)functors $\BackForth \PT {\fin -} {\size{}} \BT$
  constitutes an (ana)equivalence between the groupoids $\PT$ and
  $\BT$.

\begin{proof}
  \todo{Redo this proof using composition of anafunctors. Intuitively,
    it shouldn't actually change too much but the details need to be
    checked; also, the metavariable conventions have changed.}
  $\size{\fin -}$ is by definition the identity functor.  The
  interesting direction is $\fin{\size -}$.
  \begin{itemize}
  \item On objects, $\fin{\size {(A,m,i)}} \equiv \fin{m} \equiv (\Fin
    m, m, \id)$, and
  \item on morphisms, $e : \mor {(A,m,i)} {(B,n,j)}$ is sent to
    $\fin{\size e} \equiv \fin{i \then e \then j^{-1}} \equiv i \then e \then j^{-1}$.
  \end{itemize}
  We must exhibit a natural isomorphism $\alpha : \all{L} {L \to
    \fin{\size L}}$.  $\alpha_{(A,m,i)}$ must be a morphism in $\BT$
  from $(A,m,i)$ to $(\Fin m, m, \id)$, that is, an equivalence $A
  \iso \Fin m$.  Therefore we define $ \alpha_{(A,m,i)} \defeq
  i^{-1}$.  Naturality of $\alpha$ is given by the diagram
  \[ \xymatrix{
         (A,m,i) \ar[r]^-{i^{-1}} \ar[d]_e
         &
         (\Fin m, m, \id) \ar[d]^{i \then e \then j^{-1}}
       \\
         (B,n,j) \ar[r]_-{j^{-1}} & (\Fin n, n, \id)
     }
  \]
  which commutes by inspection.  Finally, we note that any natural
  transformation between functors whose codomain is a groupoid is
  automatically an isomorphism.
\end{proof}
\end{prop}
