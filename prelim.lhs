%% -*- mode: LaTeX; compile-command: "mk" -*-

%include polycode.fmt
%include forall.fmt

%format === = "\oldequiv"

\chapter{Preliminaries}
\label{chap:prelim}

\todo{mention logical equivalence.}

\todo{Explicitly discuss categorical monoids in HoTT. Note that strict
  vs non-strict monoids is a non-issue.}

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

\todo{Redo this based on splitting out another chapter.}
The material in \pref{sec:basic}, \pref{sec:HoTT}, and
\pref{sec:category-theory}, though by no means basic, is fairly
standard, so readers with a good background in the subjects covered
may safely skip them without too many surprises.  Even those readers
who are not familiar with some of the material may find it more
productive to begin reading \pref{chap:species} and refer back to this
chapter as needed. On the other hand, the material in
\Sect\Sect\ref{sec:AC}--\ref{sec:finiteness-hott} is somewhat less
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

\todo{definitional equality}

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
seriously, generalizing equality to isomorphism in a coherent way.

We begin our brief tour of HoTT with its syntax.

\subsection{Terms and types}

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

Although Agda notation~\citep{Agda} is mostly used in this dissertation
for dependent pairs and functions, the traditional notations $\sum_{x
  : A} B(x)$ and $\prod_{x:A} B(x)$ (instead of $(x:A) \times B(x)$
and $(x:A) \to B(x)$, respectively) are sometimes used for
emphasis. As usual, the abbreviations $A \times B$ and $A \to B$
denote non-dependent (\ie when $x$ does not appear free in $B$) pair
and function types, respectively. \later{implicit quantification? Do
  we need this? Also, to reduce clutter, we sometimes make use of
  implicit quantification: free type variables in a type---like $A$
  and $B$ in $A \times (B \to \N)$---are implicitly universally
  quantified, like $(A : \Type) \to (B : \Type) \to A \times (B \to
  \N)$.}

\subsection{Equality}

HoTT distinguishes between two different types of equality:
\later{reference ``On the meanings of the logical constants'' or some
  other suitable thing talking about judgments vs propositions?}
\begin{itemize}
\item \term{Judgmental} equality, denoted $x \jeq y$, is defined via
  a collection of judgments stating when things are equal to one
  another, and encompasses things like basic rules of computation. For
  example, the application of a lambda term to an argument is
  judgmentally equal to its $\beta$-reduction.  Judgmental equality is
  reflexive, symmetric, and transitive as one would expect.
  Note, however, that judgmental equality is not reflected as a
  proposition in the logical interpretation of types, so it is not
  possible to reason about or to prove judgmental equalities
  internally to HoTT.
\item \term{Propositional} equality.  Given $x, y : A$, we write $x
  =_A y$ for the proposition that $x$ and $y$ are equal (at the type
  $A$).  The $A$ subscript may also be omitted, $x = y$, when it is
  clear from the context. Unlike judgmental equality, where $x \jeq y$
  is a \term{judgment}, the propositional equality $x = y$ is a
  \emph{type} (or a \emph{proposition}) whose inhabitants are evidence
  or \emph{proofs} of the equality of $A$ and $B$.  Thus propositional
  equalities can be constructed and reasoned about \emph{within} HoTT.
  Inhabitants of $x = y$ are often called \term{paths} from $x$ to
  $y$; the intuition, taken from homotopy theory, is to think of paths
  between points in a topological space.  The important point about
  this intuition is that a path from a point $x$ to a point $y$ does
  not witness the fact that $x$ and $y$ are literally the \emph{same}
  point, but rather specifies a \emph{process} for getting from one to
  the other.  As we will see, the analogue of this intuition in type
  theory is the fact that a path of type $x = y$ can have
  \emph{nontrivial computational content} specifying how to convert
  between $x$ and $y$.

  Note that it is possible (and often useful!) to have nontrivial
  higher-order paths, \ie paths between paths, paths between paths
  between paths, and so on.
\end{itemize}

\subsection{Path induction}

To make use of a path $p : x = y$, one may use the induction principle
for paths, or \term{path induction}.  Path induction applies when is
trying to prove a statement of the form
\begin{equation} \label{eq:path-ind-form}
\all {x,y} {(p : x = y) \to
  P(p,x,y)}.
\end{equation}
There is also an equivalent induction principle, \term{based path
  induction}, which applies when proving a statement of the form \[
\all x {(x = y) \to P x}, \] where $y$ is fixed.  Crucially, however,
neither can be used to prove statements of the form $(x = y) \to P$
where both $x$ and $y$ are fixed.

For the precise details of (based) path induction, see the HoTT
book~\citep{hottbook}; the simple intuition suffices for this work: to
prove \ref{eq:path-ind-form} it suffices to assume that $p$ is $\refl$
and that $x$ and $y$ are literally the same, \ie it suffices to prove
$P(\refl,x,x)$ for an arbitrary $x$.

It is important to note that this does \emph{not} imply all paths are
equal to \refl!  It simply expresses that all paths must suitably
``act like'' \refl, inasmuch as proving a statement holds for \refl is
enough to guarantee that it will hold for all paths, no matter how
they are derived or what their computational content.

Path induction has some immediate consequences.  First, it guarantees
that functions are always functorial with respect to propositional
equality. That is, if $e : x = y$ is a path between $x$ and $y$, and
$f$ is a function of an appropriate type, then it is possible to
construct a proof that $f(x) = f(y)$ (or a suitable analogue in the
case that $f$ has a dependent type).  Indeed, this is not hard to
prove via path induction: it suffices to show that one can construct a
proof of $f(x) = f(x)$ in the case that $e$ is \refl, which is easily
done using \refl again.  Given $e : x = y$ we also have $P(x) \to
P(y)$ for any type family $P$, called the \term{transport} of $P(x)$
along $e$ and denoted $\transport{P}{e}$, or simply $e_*$ when $P$ is
clear from context.  For example, if $e : A = B$ then $\transport{X
  \mapsto X \times (X \to C)}{e} : A \times (A \to C) \to B \times (B
\to C)$.  Transport also follows easily from path induction: it
suffices to note that $\idT : P(x) \to P(x)$ in the case when $e =
\refl$.

\subsection{Equivalence and univalence}

There is also a third sort of equality, namely, \term{equivalence}.
An equivalence between $A$ and $B$, written $A \equiv B$ is
(essentially) a pair of functions $f : A \to B$ and $g : B \to A$,
along with a proof that $f$ and $g$ are inverse.\footnote{The precise
  details are more subtle \cite[chap.  4]{hottbook}, but unimportant
  for the purposes of this work.  The key takeaway is that $A \equiv
  B$ both implies and is implied by the existence of an inverse pair
  of functions, although this does not make a good \emph{definition}
  of equivalence because of problems with coherence of higher paths.}
The identity equivalence is denoted by $\id$, and the composition of
$h : B \equiv C$ and $k : A \equiv B$ by $h \comp k : A \equiv C$.  As
a notational shortcut, equivalences of type $A \equiv B$ can be used
as functions $A \to B$ where it does not cause confusion.

HoTT's main novel feature is the \emph{univalence axiom}, which states
that equivalence is equivalent to propositional equality, that is, $(A
\equiv B) \equiv (A = B)$. One direction, $(A = B) \to (A \equiv B)$,
follows easily from the properties of equality; the interesting
direction, which must be taken as an axiom, is $\ua : (A \equiv B) \to
(A = B)$, which formally encodes the \emph{principle of
  equivalence}~\citep{principle-of-equivalence}, namely, that sensible
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
    sets}~\citep{bezem2014model}.}, so using it to give a computational
interpretation of species may seem suspect. Note, however, that $\ua$
satisfies the $\beta$ law \mbox{$\transport{X \mapsto X}{\ua(f)} =
  f$}. So univalence introduces no computational problems as long as
applications of $\ua$ are only ultimately used via
$\mathsf{transport}$.  In particular, sticking to this restricted
usage of $\ua$ still allows a convenient shorthand: packaging up an
equivalence into a path and then transporting along that path results
in ``automatically'' inserting the equivalence and its inverse in all
the necessary places throughout the term. For example, let $P(X)
\hdefeq X \times (X \to C)$ as in the previous example, and suppose $e
: A \equiv B$, so $\ua\ e : A = B$.  Then $\transport P {\ua(e)} :
P(A) \to P(B)$, and in particular $\transport P {\ua(e)} \pair a g =
\pair {e(a)}{g \comp e^{-1}}$, which can be derived mechanically by
induction on the shape of $P$.

\subsection{Propositions, sets, and $n$-types}
\label{sec:n-types}

As noted previously, it is possible to have arbitrary higher-order
path structure: paths between paths, paths between paths between
paths, and so on.  This offers great flexibility but also introduces
many complications.  It is therefore useful to have a vocabulary for
explicitly talking about types with limited higher-order structure.

\begin{defn}
  A \term{proposition}, or \term{$(-1)$-type}, is a type for which any
  two inhabitants are propositionally equal.
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
``Standard'' inductive types such as \N, \Fin n, and so on, are sets,
although proving this takes a bit of work. Generally, one shows via
induction that paths between elements of the type are equivalent to an
indexed type given by $\TyZero$ when the elements are different and
$\TyOne$ when they are the same; $\TyZero$ and $\TyOne$ are mere
propositions and hence so is the type of paths. See the HoTT book for
proofs in the particular case of \N, which can be adapted to other
inductive types as well~\citep[\Sect 2.13, Example 3.1.4, \Sect
7.2]{hottbook}.

As noted above, propositions and sets are also called, respectively,
$(-1)$-types and $0$-types.  As these names suggest, there is an
infinite hierarchy of $n$-types (beginning at $n = -2$ for historical
reasons) which have no interesting higher-order path structure above
level $n$.  As an example of a $1$-type, consider the type of all
sets, \[ \SetT \hdefeq (A : \Type) \times \isSet(A), \] where
$\isSet(A) \hdefeq (x,y:A) \to (p,q:x = y) \to (p = q)$ is the
proposition that $A$ is a set.  Given two elements $A, B : \msf{Set}$
it is not the case that all paths $A = B$ are equal; such paths
correspond to bijections between $A$ and $B$, and there may be many
such bijections.

Note that $\isSet(A)$ itself is always a mere proposition for any type
$A$ (see Lemma 3.3.5 in the HoTT book).

\subsection{Truncation}

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

\subsection{Why HoTT?}
\label{sec:why-hott}

In the context of this dissertation, homotopy type theory is much more
than just a convenient choice of concrete type theory to work in.  It
is, in fact, quite central to this work.  It is therefore appropriate
to conclude with a summary of specific ways that this work benefits
from its use.  Many of these points are explored in more detail later
in the dissertation.
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
  model the concept of \emph{finiteness} (\pref{sec:finiteness-hott}).
\item Homotopy type theory allows doing category theory without using
  the axiom of choice (\pref{sec:AC}, \pref{sec:ct-hott}), which is
  essential in a constructive or computational setting.
\end{itemize}

Although not its main goal, I hope that this work can serve as a
good example of the ``practical'' application of HoTT and its benefits
for programming.  Much of the work on HoTT has so far been aimed at
mathematicians rather than computer scientists---appropriately so,
since mathematicians tend to be more skeptical of type theory in
general and constructive foundations in particular. However, new
foundations for constructive mathematics must almost by necessity have
profound implications for the foundations of programming as
well~\citep{martin1982constructive}.

\section{Category theory}
\label{sec:category-theory}

\todo{Note notation for natural transformations---sometimes use $\nt F
  G$, sometimes just $F \to G$.}
\todo{Add section about \Hask}

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
\item $\Grp$, the category of groups and group homomorphisms.
\item $\Vect_K$, the category of vector spaces over the field $K$,
  together with linear maps.
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

\paragraph{Sums and products}

\todo{Definitions?  Notation for universal morphisms; link to
  Haskell.  Note $\beta$ laws and so on.}

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
carries over to functor categories; for example, $\C^{\D + \E} \equiv
\C^\D \times \C^\E$, $(\C \times \D)^\E \equiv \C^\E \times \D^\E$, and
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
  = map (\e -> text [e] <> circle 1 # lc (colors !! i)) elts
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
  # lwO 0.7

aOpts = with & arrowTail .~ dart'
  \end{diagram}
  \caption{An element of $\Set^X$ or $\Set/X$}
  \label{fig:discrete-slice}
\end{figure}

\paragraph{Equivalence of categories}

When are two categories ``the same''?  In traditional category theory,
founded on set theory, there are quite a few different definitions of
``sameness'' for categories.  There are many different notions of
``equality'' (isomorphism, equivalence, \dots), and they often do not
correspond to the underlying equality on sets, so one must carefully
pick and choose which notions of equality to use in which situations
(and some choices might be better than others!).  Many concepts come
with ``strict'' and ``weak'' variants, depending on which version of
equality is being used.  Maintaining the principle of equivalence in
this setting requires hard work and vigilence.

A na\"ive first attempt is as follows:
\begin{defn} \label{defn:cat-iso}
  Two categories $\C$ and $\D$ are \term{isomorphic} if
  there are inverse functors $\BackForth \C F G \D$, such that $GF =
  1_\C$ and $FG = 1_\D$.
\end{defn}
This definition has the right idea in general, but it is subtly
flawed.  In fact, it is somewhat ``evil'', in that it talks about
\emph{equality} of functors ($GF$ and $FG$ must be \emph{equal to} the
identity).  However, two functors $H$ and $J$ can be isomorphic
without being equal, if there is a natural isomorphism between
them---that is, a pair of natural transformations $\phi : \nt H J$ and
$\psi : \nt J H$ such that $\phi \circ \psi$ and $\psi \circ \phi$ are
both equal to the identity natural transformation.\footnote{The astute
  reader may well ask: but how do we know \emph{this} is a non-evil
  definition of isomorphism between \emph{functors}?  Is it turtles
  all the way down (up)?  This is a subtle point, but it turns out
  that it is not evil to talk about equality of natural
  transformations, since for the usual notion of category there is no
  higher structure after natural transformations, \ie no nontrivial
  morphisms (and hence no nontrivial isomorphisms) between natural
  transformations.} For example, consider the functors given
by the Haskell types
\begin{spec}
data Rose a = Node a [Rose a]
data Fork a = Leaf a | Fork (Fork a) (Fork a)
\end{spec}
These are obviously not \emph{equal}, but they are isomorphic, in the
sense that there are natural transformations, \ie polymorphic
functions, |rose2fork :: forall a. Rose a -> Fork a| and |fork2rose ::
forall a. Fork a -> Rose a|, such that |rose2fork . fork2rose === id|
and |fork2rose . rose2fork === id| \citep{yorgey-2010-species, hinze2010reason}.

Here, then, is a better definition:
\begin{defn} \label{defn:cat-equiv} Categories $\C$ and $\D$ are
  \term{equivalent} if there are functors $\BackForth \C F G \D$ which
  are inverse up to natural isomorphism, that is, there are natural
  isomorphisms $GF \iso 1_\C$ and $FG \iso 1_\D$.
\end{defn}

So the compositions of the functors $F$ and $G$ do not \emph{literally}
have to be the identity functor, but only (naturally) \emph{isomorphic} to
it.  This does turn out to be a well-behaved notion of sameness for
categories. \todo{citation, or pointer to further reading.}

There is much more to say about equivalence of categories;
\pref{sec:AC} picks up the thread with a much fuller discussion of the
relationships among equivalence of categories, equality, the axiom of
choice, and classical versus constructive logic.

\paragraph{Adjunctions}

The topic of \term{adjunctions} is much too large to adequately cover
here.  For the purposes of this dissertation, the most important form
of the definition to keep in mind is that a functor $F : \C \to \D$ is
\term{left adjoint} to $G : \D \to \C$ (and $G$ \term{right adjoint}
to $F$), notated $F \adj G$, if and only if \[ \Hom[\D]{F A}{B} \iso
\Hom[\C]{A}{G B}, \] that is, if there is some natural isomorphism
matching morphisms $F A \to B$ in the category $\D$ with morphisms $A
\to G B$ in $\C$.

One example familiar to functional programmers is \emph{currying}, \[
(A \times B \to C) \iso (A \to (B \to C)), \] which corresponds to the
adjunction \[ (- \times B) \adj (B \to -). \]

\paragraph{Monads}

Monads are familiar to many, and do not play a very important role in
this work, so only a few words need to be said.

\todo{monad basics. Kleisli category.}

\subsection{Monoidal categories}
\label{sec:monoids}

Recall that a \term{monoid} is a set $S$ equipped with an associative
binary operation \[ \mappend : S \times S \to S \] and a distinguished
element $\mempty : S$ which is an identity for $\mappend$. (See, for
example, \citet{yorgey2012monoids} for a discussion of monoids in the
context of Haskell.)  A \term{monoidal category} is the appropriate
``categorification'' of the concept of a monoid, \ie with the set $S$
replaced by category, the binary operation by a bifunctor, and the
equational laws by natural isomorphisms.
\begin{defn}
  Formally, a \term{monoidal category} is a category $\C$ equipped with
  \begin{itemize}
  \item a bifunctor $\otimes : \C \times \C \to \C$;
  \item a distinguished object $I \in \C$;
  \item a natural isomorphism $\alpha : \all{ABC}{(A \otimes B)
      \otimes C \iso A \otimes (B \otimes C)}$; and
  \item natural isomorphisms $\lambda : \all{A}{I \otimes A \iso
      A}$ and $\rho : \all{A}{A \otimes I \iso A}$.
  \end{itemize}
  $\alpha$, $\lambda$, and $\rho$ must additionally satisfy some
  ``coherence axioms'', which ensure that parallel isomorphisms
  constructed from $\alpha$, $\lambda$, and $\rho$ are always equal;
  for details, see \citet[Chapter VII]{mac1998categories} \todo{fill in page or
    section number}.

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
  natural isomorphism $\gamma : \all{AB}{A \otimes B \iso B \otimes
    A}$.
\end{defn}

For example, $\Set$ is symmetric monoidal under both Cartesian product
and disjoint union. As an example of a non-symmetric monoidal
category, consider the functor category $[\C,\C]$, with the monoid given
by composition of functors.

\begin{defn}
  A monoidal category $\C$ is \term{closed} if there some bifunctor $[-,-]
  : \C^\op \times \C \to \C$ such that there is a natural
  isomorphism \[ \all{ABC}{(\Hom {A \otimes B} C) \iso (\Hom A
    {[B,C]})}, \] that is, $- \otimes B$ is left adjoint to $[B,-]$.
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
  cliques~\citep{joyal1991geometry}, explained in \pref{sec:cliques}),
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
by the type \texttt{exists c.\ T c c} \citep{kmett2008kan}---or
rather, by an isomorphic encoding such as
\begin{spec}
data Coend t where
  Coend :: t c c -> Coend t
\end{spec}
since \texttt{exists} is not actually valid Haskell syntax. $T$ is required to be a functor from $\C^\op
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
  each natural number, as illustrated in~\pref{fig:groupoid-P}.  In
  particular, this means that any functor $F : \P \to \C$ is
  equivalent to a collection of functors $\prod_{n \geq 0} \S_n \to
  \C$, one for each natural number.  Each functor $\S_n \to \C$ is
  entirely independent of the others, since there are no morphisms
  between different $\S_n$ to introduce constraints.
\end{rem}

\begin{figure}
  \centering
  \begin{diagram}[width=400]
import Data.List (permutations)
import Diagrams.TwoD.Path.Metafont
import Control.Lens ((^.))
import SpeciesDiagrams

-- map a vertical line from 0 to h to a trail.
along :: Double -> Located (Trail R2) -> Deformation R2
along h tr = Deformation $ \p ->
  let t       = ((p ^. _y) / h)
      trailPt = tr `atParam` t
      normal  = tr `normalAtParam` t
  in  trailPt .+^ ((p ^. _x) *^ normal)

track :: Located (Trail R2)
track = ((vrule 2 # reverseTrail <> arc (0 @@@@ turn) (1/2 @@@@ turn) # reverseTrail <> vrule 2) `at` origin)
      # scaleX 0.8

drawPerm ht off = mconcat . zipWith drawStrand [0..]
  where
    xPos :: Integer -> Double
    xPos = (off*) . fromIntegral
    drawStrand :: Integer -> Integer -> Path R2
    drawStrand i j = metafont $
      (xPos i ^& 0)
        .- leaving unitY <> arriving unitY -.
      (xPos i ^& (ht * 2 / 5))
        .--.
      (xPos j ^& (ht * 3 / 5))
        .- leaving unitY <> arriving unitY -.
      endpt (xPos j ^& ht)

styles = zipWith (\c sty -> sty . lc c) colors [lwO 0.5, lwO 1, dashingL [0.3, 0.1] 0]

strokePerm :: Path R2 -> Diagram B R2
strokePerm = mconcat . zipWith (\sty t -> strokeLocTrail t # sty) styles . pathTrails

dot = circle 0.5

flower 0 = dot # dashingG [0.1,0.1] 0
flower n = permutations [0 .. n-1]
  # map (drawPerm 5 0.3)
  # map centerX
  # map (deform' 0.001 (along 5 track))
  # map centerXY
  # map strokePerm
  # map (translateY (flowerRadius n))
  # zipWith rotateBy [0, 1/factorial n ..]
  # mconcat
  # atop
    ( hcat' (with & sep .~ 0.2)
        (zipWith fc colors (replicate (fromIntegral n) dot # lw none))
      # centerXY
    )
  # frame 1

flowerRadius 1 = 3
flowerRadius 2 = 3
flowerRadius 3 = 4
flowerRadius 4 = 10

ellipsis = hcat' (with & sep .~ 0.6) (replicate 3 (circle 0.1 # fc black))

factorial :: Integer -> Double
factorial n = fromIntegral $ product [1 .. n]

dia = hcat' (with & sep .~ 2) (map flower [0..3] ++ [ellipsis]) # frame 0.5 # lwO 0.7
  \end{diagram}
  \caption{The groupoid $\P$}
  \label{fig:groupoid-P}
\end{figure}

There is a close relationship between $\B$ and $\P$.  In the presence
of the axiom of choice, they are equivalent; intuitively, $\P$ is what
we get by noting that any two sets of the same size are isomorphic, so
we ``might as well'' just forget about the elements of finite sets and
work directly with their sizes.  However, if the axiom of choice is
rejected, the details become much more subtle; this is addressed
in~\pref{sec:finiteness-sets}.

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

