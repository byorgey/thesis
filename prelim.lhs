%% -*- mode: LaTeX; compile-command: "mk" -*-

%include polycode.fmt

\chapter{Preliminaries}
\label{chap:prelim}

\todo{Describe some big ideas here.  Give some instruction for how to
  use this chapter.}

\todo{Give some backward references from the rest of the text to
  relevant descriptions here.}

\section{Basic notations}
\label{sec:basic}

\todo{$\fin n = \{0, \dots, n-1\}$.}

\todo{Image of a set under a function or bijection.  Function restriction.}

\todo{Typography.}

\section{Homotopy type theory}
\label{sec:HoTT}

\todo{Probably need to re-expand this section.}

We work with a type theory equipped with an empty type \TyZero, a unit
type \TyOne (with inhabitant $\unit$), coproducts $A + B$ (with
constructors $\inl$ and $\inr$), dependent pairs $(x:A) \times B(x)$,
dependent functions $(x:A) \to B(x)$, a hierarchy of type universes
$\Type_0$, $\Type_1$, $\Type_2$\dots (we usually omit the subscript
from $\Type_0$), judgmental equality $A \equiv B$, and propositional
equality $A = B$.  The theory also allows inductive definitions.  We
use $\N : \Type_0$ to denote the type of natural numbers, and $\Fin :
\N \to \Type_0$ the usual indexed type of canonical finite sets.

Although we use Agda's notation~\cite{Agda} for dependent pairs and
functions, we occasionally use the traditional $\sum_{x : A} B(x)$ and
$\prod_{x:A} B(x)$ for emphasis, and the
abbreviations $A \times B$ and $A \to B$ for non-dependent pair and
function types.
\todo{implicit quantification?}
% Also,
% to reduce clutter, we sometimes make use of implicit quantification:
% free type variables in a type---like $A$ and $B$ in $A \times (B \to
% \N)$---are implicitly universally quantified, like $(A : \Type) \to (B
% : \Type) \to A \times (B \to \N)$.

The type of \term{equivalences} between $A$ and $B$, written $A \iso
B$, is definable in HoTT; intuitively, an equivalence is a pair of
inverse functions $f : A \to B$ and $g : B \to A$.\footnote{The
  precise details are more subtle \cite[chap.  4]{hottbook}, but
  unimportant for our purposes.}  We overload the notations $\id$ and
$\comp$ to denote the identity equivalence and equivalence composition
respectively; we also allow equivalences of type $A \iso B$ to be
implicitly used as functions $A \to B$ where it does not cause
confusion.  We use the notation $\mkIso$ for constructing equivalences
from a pair of functions. That is, if $f : A \to B$ and $g : B \to A$
are inverse, then $f \mkIso g : A \iso B$; the proof that $f$ and $g$
are inverse is left implicit. \todo{is this $\mkIso$ needed?}

The structure of HoTT guarantees that functions are always functorial with
respect to equality. That is, if $e : x = y$ is a witness of equality between
$x$ and $y$ (informally, a ``path'' between $x$ and $y$), and $f$ is a
function of an appropriate type, then $f(x) = f(y)$.  Given $e$ we also have
$P(x) \to P(y)$ for any type family $P$, called the \term{transport} of $P(x)$
along $e$ and denoted $\transport{P}{e}$, or simply $e_*$ when $P$ is clear
from context.

HoTT includes the \emph{univalence axiom} which states that an
equivalence $A \iso B$ can be converted to the propositional equality
$A = B$ (and vice versa).  This axiom formally encodes
the mathematical practice of treating isomorphic things as
identical.  In other words, $A = B$ does not mean that $A$ and $B$ are
identical, but that they can be used interchangeably---and moreover,
interchanging them may require some work, computationally speaking.
Thus an equality $e : A = B$ can have nontrivial computational
content.

As of yet, univalence has no direct computational interpretation, so
using it to give a computational interpretation of species may seem
suspect. Note, however, that \mbox{$\transport{X \mapsto X}{\ua(f)} =
  f$}, where $\ua : (A \iso B) \to (A = B)$ denotes (one direction of)
the univalence axiom. So univalence introduces no computational
problems as long as applications of $\ua$ are only ultimately used via
$\mathsf{transport}$.  Univalence allows a convenient shorthand:
packaging up an equivalence into a path and then transporting along
that path results in ``automatically'' inserting the equivalence and
its inverse in all the necessary places throughout the term.

\todo{Mere propositions, sets. Truncation. Recursion principle for
  truncation, intuition. }  The propositional truncation of a type
``squashes'' the type down to a mere proposition, by adding a path
between every pair of inhabitants. Intuitively, this can be thought of
as ``forgetting'' all information contained in the inhabitants other
than their existence, though the reality is more subtle.

\section{Category theory}
\label{sec:category-theory}

Make extensive use of category theory.  Very quick overview of basics
(categories, functors, natural transformations, functor categories,
adjunctions).  Basic categories which will be used often: $\Set$,
$\N$, \Type.

Use $\forall$ notation for natural transformations. \todo{Make it so.}

Bifunctors.

  \todo{Action of functor on morphisms follows from action
  on objects.  Always true when expression giving action on objects is
  composed of functors from groupoids; then functoriality comes for
  free too.  Later, can make connection to homotopy type theory.}

Functor categories.  The notations $[\C,\D]$ and $\D^\C$ for a functor
category will be used interchangeably, as convenient.  The notation
$\D^\C$ is often helpful since intuition for exponents carries over to
functor categories.  For example, \todo{finish}

\bay{Note a category is complete iff it has pullbacks and products.
  $\Type$ clearly has products.  It also has pullbacks: given $A
  \stackrel{f}{\longrightarrow} C \stackrel{g}{\longleftarrow} B$, we
  can define $A \times_C B = (a : A) \times (b : B) \times (g\ a = f\ b)$.}

Equivalence of categories.

Enriched categories.

\subsection{Monoids}
\label{sec:monoids}

Monoids, monoidal categories.  Note we will pretend all monoidal
categories are strict (justify).  Products and coproducts. Monoidal
closed. Cartesian closed.

\bay{How can we say that we are using ``the same'' ``product-like''
  monoidal structure in all these different categories?  Are they
  related by monoidal functors?}

\subsection{Ends, coends, and parametricity}
\label{sec:parametricity}

\todo{Define/give intuition for ends and coends.  (Co)ends as
(co)equializers.  Talk about connection between natural
transformations and polymorphic functions, specific ways it plays out
in a dependent type theory---e.g. can we assume parametricity for
functions that abstract over things classified by |*|? Cite Bernardy
et al.}

\subsection{Coends}
\label{sec:coends}

Given a bifunctor $T : \C^\op \times \C \to \D$, a \term{coend} over
$T$, denoted $\int^C T(C,C)$, is an object of $\D$ together with some
(di)naturality conditions.  In the specific case when the objects of
$\D$ can be thought of as sets or types with
``elements''\footnote{This definition can be made precise in full
  generality (without requiring the objects of $\D$ to have
  ``elements'') using a \emph{coequalizer}.}, the coend $\int^C
T(C,C)$ is given by a quotient of an indexed coproduct $\left( \sum_{C
    \in \C} T(C,C) \right) / \sim$.  Elements of the indexed coproduct
look like pairs $(C, t)$ where $C \in \C$ and $t \in T(C,C)$. The idea
behind the quotient is that we want to consider two pairs $(C,t)$ and
$(C', t')$ equivalent if they are related by the functoriality of $T$.
In particular, for each arrow $f : C \to C'$ in $\C$ and each $x \in
T(C',C)$, we set $(C, T(f,1)\ x) \sim (C', T(1,f)\ x)$.  That is, we
can always ``swap out $(C,t)$ for $(C',t')$'' as long as we have some
way to map from $C$ to $C'$ and the associated values $t$ and $t'$ are
related by the same mapping.

Intuitively, the functor $T$ can be thought of as an ``interface'';
$(C,t)$ is then a ``module'' with ``representation type'' $C$ and
``implementation'' $t$.  Indeed, in Haskell, the coend of $T$ is given
by the type \texttt{exists c.\ T c c} (or rather, by an isomorphic
encoding, since \texttt{exists} is not actually valid Haskell snytax)
\cite{kmett2008kan}. $T$ is required to be a bifunctor from $\C^\op
\times \C$ since the representation type may occur both co- and
contravariantly in the interface.

\todo{Expand.  Give formal definition in terms of coequalizer.}

\begin{rem}
  Note that $\int^{L_1, L_2} \dots$ is used as an abbrevation for a
  coend over the product category $\Lab \times \Lab$.
\end{rem}

\subsection{Groupoids}
\label{sec:groupoids}

A \term{groupoid} is a category in which all morphisms are invertible,
that is, for each morphism $f$ there is another morphism $f^{-1}$ for
which $f \comp f^{-1} = id$ and $f^{-1} \comp f = id$.  Groupoids play
a prominent role in \todo{finish; cite groupoids and stuff; HoTT; etc.}

Some examples:

\begin{defn}
Any type $T$ gives rise to a groupoid $\tygrpd{T}$ where the objects
are values $a : T$, and $\tygrpd{T}(a,b) \defeq a = b$, that is,
morphisms from $a$ to $b$ are paths $p : a = b$.
\end{defn}

\begin{defn}
  Any category $\C$ gives rise to a groupoid $\C^*$, called the
  \term{core} of $\C$, whose objects are the objects of $\C$ and whose
  morphisms are the isomorphisms in $\C$.
\end{defn}

Checking that $\C^*$ is indeed a groupoid is left as an easy exercise.

\begin{defn}
  We give the name $\B$ to $\FinSet^*$, that is, the groupoid whose
  objects are finite sets and whose morphisms are \emph{bijections}
  between finite sets. \todo{intuition, picture}
\end{defn}

\todo{Notation for permutations: $\perm{A}$}
\todo{Define ``transitive''} \bay{Why is this todo here?}

$\B$ does not have products or coproducts. To see that $\B$ does not
have coproducts, let $A, B \in \B$ be arbitrary finite sets, and
suppose they have some coproduct $A+B$. By definition this comes with
a diagram $\xymatrix{A \ar[r]^-{\iota_1} & A+B & B \ar[l]_-{\iota_2}}$
in $\B$. Since morphisms in $\B$ are bijections, this would imply that
$A$ and $B$ are in bijection, but since $A$ and $B$ were arbitrary
finite sets, this is absurd.  A similar argument applies in the case
of products.  More generally, any category with all products or coproducts
is necessarily \term{connected}, \ie has some zig-zag sequence of
arrows connecting any two objects, and this is clearly not true of
$\B$.

$\B$ does, however, have monoidal structures given by Cartesian
product and disjoint union of finite sets, even though these are not a
categorical product or coproduct. \todo{More intuition/illustration here.}
In fact, something more general is true:

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
  result must be an isomorphism---hence a morphism in $\C^*$---since
  all functors (here, $U$ and $\otimes$ in particular) preserve
  isomorphisms.

  The fact that $1$ is an identity for $\otimes^*$, associativity, and
  the coherence conditions all follow readily from the definitions.
\end{proof}

\section{The Axiom of Choice (and how to avoid it)}
\label{sec:AC}

The (in)famous \emph{Axiom of Choice} (hereafter, AC) can be
formulated in a number of equivalent ways.  Perhaps the most
well-known is
\begin{equation}
  \label{eq:ac1} \tag{AC}
  \text{The Cartesian product of any collection of non-empty sets is non-empty.}
\end{equation}
Given a family of sets $\{X_i \mid i \in I\}$, an element of their
Cartesian product is some $I$-indexed tuple $\{x_i \mid i \in I\}$
where $x_i \in X_i$ for each $i$. Such a tuple can be thought of as a
function (called a \emph{choice function}) which picks out some
particular $x_i$ from each $X_i$. \todo{finish.}

\todo{Moved here, need to edit.}
Several variants of the axiom of choice can be expressed within
homotopy type theory.  A ``na\"ive'' variant, referred to as
$\AC_\infty$, is given by
\begin{equation} \tag{$\AC_\infty$}
  \label{eq:ac-infty}
  \left( \prod_{x : X} \sum_{(a : A(x))} P(x,a) \right) \iso \left(
    \sum_{(g : \prod_{x:X} A(x))} \prod_{(x:X)} P(x,g(x)) \right).
\end{equation}
This variant is actually \emph{provable} within the theory; however,
it is of little use here, since rather than just requiring a family of
``nonempty'' sets, it actually requires, for each $x$, an explicit
\emph{witness} $a : A(x)$ for which the property $P(x,a)$ holds.  That
is, it requires that we have already made a choice for each $x$.

A variant which corresponds more closely to standard mathematical
practice, referred to as $\AC_{-1}$ or simply $\AC$, is
\begin{equation} \tag{$\AC$}
  \label{eq:AC}
  \left( \prod_{x : X} \ptrunc{\sum_{(a : A(x))} P(x,a)} \right) \to
    \ptrunc{\sum_{(g : \prod_{x:X} A(x))} \prod_{(x:X)} P(x,g(x))}.
\end{equation}
Intuitively, this says that given a family of \emph{nonempty}---\ie
merely inhabited---sets, there merely exists a choice function.
Although $\AC$ is not provable within the theory, it is consistent to
assume it as an axiom.  However, as an axiom, it has no computational
interpretation, and is therefore unsuitable for constructing a functor
with computational content.  Moreover, even if it did have a computational
interpretation, it would also be of limited use, since
\todo{propositional truncation would get in the way.}

The problem with the axiom of choice is that it is non-constructive,
in the sense that a choice function produced by AC has no real
computational content.  AC simply postulates the \emph{existence} of a
choice function but does not actually specify its behavior.  In the
setting of this work, therefore, AC must be rejected. \bay{Expound on
  this a bit?  Why must it be rejected?  Maybe somewhere else I ought
  to clearly lay out and motivate the constructivist viewpoint
  underlying this work.}

\subsection{Unique isomorphism and generalized ``the''}
\label{sec:generalized-the}

In category theory, one is typically interested in specifying objects
only \emph{up to unique isomorphism}.  In fact, definitions which make
use of actual \emph{equality} on objects are sometimes referred to
(half-jokingly) as \emph{evil}.  More positively, the widely
subscribed-to \term{principle of
  equivalence}~\cite{principle-of-equivalence} states that properties
of mathematical structures should be invariant under equivalence.
This principle leads naturally to speaking of ``the'' object having
some property, when in fact there may be many objects with the given
property, but are all uniquely isomorphic; this cannot cause
confusion if the principle of equivalence is in effect.

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

The right way around this use of AC is to generalize functors to
\term{anafunctors}, which are presented below.  The theory of
\term{cliques} is presented first---cliques come close to being a way
around AC, and although they don't completely surmount the problem in
the end, they offer some good intuition for understanding anafunctors.

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
  \item $u_{ii} = id_{A_i}$, and
  \item $u_{ij} \then u_{jk} = u_{ik}$.
  \end{itemize}
\end{defn}

\begin{rem}
  Note that the last two conditions together imply $u_{ij} =
  u_{ji}^{-1}$, since $u_{ij} \then u_{ji} = u_{ii} = id$.
\end{rem}

A clique can thus be visualized as an actual clique in a directed
graph, with a unique morphism between any two objects. \todo{picture}
Note that this is actually a \emph{commuting} diagram!

Thus, a clique represents a collection of objects in $\C$ which are
all isomorphic, with a single chosen isomorphism between any two.
Note that $\C$ may in fact contain \emph{other} isomorphisms between
two objects in a clique. \todo{More intuition for why this is OK}

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
to $C_k$, \todo{picture}.  If we pick some particular $B_j$, we can
define $h_{ik} = f_{ij} \then g_{jk}$; and it's not hard to show that
the result will be the same no matter which $B_j$ we pick, since
everything in sight commutes.  But which $B_j$ should we pick?  In
fact, we have to use the axiom of choice!  Again, this use of AC is
``benign'', but it is a use nonetheless.

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
would likely end up defining a new notion of ``clique functor'' $F :
\C \stackrel{\clq{}}{\to} \D$ given by a regular functor $\C \to \clq
\D$, and showing that these clique functors ``act like'' functors (\ie
can be composed, have a suitable notion of natural transformations,
\etc).

In fact, this idea of generalizing functors is the right one, but
instead of generalizing them to ``clique functors'' we generalize
instead to \term{anafunctors}.

\subsection{Anafunctors}
\label{sec:anafunctors}

The basic idea of an anafunctor is similar to that of a functor $\C
\to \clq \D$---it represents a functor whose ``values are specified
only up to unique isomorphsim''.  In fact, anafunctors $\C \to \D$ and
functors $\C \to \clq \D$ are \todo{equivalent? with AC? check
  this\dots}, though this is far from apparent, and anafunctors are
nicer to work with.  Every functor is trivially an anafunctor, and in
the presence of AC, anafunctors ``collapse'' to regular functors.
Moreover, anafunctors possess many of the same properties as functors
\todo{like what?}

The key idea is to add a class of ``specifications'' which mediate the
relationship between objects in the source and target categories, in
exactly the same way that a ``junction table'' must be added to
support a many-to-many relationship in a database schema.

\begin{defn}
  An \term{anafunctor} $F : \C \to \D$ is defined as follows.
  \begin{itemize}
  \item There is a class $||F||$ of \term{specifications}.
  \item There are two functions $\xymatrix{\Ob \C & ||F|| \ar[l]_{\sigma}
      \ar[r]^{\tau} & \Ob \D}$ mapping specifications to objects of
    $\C$ and $\D$.
  \end{itemize}
  $||F||$, $\sigma$, and $\tau$ together define a many-to-many
  relationship between objects of $\C$ and objects of $\D$.  Any
  normal functor may map multiple objects of $\C$ to the same object
  in $\D$; the novel aspect is the ability to have a single object of
  $\C$ correspond to multiple objects of $\D$.

  $D \in \D$ is called a \term{specified value of $F$ at $C$} if there
  is some specification $s \in ||F||$ such that $\sigma(s) = C$ and
  $\tau(s) = D$, in which case we write $F_s(C) = D$.  Moreover, $D$
  is \term{a value of $F$ at $C$} (not necessarily a \emph{specified}
  one) if there is some $s$ for which $D \cong F_s(C)$.

  The name of the game now is to impose additional conditions which
  ensure that $F$ ``acts like'' a regular functor $\C \to \D$.
  \begin{itemize}
  \item Functors are defined on all objects; so we require each object
    of $\C$ to have at least one specification $s$ which corresponds
    to it---that is, $\sigma$ must be surjective.
  \item Functors transport morphisms as well as objects.  For each
    $s,t \in ||F||$ and each $f : \sigma(s) \to \sigma(t)$ in $\C$,
    there must be a morphism $F_{s,t}(f) : F_s(\sigma(s)) \to
    F_t(\sigma(t))$ in $\D$. \todo{picture}
  \item Functors preserve identities: for each $s \in ||F||$ we should
    have $F_{s,s}(id_{\sigma(s)}) = id_{\tau(s)}$. \todo{picture}
  \item Finally, functors preserve composition: for all $s,t,u \in
    ||F||$, $f : \sigma(s) \to \sigma(t)$, and $g : \sigma(t) \to
    \sigma(u)$, it must be the case that $F_{s,u}(f \then g) =
    F_{s,t}(f) \then F_{t,u}(g)$. \todo{picture}
  \end{itemize}
\end{defn}

Note that if $s,t \in ||F||$ with $\sigma(s) = \sigma(t) = C$, then
$F_{s,t}(id_C) \then F_{t,s}(id_C) = F_{s,s}(id_C) = id_{\tau(s)}$, so
each object of $\C$ really does map to an equivalence class of
isomorphic objects in $\D$.

There is an alternative, equivalent definition of anafunctors, which
is somewhat less intuitive but sometimes more convenient to work with.

\begin{defn}
  An anafunctor $F : \C \to \D$ is a category $||F||$ together with a
  span of \emph{functors} $\xymatrix{\C & ||F|| \ar[l]_\sigma
    \ar[r]^\tau & \D}$, such that $\sigma$ is faithful, and surjective
  on both objects and morphisms.
\end{defn}

We are punning on notation a bit here: in the original definition of
anafunctor, $||F||$ is a set and $\sigma$ and $\tau$ are functions on
objects, whereas in this more abstract definition $||F||$ is a
category and $\sigma$ and $\tau$ are functors.  Of course, the two are
closely related: given a span of functors $\xymatrix{\C & \overline F
  \ar[l]_{\overline \sigma} \ar[r]^{\overline \tau} & \D}$, we may
simply take the objects of $\overline F$ as the class of
specifications $||F||$, and the actions of the functors $\overline
\sigma$ and $\overline \tau$ on objects as the functions $\sigma$ and
$\tau$.  Conversely, given a class of specifications $||F||$ and
functions $\sigma$ and $\tau$, we may construct the category
$\overline F$ with $\Ob \overline F = ||F||$ and with morphisms
$\sigma(s) \to \sigma(t)$ in $\C$ acting as morphisms $s \to t$ in
$\overline F$.  We take $\overline \sigma$ to be $\sigma$ on objects
and the identity on morphisms, and $\overline \tau$ maps $f : s \to t$
in $\overline F$ to $F_{s,t}(f) : \tau(s) \to \tau(t)$ in $\D$.

Every functor $F : \C \to \D$ can be trivially turned into an
anafunctor: we take $\overline F = \Ob \C$, $\sigma$ the
identity functor, and $\tau = F$.

Anafunctors compose: given anafunctors $F_1 : \C \to \D$ and $F_2 : \D
\to \E$, the key idea is to take a suitable \emph{product} of their
specifications.  In particular, \todo{finish.  Reference Makkai.}
This is actually easier to see using the abstract definition in terms
of spans: \[ \xymatrix{ {} \ar[d] \ar[r] \pullback & ||F_2||
  \ar[d]_{\sigma_2} \ar[r]^{\tau_2} & \E \\ ||F_1|| \ar[d]_{\sigma_1}
  \ar[r]^{\tau_1} & \D & \\ \C & & } \] $\Cat$ is cocomplete, and in
particular has pullbacks, so we may construct a new anafunctor from
$\C$ to $\E$ by taking a pullback of $\tau_1$ and $\sigma_2$ and then
composing appropriately, as illustrated in the diagram.

\todo{State a few other ways in which anafunctors ``act like''
  functors; handwave at general theorem stating something about their
  equivalence.} \todo{Do we need to discuss saturated anafunctors?
  Maybe that only comes up in working out the precise details of
  equivalence between functors and anafunctors?}

We are therefore justified in ``mixing and matching'' functors and
anafunctors as convenient, but discussing them all as if they were
regular functors (except when defining a particular anafunctor).  Such
usage can be formalized by turning everything into an anafunctor, and
translating functor operations and properties into corresponding
operations and properties of anafunctors.

\todo{Implementation of anafunctors in type theory: can model set of
  specifications $||F||$ together with mapping $\sigma$ as an indexed
  type $||F|| : \Ob \C \to \U$.  In what situations do we get
  functoriality for free?}

\subsection{Finiteness}
\label{sec:finiteness}

Recall that $\B$ denotes the groupoid of finite sets and bijections,
and $\P$ the groupoid of natural numbers and permutations.  We begin
by discussing the relationship between $\B$ and $\P$, which is more
interesting than it may first seem.

$\P$ is a \term{skeleton} of $\B$---roughly, we may think of it as the
result of replacing each equivalence class of isomorphic objects in
$\B$ with a single object.  In this case, we can identify each
equivalence class of isomorphic finite sets with a \emph{size}, the
only property of sets which is invariant under isomorphism.

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
in type theory.  A type-theoretic counterpart fo $\P$ is relatively
straightforward.

\begin{defn}
  $\PT$ is the groupoid where
  \begin{itemize}
  \item the objects are values of type $\N$, and
  \item the morphisms $\mor m n$ are equivalences of type $\Fin m \iso
    \Fin n$.
  \end{itemize}
\end{defn}

\todo{There is something funny going on here with groupoids
  vs. $\infty$-groupoids.  Should figure out how much of a difference
  this makes.  At the very least we should mention that we are aware
  of the issues.}

Developing a counterpart to $\B$ is more subtle.  The first order of
business is to decide how to port the concept of a ``finite set''.
Generally, ``a set with property X'' ports to type theory as ``a type
paired with constructive evidence of property X''; so what is
constructive evidence of finiteness? This is not \latin{a priori}
clear, and indeed, there are several possible answers
\citep{finite}. However, the discussion above, where bijections $S \bij
\fin{\size S}$ played a prominent role, suggests that we adopt the
simplest option, \term{cardinal-finiteness}.  A set (type) $A$ is
\term{cardinal-finite} iff there exists some $n \in \N$ and a
bijection $A \bij \fin n$; $n$ is called the size or cardinality of
$A$.  Our first try at encoding this in type theory is
\[ \FinType \defeq (A : \Type) \times (n : \N) \times (A \iso \Fin n). \]

We would like to build a groupoid having such finite types as objects,
and equivalences between them as morphisms.  Via univalence, we may
conveniently package up such equivalences as paths.  Unfortunately,
the standard method to build an $\infty$-groupoid out of any type does
not work! Recall that given some type $A$, the $\infty$-groupoid
$\tygrpd{A}$ has values $(a : A)$ as its objects, paths $a = b$ as its
$1$-morphisms, paths between paths as $2$-morphims, and so on.
$\tygrpd{\FinType}$ does not work as a constructive counterpart to
$\B$, because it has only one morphism between each pair of objects
($\B$, of course, has $n!$ morphisms between any two sets of size
$n$).  Intuitively, the problem is that paths between objects in
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
  There is at most one morphism between any two objects of
  $\tygrpd{\FinType}$.  That is, for any $X, Y : \FinType$,
  if $p_1, p_2 : X = Y$ then $p_1 = p_2$.  (Using the terminology of
  homotopy type theory, $\FinType$ is a set, \ie a $0$-type.)
\end{prop}

\begin{proof}[Proof (sketch).]
  A path $(A_1, n_1, e_1) = (A_2, n_2, e_2)$ is equivalent to $(p :
  A_1 = A_2) \times (q : n_1 = n_2) \times (q_*(p_*(e_1)) = e_2)$.
  Noting that $p_*(e_1)$, in particular, is given by the composition
  of $p$ with $e_1$, and \todo{finish}
\end{proof}

The underlying problem is that $\FinType$ does not actually do a very
good job at encoding what classical mathematicians usually mean by
``finite set''.  Saying that a set $A$ is finite with size $n$ does
not typically imply there is some specific, chosen bijection $A \bij
\fin n$, but merely that $A$ \emph{can be put} in bijection with $\fin
n$, with no mention of a specific bijection.  This is justified by the
fact that, up to isomorphism, any bijection $A \bij \fin n$ is just as
good as any other.

This suggests a better encoding of finiteness in type theory, given
by \[ \FinTypeT \defeq (A : \Type) \times (n : \N) \times \ptrunc{A
  \iso \Fin n}, \] making use of propositional truncation to encode
the fact that there \emph{merely exists} an equivalence between $A$
and $\Fin n$, but without exposing a precise choice.  This does give
us the expected groupoid structure: since there is a path between any
two elements of a truncated type, a path between two inhabitants
$(S,m,\psi_S), (T,n,\psi_T)$ of $\FinTypeT$ is equivalent to a pair of
paths $(S = T) \times (m = n)$.

\begin{defn}
  $\BT$ is defined by \[ \BT \defeq \tygrpd{\FinTypeT}, \] the
  $\infty$-groupoid of cardinal-finite types and paths bewteen them.
\end{defn}

Just as with $\B$ and $\P$, we cannot directly define a functor $\size
- : \BT \to \PT$, since defining its action on morphisms would require
a specific choice of equivalence $A \iso \Fin n$, and the objects of
$\BT$ merely guarantee that such equivalences exist, without giving
access to any particular such equivalence.  Instead, we can define an
anafunctor $\size - : \BT \to \PT$, similarly to $\size - : \B \to
\P$\footnote{We overload $\size{}$ to serve as the name of both
  anafunctors (as well as set cardinality); this should not cause
  confusion as they are never used in similar contexts.}.

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

We can also define a functor from $\PT$ to $\BT$; together, these define
an anaequivalence between $\PT$ and $\BT$.

\begin{defn}
  We define a functor $\fin - : \PT \to \BT$ as follows: on objects,
  $\fin n \defeq (\Fin n, n, \id)$, and $\fin -$ is the identity on
  morphisms.
\end{defn}

\begin{prop}
  The pair of (ana)functors $\xymatrix{\PT \ar@@<.5ex>[r]^{\fin -} & \BT
    \ar@@<.5ex>[l]^{\size{}}}$ constitutes an (ana)equivalence
  between the groupoids $\PT$ and $\BT$.

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
  We must exhibit a natural isomorphism $\alpha : \nt{Id}{\fin{\size
      -}}$.  $\alpha_{(A,m,i)}$ must be a morphism
  in $\BT$ from $(A,m,i)$ to $(\Fin m, m, \id)$, that is, an
  equivalence $A \iso \Fin m$.  Therefore we define $
  \alpha_{(A,m,i)} \defeq i^{-1}$.  Naturality of $\alpha$ is given
  by the diagram
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
