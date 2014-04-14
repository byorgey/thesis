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

\bay{Note a category is complete iff it has pullbacks and products.
  $\Type$ clearly has products.  It also has pullbacks: given $A
  \stackrel{f}{\longrightarrow} C \stackrel{g}{\longleftarrow} B$, we
  can define $A \times_C B = (a : A) \times (b : B) \times (g\ a = f\ b)$.}

Equivalence of categories.

Enriched categories.

\subsection{Groupoids}
\label{sec:groupoids}

A \term{groupoid} is a category in which all morphisms are invertible,
that is, for each morphism $f$ there is another morphism $f^{-1}$ for
which $f \comp f^{-1} = id$ and $f^{-1} \comp f = id$.  Groupoids play
a prominent role in \todo{finish; cite groupoids and stuff; HoTT; etc.}

Examples of groupoids include:

\begin{itemize}
\item $\B$ is the groupoid whose objects are finite sets and whose
  morphisms are \emph{bijections} between finite sets. \todo{intuition,
    picture}

\item Any type $T$ gives rise to a groupoid $\tygrpd{T}$ where the objects
are values $a : T$, and $\tygrpd{T}(a,b) \defeq a = b$, that is,
morphisms from $a$ to $b$ are paths $p : a = b$.
\end{itemize}

\subsection{Finiteness}
\label{sec:finiteness}

Recall that $\B$ denotes the groupoid of finite sets and bijections.
We define its constructive
counterpart $\BT$ in two stages. First, we introduce $\P$, the
skeleton of $\B$, which corresponds to working directly with the
\emph{sizes} of finite sets, and define its constructive analogue $\PT$. This
simpler context brings many of the issues surrounding constructive
finiteness into focus.  We then show how to extend $\PT$ to $\BT$.

Denote by $\P$ the category whose objects are natural numbers and
whose morphisms $\mor m n$ are bijections $\fin m \bij \fin n$ (hence
there are no morphisms unless $m \equiv n$).  Defining a counterpart
to $\P$ is straightforward:
\begin{defn}
  $\PT$ is the groupoid where (1) the objects are values of type $\N$,
  and (2) the morphisms $\mor m n$ are equivalences of type $\Fin m \iso
    \Fin n$.
\end{defn}

\todo{There is something funny going on here with groupoids
  vs. $\infty$-groupoids.  Should figure out how much of a difference
  this makes.  At the very least we should mention that we are aware
  of the issues.}

Often it is noted as trivial that $\P$ is equivalent to $\B$ and hence
that working with $\P$ rather than $\B$ when convenient is
justified. Constructively, this equivalence is not so trivial: in
particular, showing that $\P$ and $\B$ are (strongly) equivalent
requires the axiom of choice.  In more detail, it is easy to define a
functor $\fin - : \P \to \B$ which sends $n$ to $\fin n$ and preserves
morphisms; defining an inverse functor $\size - : \B \to \P$ is more
problematic. We can send each set $S$ to its size $\size S$, but we
must send a bijection $S \bij T$ to a bijection $\fin{\size S} \bij
\fin{\size T}$, and we have no way to pick one: we would need to
decide on a way to match up the elements of each set $S$ with the set
of natural numbers $\fin{\size S}$.  It does not actually matter what
choice we make, since the results will be isomorphic in any case.
This is precisely where the axiom of choice comes in: we may use it to
arbitrarily choose bijections between each set $S$ and the
corresponding set of natural numbers $\fin{\size S}$.

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

Constructing a counterpart to $\B$, then, is more subtle: we wish to
construct something equivalent to $\PT$, but without the use of $\AC$.
Furthermore, it is not \latin{a priori} clear what it should mean,
constructively, for a type to be finite.  There are, indeed, several
possible answers to this question \cite{finite}. Taking our cue from
the discussion above, we note that what was missing in trying to
define $\size- : \B \to \P$ was a choice of bijections $S \bij
\fin{\size S}$: such bijections can be thought of as evidence of the
finiteness of $S$.  This is the most straightforward definition of
constructive finiteness, and the one we adopt here.  More formally, a
finite type is one with some natural number size $n$, and an
equivalence between the type and $\Fin n$. That is, finite types are
inhabitants of $\FinType$, where
\[ \FinType \defeq (A : \Type) \times (n : \N) \times (\Fin n \iso
A). \]

We need to build a groupoid having such finite types as objects, and
equivalences between them as morphisms.  Via univalence, we may
conveniently package up such equivalences as paths.
Unfortunately, the standard method to build an
$\infty$-groupoid out of any
type does not work! Consider:
\begin{defn}
  For a type $A$, the $\infty$-groupoid $\tygrpd{A}$ has
  values $a : A$ as its objects, paths $a = b$ as its $1$-morphisms,
  paths between paths as $2$-morphims, and so on.
\end{defn}

$\tygrpd{\FinType}$ does not work as a constructive counterpart to
$\B$, because it has only one morphism between each pair of objects.
Intuitively, the problem is that the paths involve not just the types
in question but also the evidence of their finiteness, so that a path
between two finite types requires them to be finite ``in the same
way''.

The situation can be pictured as shown in \pref{fig:fin-equiv}. The elements
of types $A_1$ and $A_2$ are shown on the sides; the evidence of their
finiteness is represented by bijections between their elements and the
elements of $\Fin n$, shown along the bottom.  The catch is that the diagram
necessarily contains only triangles: corresponding elements of $A_1$ and $A_2$
must correspond to the same element of $\Fin n$ on the bottom row.  Therefore,
there are only two degrees of freedom: once the evidence of finiteness is
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

As having paths between evidence of finiteness imposes too strong a
constraint, we next try using the \emph{propositional truncation} of
finiteness evidence.  That is, we consider $\tygrpd{\FinTypeT}$,
where \[ \FinTypeT \defeq (A : \Type) \times (n : \N) \times
\ptrunc{\Fin n \iso A}. \] A path between two inhabitants of
$\FinTypeT$ is now unconstrained by the finiteness evidence (there is
always a path between any two inhabitants of a propositional
truncation), and hence equivalent to a path between their underlying
types.  This does yield the right groupoid structure. However, we now
have a different problem: we can only prove that $\tygrpd{\FinTypeT}$
is equivalent to $\PT$ if we treat equivalence of categories as a mere
proposition. The reason is that the recursion principle for
propositional truncation only allows making use of the contained
finiteness evidence if it is in the service of constructing an
inhabitant of a mere proposition.  This ensures that the precise
content of the truncation cannot ``leak''.  However, since our goal is
to construct computationally relevant functors witnessing the
equivalence, equivalence as a mere proposition is unsatisfactory.

Instead, we define $\BT$ as follows:

\begin{defn}
Define the $\infty$-groupoid $\BT$ where
\begin{itemize}
\item the objects are values of type $\FinType \defeq (A : \Type) \times (n : \N)
\times (\Fin n \iso A)$,
\item $1$-morphisms $\mor{(A,m,i)}{(B,n,j)}$ are paths $A = B$, and
\item higher morphisms are paths between paths, and so on.
\end{itemize}
\end{defn}

That is, we do not hide finiteness evidence in a propositional
truncation, but morphisms simply ignore the finiteness evidence.  This
may seem strange: we go to the trouble of adding extra computational
evidence to objects, but then we turn around and say that the additional
evidence is irrelevant after all!  However, the point is that although the
extra evidence may be irrelevant to
\emph{morphisms}, functors out of the category may still make use of
it (see \pref{defn:size}).  Instead of having to make an arbitrary
choice of isomorphism when mapping out of an object, we ``blow up''
the category by making a separate object for each possible choice, but
ensure that objects which differ only by this choice are isomorphic.

\begin{rem}
  Note that given a morphism $e : \mor {(A,m,i)} {(B,n,j)}$, it is
  provably the case that $m = n$.  In particular, $i \then e \then j^{-1} :
  \Fin m \iso \Fin n$, from which we may prove $m = n$ by double
  induction.
\end{rem}

\begin{defn}
  We define a functor $\fin - : \PT \to \BT$ as follows: on objects,
  $\fin n \defeq (\Fin n, n, \id)$, and $\fin -$ is the identity on
  morphisms.
\end{defn}

\begin{defn} \label{defn:size}
In the other direction, we define $\size : \BT \to \PT$ which sends
objects $(A, m, i)$ to $m$, and sends morphisms
$e : \mor {(A, m, i)} {(B, n, j)}$ to $i \then e \then j^{-1}$:
\[
  \xymatrix{\Fin m \ar@@{<->}[d]_-i & \Fin n \\ A \ar@@{<->}[r]_e & B
    \ar@@{<->}[u]_-{j^{-1}} } \]
The functoriality of $\size{}$ can be seen by noting the cancelling
pair of inverse equivalences in each of the following two diagrams:
  \[
     \xymatrix{\Fin m \ar@@<-.4em>@@{<->}[d]_i
         \ar@@<.4em>@@{<->}[d]^{i^{-1}}
       \\
         A \ar@@(dl,dr)_{\id}
     }
     \qquad\qquad
     \xymatrix{
       \Fin m \ar@@{<->}[d]_i &
       \Fin n \ar@@<-.4em>@@{<->}[d]_j \ar@@<.4em>@@{<->}[d]^{j^{-1}} &
       \Fin o \ar@@{<->}[d]^k
     \\
       A \ar@@{<->}[r]_e &
       B \ar@@{<->}[r]_f &
       C
     }
  \]
\end{defn}

\begin{prop}
  The pair of functors $\xymatrix{\PT \ar@@<.5ex>[r]^{\fin -} & \BT
    \ar@@<.5ex>[l]^{\size{}}}$ constitutes an equivalence
  between the groupoids $\PT$ and $\BT$.

\begin{proof}
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

\subsection{Monoids}
\label{sec:monoids}

Monoids, monoidal categories.  Note we will pretend all monoidal
categories are strict (justify).  Products and coproducts. Monoidal
closed. Cartesian closed.

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
