%% -*- mode: LaTeX; compile-command: "mk" -*-

%include polycode.fmt

\chapter{Preliminaries}
\label{chap:prelim}

\todo{Describe some big ideas here.  Give some instruction for how to
  use this chapter.}

\todo{Give some backward references from the rest of the text to
  relevant descriptions here.}

\section{Homotopy type theory}
\label{sec:HoTT}

\todo{put intro to HoTT here}

Basics of type theory (copy from other paper).

Equivalences.

Equality/paths.  Univalence.  Intuition: richer space of equalities.
We have Leibniz equality (transport) but transport may involve some
work.

Mere propositions, sets. Truncation. Recursion principle for
truncation, intuition.

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

\todo{better title for this section?}

Let $\fin n \defeq \{0, \dots, n-1\}$ be the set of the first $n$ natural
numbers.  Denote by $\P$ the category whose objects are natural
numbers and whose morphisms $\mor m n$ are bijections $\fin m \bij \fin
n$ (hence there are no morphisms $\mor m n$ unless $m \equiv n$).  Often it
is noted as a triviality not requiring proof that $\P$ is equivalent
to (in fact, a skeleton of) $\B$ and hence we are justified in working
with $\P$ rather than $\B$ when convenient.

However, upon digging a bit deeper it is not quite so trivial after
all: in particular, showing that $\P$ and $\B$ are (strongly)
equivalent requires the axiom of choice.  In more detail, it is easy
to define a functor $\fin - : \P \to \B$ which sends $n$ to $\fin n$
and preserves morphisms.  Defining an inverse functor $\B \to \P$ is
more problematic. Clearly we must send each set $S$ to its size $\size
S$. However, a morphism $S \bij T$ must be sent to some bijection
$\fin{\size S} \bij \fin{\size T}$, and intuitively we have no way to
pick one: we would need to decide on a way to match up the elements of
each set $S$ with the set of natural numbers $\fin{\size S}$.  In a
sense it ``does not matter'' what choice we make, since the results
will be isomorphic in any case, and this is precisely where the axiom
of choice comes in. \todo{Need to think through this a bit more
  carefully.}

\todo{Note that HoTT can express several variants on AC.  Some are
  inherently non-constructive so we do not want to assert them.  There
  is one variant which is simply provable, but in order to apply it we
  need to already have evidence of a correspondence between arbitrary
  finite sets and canonical finite sets of the same size.}

This leads us to the need for \emph{computational evidence of
  finiteness}.  (Even the phrase ``send each set $S$ to its size
$\size S$'' should have been suspect before.  Where does this size
actually come from?)

First, we define a counterpart to $\P$ in type theory:
\begin{defn}
  $\PT$ is the groupoid where
  \begin{itemize}
  \item the objects are natural numbers in our type theory, that is,
    values of type $\N$, and
  \item the morphisms $\mor m n$ are equivalences of type $\Fin m \iso
    \Fin n$.
  \end{itemize}
\end{defn}

As a first try at defining a constructive counterpart to $\B$, we
consider $\tygrpd{\FinType}$, where
\[ \FinType \defeq (A : \Type) \times (n : \N) \times (\Fin n \iso
A). \] However, this does not work: the explicit evidence of
finiteness is too strong, and collapses all the interesting groupoid
structure.

\begin{prop}
  There is at most one morphism between any two objects of
  $\tygrpd{\FinType}$.  That is, for any $X, Y : \FinType$,
  if $p_1, p_2 : X = Y$ then $p_1 = p_2$.  (Using the terminology of
  homotopy type theory, $\FinType$ is a set, \ie a $0$-type.)
\end{prop}

\todo{Give some intuition.  Use triangle picture.}

\begin{proof}
  \todo{prove me.}
\end{proof}

The next thing to try is thus $\tygrpd{\FinTypeT}$, where \[ \FinTypeT
\defeq (A : \Type) \times (n : \N) \times \ptrunc{\Fin n \iso A} \]
This does give us the right groupoid structure, and we can prove that
it is equivalent to $\PT$---as long as equivalence of categories is a
mere proposition! \todo{explain why} \todo{Aren't there any tricks we
  can pull to uniquely characterize the functor we're trying to
  construct?} Equivalence as a mere proposition is not all that
useful, however. We want to define a functor $\tygrpd{\FinTypeT} \to
\PT$ that we can actually compute with, but we cannot since it needs
the equivalences in a computationally relevant way.

In the end, we are forced to give up on constructing a groupoid via
$\tygrpd{-}$, and define $\BT$ as follows.

\begin{defn}
$\BT$ is the groupoid where
\begin{itemize}
\item the objects are values of type $\FinType \defeq (A : \Type) \times (n : \N)
\times (\Fin n \iso A)$, and
\item morphisms $\mor{(A,m,i)}{(B,n,j)}$ are equivalences $A \iso B$.
\end{itemize}
\end{defn}

That is, morphisms simply ignore the equivalences contained in
objects.

\begin{rem}
  Note that given a morphism $e : \mor {(A,m,i)} {(B,n,j)}$, it is
  provably the case that $m \equiv n$.  In particular, $i \then e \then j^{-1} :
  \Fin m \iso \Fin n$, from which we may prove $m \equiv n$ by double
  induction.
\end{rem}

\begin{rem}
  This may seem a bit funny: we go to the trouble of adding extra
  computational evidence to objects, but then the next minute we turn
  around and say that the additional evidence is irrelevant after all!
  However, the point is that although the extra evidence may be
  irrelevant to \emph{morphisms}, functors out of the category may
  still make use of it (see \pref{defn:size}).  Instead of having to
  make an arbitrary choice of isomorphism when mapping out of an
  object, we ``blow up'' the category by making a separate object for
  each possible choice, but ensure that objects which differ only by
  this choice are isomorphic.
\end{rem}

\begin{defn}
We can now define a functor $\fin - : \PT \to \BT$ in the evident way:
\begin{itemize}
\item On objects, $\fin n \defeq (\Fin n, n, \id)$.
\item $\fin -$ is the identity on morphisms.
\end{itemize}
\end{defn}

\begin{defn} \label{defn:size}
In the other direction, we define $\size{} : \BT \to \PT$:
\begin{itemize}
\item On objects, $\size{(A, m, i)} \defeq m$.
\item On morphisms, $e : \mor {(A, m, i)} {(B, n, j)}$ is sent to \[
  \xymatrix{\Fin m \ar@@{<->}[d]_-i & \Fin n \\ A \ar@@{<->}[r]_e & B
    \ar@@{<->}[u]_-{j^{-1}} } \]
\end{itemize}
The functoriality of $\size{}$ can be seen by noting the cancelling
pair of inverse equivalences in each of the following two diagrams:
  \[ \xymatrix{\Fin m \ar@@<-.4em>@@{<->}[d]_i
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
    \ar@@<.5ex>[l]^{\size{}}}$ constitutes a (strong) equivalence
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
  We must exhibit a natural isomorphism $\alpha : \nat{Id}{\fin{\size
      -}}$.  The component of $\alpha$ at $(A,m,i)$ must be a morphism
  in $\BT$ from $(A,m,i)$ to $(\Fin m, m, \id)$, that is, an
  equivalence $A \iso \Fin m$.  Therefore we define \[
  \alpha_{(A,m,i)} \defeq i^{-1}. \]  Naturality of $\alpha$ is given
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

Define/give intuition for ends and coends.  Talk about connection
between natural transformations and polymorphic functions, specific
ways it plays out in a dependent type theory---e.g. can we assume
parametricity for functions that abstract over things classified by
|*|? Cite Bernardy et al.

