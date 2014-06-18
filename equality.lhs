%% -*- mode: LaTeX; compile-command: "mk" -*-

%include polycode.fmt

\chapter{Equality}
\label{chap:equality}

\todo{Write an introduction to this chapter.}

\todo{Definitional equality. Leibniz equality. Judgmental
  equality. Equivalence.  Principle of equivalence.}

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

import           SpeciesDiagrams (enclose)

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
      || Just i == opts ^. highlight = base # lw veryThick # lc black
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
    mkSel i shp (Just j)
      = (shp 1 # sized (Dims 1 1) # centerXY <> phantom (square 1 :: D R2))
        # fc (cycle colors !! j) # named ("b" .> i .> j)
    mkSel _ _ _ = mempty

dia = lwO 0.7 . frame 1 $   -- $
  vcat' (with & sep .~ 2)
    [ collection
    , choice
    ]
    # applyAll
      [ connectOutside' aOpts (mkNm i j) ("b" .> mkNm i j)
      || i      <- [0..5]
      || Just j <- selections
      ]

aOpts = with & shaftStyle %~ lc grey
             & headTexture .~ solid grey
             & headGap .~ Local 0.5
             & headLength .~ Local 0.5

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
categories.  In fact, the underlying issue is the same, that is,
functors defined only up to unique isomorphism; equivalence of
categories is just a particularly important instantiation.

Recall, from \pref{sec:ct-fundamentals}, the definition of equivalence
of categories:
\begin{repdefn}{defn:cat-equiv}
  An \term{equivalence} between $\C$
  and $\D$ is given by functors $\BackForth \C F G \D$ which are
  inverse up to natural isomorphism, that is, $GF \iso 1_\C$ and $FG
  \iso 1_\D$.
\end{repdefn}
In set theory, a function is a bijection---that is, an isomorphism of
sets---if and only if it is both injective and surjective.  By
analogy, one might wonder what properties a functor $F : \C \to \D$
must have in order to be one half of an equivalence.  This leads to
the following definition:

\begin{defn} \label{defn:protoequiv}
  $\C$ is \term{protoequivalent} to $\D$ if there is a functor $F
  : \C \to \D$ which is full and faithful (\ie a bijection on each
  hom-set) as well as \term{essentially surjective}, that is, for
  every object $D \in \D$ there exists some object $C \in \C$ such
  that $F(C) \iso D$.
\end{defn}

Intuitively, this says that $F$ ``embeds'' an entire copy of $\C$ into
$\D$ (the ``full and faithful'' part of the definition), and that
every object of $D$ which is not directly in the image of $F$ is
isomorphic to one that is.  So every object of $\D$ is ``included'' in
the image of $\C$, at least up to isomorphism (which is supposed to be
all that matters).

So, are equivalence and protoequivalence the same thing? In one
direction, it is not too hard to show that every equivalence is a
protoequivalence: if $F$ and $G$ are inverse up to natural
isomorphism, then they must be fully faithful and essentially
surjective.  It would be nice if the converse were also true: in that
case, in order to prove two categories equivalent, it would suffice to
construct a single functor $F$ from one to the other, and show that
$F$ has the requisite properties.  This often ends up being more
convenient than explicitly constructing two functors and showing they
are inverse.  However, it turns out that the converse is provable
\emph{only} if one accepts the axiom of choice!\footnote{At this point
  I should note that ``protoequivalence'' is not standard terminology,
  and now it should be clear why: there is no need for a separate term
  if one accepts the axiom of choice.}  To get an intuitive sense for
why this is, suppose $F : \C \to \D$ is fully faithful and essentially
surjective.  To construct an equivalence between $\C$ and $\D$
requires defining a functor $G : \D \to \C$ which is inverse to $F$
(up to natural isomorphism).  However, to define $G$ we must give its
action on each object $D \in \D$, that is, we must exhibit a function
$\Ob \D \to \Ob \C$.  We know that for each $D \in \D$ there
\emph{exists} some object $C \in \C$ with $F\ C \iso D$. That is, \[
\{ \left\{ C \in \C \mid F\ C \iso D \} \mid D \in \D \right\} \] is a
collection of nonempty sets.  However, in a non-constructive logic,
knowing these sets are nonempty does not actually give us any objects.
Instead, we must use the axiom of choice, which yields a choice
function $\Ob \D \to \Ob \C$, and this function can serve as the
object mapping of the functor $G$.

So AC is required to prove that every protoequivalence is an
equivalence.  In fact, the association goes deeper yet: it turns out
that the statement
\begin{equation}
  \text{every protoequivalence is an equivalence} \tag{AP} \label{eq:AP-eqv}
\end{equation}
(let's call this the ``Axiom of Protoequivalence'', or AP) not only
requires AC, but is \emph{equivalent} to it, in the sense that AC is
derivable given AP as an exiom \citep{cat-equivalence-AC}!

On purely intuitive grounds, however, it still ``feels'' like AP
``ought to be'' true.  The particular choice of functor $G : \D \to
\C$ ``doesn't matter'', since it makes no difference up to
isomorphism.  One is therefore left in the awkward position of having
two logically equivalent statements which it seems ``ought to be''
respectively affirmed and rejected.

Obviously this is not a tenable state of affairs; there are (at least)
four options for resolving the situation.

\begin{enumerate}
\item If one is feeling particularly rational, one can simply say,
  ``Since AC and AP are equivalent, and I reject AC, I must therefore
  reject AP as well; my \emph{feelings} about it are irrelevant.''
\end{enumerate}

This is a perfectly sensible and workable approach.  It's important to
highlight, therefore, that the ``problem'' is in some sense more a
\emph{philosophical} problem than a \emph{technical} one.  One can
perfectly well adopt the above solution and continue to do category
theory; it just may not be the ``nicest'' (a philosophical rather than
technical notion!) way to do it.

There are also, however, several more creative options:

\begin{enumerate}[resume]
\item In a classical setting, one can avoid AC and affirm (an analogue
  of) AP by generalizing the notion of functor to that of
  \term{anafunctor}~\cite{makkai1996avoiding}.  Essentially, an
  anafunctor is a functor ``defined only up to unique isomorphism''.
  It turns out that the appropriate analogue of AP, where ``functor''
  has been replaced by ``anafunctor'', is indeed true---and neither
  requires nor implies AC.  Anafunctors ``act like'' functors in a
  sufficiently strong sense that one can simply do category theory
  using anafunctors in place of functors.  However, one also has to
  replace natural transformations with ``ananatural transformations'',
  and so on, and it quickly gets rather fiddly.  Anafunctors are
  defined and discussed in more detail in \pref{sec:anafunctors}.

\item In a constructive setting, a witness of essential surjectivity
  is necessarily a function which gives an \emph{actual witness} $C
  \in \C$, along with a proof that $F\ C \cong D$, for each $D \in
  \D$.  In other words, a constructive witness of essential
  surjectivity is already a ``choice function'', and an inverse
  functor $G$ can be defined directly, with no need to invoke AC and
  no need for anafunctors.  So in constructive logic, AP is simply
  true.  However, this version of ``essential surjectivity'' is rather
  strong, in that it forces you to make choices you might prefer not
  to make: for each $D \in \D$ there might be many isomorphic $C \in
  \C$ to choose from, with no ``canonical'' choice, and it is annoying
  (again, a philosophical rather than technical consideration!) to be
  forced to choose one.

\item Instead of generalizing functors, a more direct solution is to
  \emph{generalize the notion of equality}.  After all, what really
  seems to be at the heart of all these problems is differing notions
  of equality (\ie equality of sets, isomorphism, equivalence \dots).
  In fact, this is precisely what is done in HoTT. \bay{As a
    historical note
    \url{http://byorgey.wordpress.com/2014/05/13/unique-isomorphism-and-generalized-the/\#comment-13123},
    it seems that the original work on anafunctors is part of the same
    intellectual thread that led to the development of HoTT.}  It
  turns out that if one builds up suitable notions of category theory
  on top of HoTT instead of set theory, then AP is true, without the
  need for AC, and even with a \emph{weaker} version of essential
  surjectivity that corresponds more closely to essential surjectivity
  in classical logic, using propositional truncation to encode the
  classical notion of existence. This is discussed in more detail
  in \pref{sec:ct-hott}.
\end{enumerate}

\subsection{Cliques}
\label{sec:cliques}

As a preface to anafunctors, we begin with a brief outline of the
theory of \term{cliques}, which are a formal way of representing the
informal notion of ``equivalence class of uniquely isomorphic
objects''. \todo{say something else here?}

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
  There are two things worth pointing out about this definition.
  First, note that the same object may occur multiple times in the
  collection $A$---that is, multiple different values of $I$ may index
  the same object of $\C$.  Second, note that the last two conditions
  together imply $u_{ij} = u_{ji}^{-1}$, since $u_{ij} \then u_{ji} =
  u_{ii} = id$.
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

As an intuition for anafunctors it is helpful to keep in mind the
equivalent concept of functors $\C \to \clq \D$---both represent
functors whose ``values are specified only up to unique isomorphsim''.
Such functors represent a many-to-many relationship between objects of
$\C$ and objects of $\D$.  Normal functors, as with any function, may
of course map multiple objects of
$\C$ to the same object in $\D$.  The novel aspect is the ability to
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

table2 = map ((id &&& ((<> square 1 # lw none) . text)) . show) [1..4]

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
  # lwO 0.7
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
  one) if there is some $s$ for which $D \iso F_s(C)$.

  The idea now is to impose additional conditions which ensure that
  $F$ ``acts like'' a regular functor $\C \to \D$.
  \begin{itemize}
  \item Functors are defined on all objects; so we require each object
    of $\C$ to have at least one specification $s$ which corresponds
    to it---that is, $\lana{F}$ must be surjective.
  \item Functors transport morphisms as well as objects.  For each
    $s,t \in S$ (the middle of the below diagram) and each $f :
    \lana{F}(s) \to \lana{F}(t)$ in $\C$ (the left-hand side below),
    there must be a morphism $F_{s,t}(f) : \rana{F}(s) \to
    \rana{F}(t)$ in $\D$ (the right-hand side):
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
  # lwO 0.7

aOpts = with & gaps .~ Local 0.2 & headLength .~ Local 0.4
      \end{diagram}
    \end{center}
  \item Functors preserve identities: for each $s \in S$ we should
    have $F_{s,s}(\id_{\lana{F}(s)}) = \id_{\rana{F}(s)}$.
  \item Finally, functors preserve composition: for all $s,t,u \in
    S$ (in the middle below), $f : \lana{F}(s) \to \lana{F}(t)$, and $g : \lana{F}(t) \to
    \lana{F}(u)$ (the left side below), it must be the case that $F_{s,u}(f \then g) =
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
  # lwO 0.7

aOpts = with & gaps .~ Local 0.2 & headLength .~ Local 0.4
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
  fully faithful and (strictly) surjective on objects.
\end{defn}

\begin{rem}
  Note that in this definition, $\lana{F}$ must be \emph{strictly}
  (as opposed to \emph{essentially}) surjective on objects, that is,
  for every $C \in \C$ there is some $S \in \Spec$ such that
  $\lana{F}(S) = C$, rather than only requiring $\lana{F}(S) \iso
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
anafunctor \[ \Span \C \Id \C F \D. \] Anafunctors also compose.
Given compatible anafunctors $F : \Span \C {\lana F} S {\rana F} \D$
and $G : \Span \D {\lana G} T {\rana G} \E$, consider the action of
their composite on objects: each object of $\C$ may map to multiple
objects of $\E$, via objects of $\D$.  Each such mapping corresponds
to a zig-zag path \[ \xymatrix@@dr{ & t & E \\ s & D \\ C } \]  In
order to \emph{specify} such a path it suffices to give the pair
$(s,t)$, which determines $C$, $D$, and $E$.  Note, however, that not
every pair in $S \times T$ corresponds to a valid path, but only those
which agree on the middle object $D \in \D$.  Thus, we
may take $\{ (s,t) \mid s \in S, t \in T, \rana{F}(s) = \lana{G}(t)
\}$ as the set of specifications for the composite $F \then G$, with
$\lana{F \then G}(s,t) = \lana{F}(s)$ and $\rana{F \then G}(s,t) =
\rana{G}(t)$. On morphisms, $(F \then G)_{(s,t),(u,v)}(f) =
G_{t,v}(F_{s,u}(f))$.  It is not hard to check that this satisfies the
anafunctor laws.

The same thing can also be defined at a higher level in terms of
spans: \[ \xymatrix@@dr{ \Spec \times_\D \bbb{T} \ar[d]_{\lana F'}
  \ar[r]^{\rana G'} & \bbb{T} \ar[d]_{\lana G} \ar[r]^{\rana G} & \E
  \\ \Spec \ar[d]_{\lana F} \ar[r]^{\rana F} & \D \\ \C } \] $\Cat$ is
cocomplete, and in particular has pullbacks, so we may construct a new
anafunctor from $\C$ to $\E$ by taking a pullback of $\rana F$ and
$\lana G$ and then composing appropriately, as illustrated in the
diagram.

One can go on to define ananatural transformations between
anafunctors, and show that together these constitute a $2$-category
$\mathbf{AnaCat}$ which is analogous to the usual $2$-category of
(small) categories, functors, and natural transformations; in
particular, there is a fully faithful embedding of $\mathbf{Cat}$ into
$\mathbf{AnaCat}$, which moreover is an equivalence if AC holds.

To work in category theory based on set theory and classical logic,
while avoiding AC, one is therefore justified in ``mixing and
matching'' functors and anafunctors as convenient, but discussing them
all as if they were regular functors (except when defining a
particular anafunctor).  Such usage can be formalized by turning
everything into an anafunctor, and translating functor operations and
properties into corresponding operations and properties of
anafunctors.  However, as we will see, by founding category theory on
HoTT instead of category theory, this becomes unnecessary.

\section{Category theory in HoTT}
\label{sec:ct-hott}

As hinted earlier, category theory works much more nicely when founded
in HoTT instead of set theory.  Intuitively, the main reason is that
in set theory the only notion of equality (extensional equality of
sets) is too impoverished---one really wants to work up to
\emph{isomorphism} rather than literal equality, and the mismatch
between isomorphism and strict equality introduces all sorts of
difficulties and extra work.  In contrast, via the univalence axiom,
HoTT has a very rich notion of equality that is able to encompass
isomorphism in categories.

This section lays out a few relevant definitions along with some
intuition and commentary.  A fuller treatment may be found in Chapter
9 of the HoTT book~\citep{hottbook}.  Generally, ``\hott{widget}'' is
used to refer to widgets as defined in HoTT, to distinguish from
widgets as defined in set theory.

We begin with the definition of a \term{precategory}.

\begin{defn}
  A \term{precategory} $\CT$ consists of
  \begin{itemize}
  \item A type $\CT_0 : \Type$ of objects (we often write simply
    $c : \CT$ instead of $c : \CT_0$);
  \item a function $- \homsymb - : \CT \to \CT \to \SetT$ associating
    a \emph{set} ($0$-type) of morphisms to each pair of objects (we
    often write $\hom[\CT] X Y$ to indicate the precategory being
    referenced, especially when multiple precategories are under
    consideration);
  \item a function $\idT : (X : \CT) \to (\hom X X)$ associating
    an identity morphism to each object;
  \item a function $- \then - : (X,Y,Z : \CT) \to (\hom X Y) \to
    (\hom Y Z) \to (\hom X Z)$; and
  \item proofs of the identity and associativity laws.
  \end{itemize}
\end{defn}

\begin{rem}
  Note how well the idea of types fits the definition: in the usual
  set-theoretic definition of a category, one must resort to awkward
  constructions like saying that composition is a partial function,
  with $f \then g$ being defined only when $\mathrm{tgt}(f) =
  \mathrm{src}(g)$.  Here, the same idea is expressed simply as the
  type of the composition operator.

  The restriction that $\hom X Y$ is a \emph{set}, \ie a $0$-type
  (rather than an arbitrary type) is important: otherwise one runs
  into problems with coherence of the identity and associativity laws,
  and extra laws become necessary.  Down this path lies $n$-categories
  or even $(\infty,1)$-categories; but to model traditional
  ($1$-)categories, it suffices for $\hom X Y$ to be a $0$-type.  In
  particular, this means that the identity and associativity laws,
  being equalities between elements of a $0$-type, are themselves
  $(-1)$-types, \ie mere propositions.
\end{rem}

One might wonder why the term \term{precategory} is used for something
that is evidently a straightforward port of the definition of a
category from set theory into HoTT.  The problem is that this
definition suffers from problems similar to the one in set theory:
there is not necessarily a strong enough connection between
isomorphism and equality.  This is remedied in the definition of an
\hott{category}.

\begin{defn}
  An \term{isomorphism} in $\CT$ is a morphism $f : \hom X Y$
  together with a morphism $g : \hom Y X$ such that $f \then g =
  \idT_X$ and $g \then f = \idT_Y$.  We write $X \iso Y$ for the type
  of isomorphisms between $X$ and $Y$.
\end{defn}

\begin{rem}
  Note the distinction between $X \iso Y$, the type of isomorphisms
  between $X$ and $Y$ as objects in the precategory $\CT$, and $X \equiv
  Y$, the type of equivalences between the types $X$ and $Y$.  The
  latter consists of a pair of inverse functions; the former of a pair
  of inverse \emph{morphisms}.  Morphisms, of course, need not be
  functions, and moreover, objects need not be types.
\end{rem}

It is immediate, by path induction and the fact that $\idT_X$ is an
isomorphism, that equality implies isomorphism: we call this $\idtoiso
: (X = Y) \to (X \iso Y)$.  However, the other direction is not
automatic.  Note it does not follow from univalence, due to the
distinction between $X \iso Y$ and $X \equiv Y$. However, it has a very
similar flavor to univalence, and matches the intuition that one
should always work up to isomorphism in a category.  It is therefore
added as a requirement of an \hott{category}.

\begin{defn}
  An \term{\hott{category}} is a precategory $\CT$ together with the
  additional univalence-like axiom that for all $X,Y : \CT$, \[ (X \iso
  Y) \equiv (X = Y). \] We write $\isotoid : (X \iso Y) \to (X = Y)$
  for the left-to-right direction of the equivalence.
\end{defn}

An \hott{groupoid} is an \hott{category} where every morphism is an
isomorphism. The following example will play an important role later.

\begin{defn}
  Any $1$-type $T$ gives rise to an \hott{groupoid} $\tygrpd{T}$ where the
  objects are values $a : T$, and $\hom a b \defeq a = b$, that
  is, morphisms from $a$ to $b$ are paths $p : a = b$.
\end{defn}

\begin{proof}
  Identity morphisms, composition, the identity laws, associativity,
  and the fact that every morphism is an isomorphism all follow
  directly from properties of propositional equality.  Since
  isomorphisms are already paths, $\isotoid$ is just the identity.
\end{proof}

Another important example is ana analogue to the usual category \Set
of sets and functions.

\begin{defn}[\citep{hottbook}, Examples 9.1.5 and 9.1.7]
  Let $\ST$ denote the \hott{category} of sets, that is, the category
  whose objects are $0$-types, \ie sets, and whose morphisms are
  functions $A \to B$.
\end{defn}
\begin{proof}
  This category is defined in the HoTT book in examples 9.1.5 and
  9.1.7, and explored extensively in Chapter 10.  However, the proof
  given in Example 9.1.7 leaves out some details, and it is worth
  spelling out the construction here.

  Of course, identity morphisms are given by the identity function,
  and morphism composition by function composition, so the identity
  and associativity laws are satisfied. The definition also satisfies
  the requirement that the type of morphisms is a set, since $A \to B$
  is a set whenever $B$ is.

  Finally, suppose $A \iso B$, that is, there are functions $f : A \to
  B$ and $g : B \to A$ such that $f \comp g = \id_B$ and $g \comp f =
  \id_A$.  It is not \latin{a priori} obvious that this is the same as
  an equivalence $A \equiv B$---indeed, it turns out to be so only
  because $A$ and $B$ are sets.  Technically, $(A \iso B)$ constitutes
  a \term{quasi-inverse} between $A$ and $B$, that is, $(A \iso B)
  \equiv (f : A \to B) \times \qinv(f)$, where $\qinv(f) \defeq (g : B
  \to A) \times (f \comp g = \id_B) \times (g \comp f = \id_A)$. On
  the other hand, $(A \equiv B) \equiv (f : A \to B) \times
  \isequiv(f)$.  The precise definition of $\isequiv(f)$ can be found
  in Chapter 4 of the HoTT book; for the present purpose, it suffices
  to say that although $\qinv(f)$ and $\isequiv(f)$ are
  \emph{logically} equivalent (that is, each implies the other),
  $\isequiv(f)$ is always a mere proposition but in general $\qinv(f)$
  may not be.  However, in the specific case that $A$ and $B$ are
  sets, $\qinv(f)$ is indeed a mere proposition: by Lemma 4.1.4 in the
  HoTT book, if $\qinv(f)$ is inhabited then it is equivalent to
  $(x:A) \to (x = x)$, which is a mere proposition by function
  extensionality and the fact that $A$ is a set.  Therefore $\qinv(f)
  \equiv \isequiv(f)$, since logically equivalent mere propositions
  are equivalent, and we have $(A \iso B) \equiv (A \equiv B) \equiv
  (A = B)$ by univalence.
\end{proof}

The definitions of \hott{functors} and \hott{natural transformations}
are straightforward ports of their usual definitions in set theory.

\begin{defn}
  An \hott{functor} $F$ between (pre)categories $\CT$
  and $\DT$ is a pair of functions
  \begin{itemize}
  \item $F_0 : \CT_0 \to \DT_0$
  \item $F_1 : (X,Y : \CT) \to (\hom[\CT] X Y) \to (\hom[\DT] {F_0(X)} {F_0(Y)})$
  \end{itemize}
  together with proofs of the functor laws,
  \begin{itemize}
  \item $(X : \CT) \to (F_1(\idT_X) = \idT_{F_0(X)})$, and
  \item $(X,Y,Z : \CT) \to (f : \hom[\CT] X Y) \to (g : \hom[\CT] Y Z)
    \to (F_1(f \then g) = F_1(f) \then F_1(g))$.
  \end{itemize}
\end{defn}

As is standard, we often write $F\ X$ and $F\ f$ instead of $F_0(X)$
and $F_1(f)$.

\begin{defn}
  An \hott{natural transformation} $\gamma$ between functors $F,G :
  \CT \to \DT$ is a family of morphisms
  \begin{itemize}
  \item $\gamma_X : \hom[\DT] {F\ X} {G\ X}$
  \end{itemize}
  for each $X : \CT$, satisfying
  \begin{itemize}
  \item $(X,Y : \CT) \to (f : \hom[\CT] X Y) \to (\gamma_X \then G f
    = F f \then \gamma_Y)$.
  \end{itemize}
\end{defn}

\subsection{Coends}
\label{sec:coends-hott}

\bay{Where should this section go?}
\todo{Write me.}

\section{Finiteness in set theory}
\label{sec:finiteness-sets}

\todo{Should discuss somewhere why it is so important to discuss all
  this stuff with P, B, and finiteness.}

Finally, we can assemble the foregoing material on anafunctors and
category theory in HoTT into a coherent story about representing
evidence of finiteness, first using set-theoretic foundations, and
then in HoTT.

Recall that $\B$ denotes the groupoid of finite sets and bijections,
and $\P$ the groupoid of natural numbers and permutations.  In
classical category theory, $\P$ is a \term{skeleton} of
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
\bij T$ to a permutation $\fin{\size S} \bij \fin{\size T}$, and there
is no obvious way to pick one.  For example, suppose $S =
\{\text{cat}, \text{dog}, \text{moose}\}$ and $T =
\{
\begin{diagram}[width=10]
  dia = circle 1 # frame 0.1
\end{diagram}
,
\begin{diagram}[width=10]
  dia = triangle 1 # centerXY # frame 0.1
\end{diagram}
,
\begin{diagram}[width=10]
  dia = square 1 # frame 0.1
\end{diagram}
\}$.  Given a bijection matching each animal with its favorite
shape\footnote{The details are left as an exercise for the reader.},
it must be sent to a permutation on $\{0,1,2\}$---but there is no
canonical relationship between these natural numbers and either
animals or shapes.

More abstractly, $\fin - : \P \to \B$ is fully faithful and
essentially surjective (every finite set is in bijection with $\fin n$
for some $n$); this yields an equivalence of categories (and hence an
inverse functor $\size - : \B \to \P$) only in the presence of AC.

Concretely, we can use AC to choose an arbitrary bijection $\varphi_S
: S \bij \fin{\size S}$ for each finite set $S$, matching up $S$ with
a canonical set of size $\size S$. Given $\alpha : S \bij T$ we can
then construct $\xymatrix{ \fin{\size S} \ar[r]^-{\varphi_S^{-1}} & S
  \ar[r]^\alpha & T \ar[r]^-{\varphi_T} & \fin{\size T}}$.  As is
familiar by now, this use of AC is ``benign'' in the sense that any
two sets of choices yield equivalent functors; it thus yields a
well-defined functor but has no computational interpretation.

We can avoid the use of AC by constructing an anafunctor $\size - : \B
\to \P$ instead of a functor.  In particular, as the class of
specifications $S_{\size{}}$, we choose the class of all bijections
$\sum_{T \in \B} (T \bij \fin{\size T})$.  The function $\sigma :
S_{\size{}} \to \Ob \B$ simply forgets the chosen bijection,
$\sigma(T,\varphi) = T$, and $\tau : S_{size{}} \to \Ob \P$ sends
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

Before returning to HoTT, it should be noted that there is an alternate
way around the use of AC in this particular case, using the theory of
\term{hereditarily finite} sets.
\begin{defn}
  A \term{hereditarily finite} set is a finite set, all of whose
  elements are hereditarily finite.
\end{defn}
This definition gets off the ground since the empty set is vacuously
hereditarily finite.  As is usual in set theory, this definition is
interpreted recursively, so there cannot be any infinitely descending
membership chains.  Hereditarily finite sets can thus be seen as
finitely-branching, finite-depth trees.

Now consider the groupoid $\cat{H}$ obtained by replacing ``finite''
with ``hereditarily finite'' in the definition of $\B$.  That is, the
elements of $\cat{H}$ are hereditarily finite sets, and the morphisms
are bijections.  Replacing $\B$ by $\cat{H}$ in the definition of
species is really no great loss, since we are interested in modelling
sets of ``labels'', and there is no particular reason to have labels
modelled by infinite sets.

Unlike the class of all sets, however, the class of all hereditarily
finite sets (normally written $V_\omega$) has a well-ordering.  For
example, to order two hereditarily finite sets, we can first
inductively sort their elements, and then do a lexicographic
comparison.  This means that every hereditarily finite set has an
induced ordering on its elements, since they are themselves
hereditarily finite. In other words, picking a well-ordering of
$V_\omega$ is like making a ``global'' choice of orderings, assigning
a canonical bijection $S \bij \fin{\size S}$ for every hereditarily
finite set $S$.

However, this construction is somewhat arbitrary, and has no natural
counterpart in type theory, or indeed in a structural set theory.  The
concept of hereditary finiteness only makes sense in a material set
theory such as ZF.  To determine the canonical ordering on, say,
$\{\text{dog}, \text{cat}, \text{moose}\}$, we need to know the
precise identity of the set used to encode each animal---but,
intuitively, knowing their precise encoding as sets violates the
principle of equivalence, since there may be many possible encodings
with the right properties.  Using a well-ordering on $V_\omega$ to
avoid AC in this case is therefore little more than a curiosity.

\section{Finiteness in HoTT}
\label{sec:finiteness-hott}

We now turn to developing counterparts to the groupoids $\P$ and $\B$
in type theory.  First, a few necessary lemmas:
\begin{lem} \label{lem:equiv-pres-set}
  Equivalence preserves sets, that is, if $A$ and
  $B$ are sets, then so is $A \equiv B$.
\end{lem}
\begin{proof}
  $(A \equiv B) \equiv ((f : A \to B) \times \cons{isequiv}(f))$, where
  $\cons{isequiv}(f)$ is a mere proposition expressing the fact that
  $f$ is an equivalence (\ie has a suitable inverse).  This is a set
  since $\cons{isequiv}(f)$ is a mere proposition (and hence a set),
  $A \to B$ is a set whenever $B$ is, and $\times$ takes sets to sets
  \citep[Lemma 3.3.4, Examples 3.1.5 and 3.1.6]{hottbook}.
\end{proof}

\begin{cor}
  If $A$ and $B$ are sets, then so is $A = B$.
\end{cor}
\begin{proof}
  Immediate from univalence and \pref{lem:equiv-pres-set}.
\end{proof}

\begin{lem} \label{lem:fin-iso-equal}
  For all $n_1, n_2 : \N$, if $\Fin{n_1} \equiv \Fin{n_2}$ then $n_1 =
  n_2$.
\end{lem}
\begin{proof}
  The proof is by double induction on $n_1$ and $n_2$.
  \begin{itemize}
  \item If both $n_1$ and $n_2$ are zero, the result is immediate.
  \item The case when one is zero and the other a successor is
    impossible.  In particular, taking the
    equivalence in the appropriate direction gives a function $\Fin
    (\suc \dots) \to \Fin \zero$, which can be used to produce an
    element of $\Fin \zero = \bot$, from which anything follows.
  \item In the case when both are a successor, we have
    $\Fin{(\suc{n_1'})} \equiv \Fin{(\suc{n_2'})}$, which is equivalent
    to $\top + \Fin{n_1'} \equiv \top + \Fin{n_2'}$.  If we can conclude
    that $\Fin{n_1'} \equiv \Fin{n_2'}$, the inductive hypothesis then
    yields $n_1' = n_2'$, from which $\suc{n_1'} = \suc{n_2}'$ follows
    immediately.  The implication $(\top + \Fin{n_1'} \equiv \top +
    \Fin{n_2'}) \to (\Fin{n_1'} \equiv \Fin{n_2'})$ is true, but not
    quite as straightforward to show as one might think! In
    particular, an equivalence $(\top + \Fin{n_1'} \equiv \top +
    \Fin{n_2'})$ may not match the $\top$ values with each other.  As
    illustrated in \pref{fig:gcbp-Maybe}, given $e : (\top +
    \Fin{n_1'} \equiv \top + \Fin{n_2'})$, it suffices to define
    $e'(e^{-1}\ \unit) = e\ \unit$, with the rest of $e' : \Fin{n_1'}
    \equiv \Fin{n_2'}$ defined as a restriction of $e$.  This
    construction corresponds more generally to the \term{Gordon
      complementary bijection principle}~\citep{gcbp}, to be discussed
    in more detail in \pref{sec:gcbp}.
  \end{itemize}
\end{proof}

\begin{figure}
  \centering
  \begin{diagram}[width=300]
fin_ = zipWith named [1 :: Int ..] (replicate 5 (square 1))

fin x = hcat (x ||> fin_)

t_ = named (0 :: Int) (square 1)

tfin x =
  hcat' (with & sep .~ 0.5)
    [ (x ||> t_)
    , text "+" <> square 1 # lw none
    , fin x
    ]

ht = 3

dashSty = dashingG [0.1,0.1] 0 . lc red

bij = [ ((0, 1), Just dashSty)
      , ((1, 2), Nothing)
      , ((2, 3), Nothing)
      , ((3, 0), Just dashSty)
      , ((4, 5), Nothing)
      , ((5, 4), Nothing)
      ]

tfin_e =
  vcat' (with & sep .~ ht)
  [tfin 'A', tfin 'B']
  # applyAll
    [ conn sty ('A' .> (x :: Int)) ('B' .> (y :: Int)) || ((x,y), sty) <- bij ]

fin_e =
  vcat' (with & sep .~ ht)
  [fin 'A', fin 'B']
  # applyAll
    [ conn sty ('A' .> (x :: Int)) ('B' .> (y :: Int))
    || ((x,y), sty) <- filter (\((x,y), _) -> x /= 0 && y /= 0) bij ++ [((3,1), Just (lc red . lw thick))]
    ]

conn msty x y = connect' aOpts x y
  where
    aOpts
      || Just sty <- msty = basicOpts & shaftStyle %~ sty
      || otherwise        = basicOpts
    basicOpts = with & arrowHead .~ noHead

dia = hcat' (with & sep .~ 2)
  [ tfin_e # centerY
  , text "⇒" # fontSizeL 1.5 <> square 1 # lw none
  , fin_e # centerY
  ]
  # frame 0.5
  # lwO 0.7
  \end{diagram}
  \caption{Eliminating $\top$ from both sides of an equivalence}
  \label{fig:gcbp-Maybe}
\end{figure}

Constructing a type-theoretic counterpart to $\P$ is
now straightforward.
\begin{defn}
  $\PT$ is the \hott{groupoid} where
  \begin{itemize}
  \item the objects are values of type $\N$, and
  \item the morphisms $\mor m n$ are equivalences of type $\Fin m \equiv
    \Fin n$.
  \end{itemize}
\end{defn}
It is easy to check that this satisfies the axioms for an
\hott{category}, the salient points being that $\Fin m \equiv \Fin n$ is
a set by \pref{lem:equiv-pres-set}, and $\isotoid$ follows from
\pref{lem:fin-iso-equal}.

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
\[ \FinType \defeq (A : \Type) \times (n : \N) \times (A \equiv \Fin n). \]

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
        , (unit_Y # rotateBy (-1/3), text' 4 "A₁"   )
        , (unit_Y # rotateBy (1/3) , text' 4 "A₂"   )
        ]
      # lwO 0.7
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

This suggests a better encoding of finiteness in type theory, \[
\FinTypeT' \defeq (A : \Type) \times \ptrunc{(n : \N) \times (A \equiv
  \Fin n)}, \] making use of propositional truncation to encode the
fact that there \emph{merely exists} some size $n$ and an equivalence
between $A$ and $\Fin n$, but without exposing a precise choice.  The
finiteness evidence is now irrelevant to paths in $\FinTypeT'$, since
there is always a path between any two elements of a truncated type.
We also note the following:
\begin{prop}
  For any type $A$, \[ \ptrunc{(n : \N) \times (A \equiv \Fin n)} \equiv
  (n : \N) \times \ptrunc{A \equiv \Fin n}. \]
\end{prop}
This says that the size $n$ of a finite type may be freely moved in
and out of the propositional truncation.  Practically, this means we
may freely refer to the size of a finite type without worrying about
how it is being used (in contrast, the value of the equivalence $A
\equiv \Fin n$ may only be used in constructing mere propositions).
The proof hinges on the fact that $(n : \N) \times \ptrunc{A \equiv \Fin
  n}$ is a mere proposition; intuitively, if a type is finite at all,
there is only one possible size it can have, so putting $n$ inside the
truncation does not really hide anything.
\begin{proof}
  We must exhibit a pair of inverse functions between the given types.
  A function from right to left is given by \[ f(n, \ptruncI e) =
  \ptruncI{(n,e)}, \] where pattern matching on $\ptruncI e :
  \ptrunc{A \equiv \Fin n}$ is shorthand for an application of the
  recursion principle for propositional truncation.  Recall that this
  recursion principle only applies in the case that the result is a
  mere proposition; in this case, the result is itself a propositional
  truncation which is a mere proposition by construction.

  In the other direction, define \[ g(\ptruncI{(n, e)}) = (n,\ptruncI
  e), \] which is clearly inverse to $f$.  It remains only to show
  that the implicit use of recursion for propositional truncation is
  justified, \ie that $(n : \N) \times \ptrunc{A
    \equiv \Fin n}$ is a mere proposition.

  We must show that any two values $(n_1, e_1), (n_2, e_2) : (n : \N)
  \times \ptrunc{A \equiv \Fin n}$ are propositionally equal.  Since
  $e_1$ and $e_2$ are mere propositions, it suffices to show that $n_1
  = n_2$.  This equality is itself a mere proposition (since $\N$ is a
  set, which follows from its induction principle), so we may apply
  the recursion principle for propositional truncation to $e_1$ and
  $e_2$, giving us equivalences $A \equiv \Fin n_1$ and $A \equiv \Fin
  n_2$ to work with.  By symmetry and transitivity, $\Fin n_1 \equiv
  \Fin n_2$, and thus $n_1 = n_2$ by \pref{lem:fin-iso-equal}.
\end{proof}

There is still one remaining problem, which is that $\FinTypeT'$ is
not a $1$-type, and hence $\tygrpd{-}$ does not apply. To solve this
we may simply restrict to $0$-types $A$ (which is arguably a more
faithful encoding of the situation in set theory anyway). This yields
our final definition:

\begin{defn}
  The type of finite sets is given by \[ \FinTypeT \defeq (A : \Type)
  \times \isSet(A) \times \isFinite(A), \] where \[ \isFinite(A)
  \defeq \ptrunc{(n : \N) \times (A \equiv \Fin n)}. \]
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

It is worth pointing out that with this definition of $\BT$, we have
ended up with something akin to the category of specifications
$\Spec_{\size{}}$ used to define the anafunctor $\size : \B \to \P$ in
\pref{sec:finiteness-sets}, rather than something corresponding
directly and na\"ively to $\B$ itself. The main difference is that
$\BT$ uses a propositional truncation to ``hide'' the explicit choice
of finiteness evidence.

We now turn to the equivalence of $\PT$ and $\BT$.

\begin{defn}
  We can easily define a functor $\fin - : \PT \to \BT$: on objects,
  it sends $n$ to $\Fin n$, along with proofs that it is a set and
  finite (using the identity equivalence for the latter).  On
  morphisms, it sends $f : \Fin m \equiv \Fin n$ to $\ua\ f : \Fin m =
  \Fin n$.
\end{defn}

However, it is not at all obvious how to directly define a functor
$\size : \BT \to \PT$. Just as with $\B \to \P$, defining its action
on morphisms requires a specific choice of equivalence $A \equiv \Fin
n$. The objects of $\BT$ contain such equivalences, in the proofs of
finiteness, but they are propositionally truncated; the type of
functors $\BT \to \PT$ is decidedly not a mere proposition, so it
seems the recursion principle for truncation does not apply.

However, all is not lost!  We could try porting the concept of
anafunctor into HoTT, but it turns out that there is a better way.
Recall that in set theory, every fully faithful, essentially
surjective functor is an equivalence \emph{if and only if} the axiom
of choice holds.  In HoTT the situation turns out much better, thanks
to the richer notion of equality and the extra axiom associated with a
category.

\begin{lem}
  $\fin - : \PT \to \BT$ is full and faithful.
\end{lem}
\begin{proof}
  For any $m, n : \PT$, we must exhibit an equivalence between
  $(\hom[\PT] m n) \jeq (\Fin m \equiv \Fin n)$ and $\hom[\BT] {\fin
    m} {\fin n} \jeq (\fin m = \fin n) \equiv (\Fin m = \Fin
  n)$---such an equivalence is given by univalence.
\end{proof}

There are two relevant notions of essential surjectivity:

\begin{defn}
  A functor $F : \CT \to \DT$ between precategories $\CT$ and $\DT$ is
  \term{split essentially surjective} if for each object $D : \DT$
  there \emph{constructively} exists an object $C : \CT$ such that $F\
  C \iso D$. That is, \[ \msf{splitEssSurj}(F) \defeq (D : \DT) \to (C :
  \CT) \times (F\ C \iso D). \]
\end{defn}

\begin{defn}
  A functor $F : \CT \to \DT$ between precategories $\CT$ and $\DT$ is
  \term{essentially surjective} if for each object $D : \DT$ there
  \emph{merely} exists an object $C : \CT$ such that $F\ C \iso D$. That
  is, \[ \msf{essSurj}(F) \defeq (D : \DT) \to \ptrunc{ (C : \CT)
    \times (F\ C \iso D) }. \]
\end{defn}

It turns out that being split essentially surjective is a rather
strong notion.  In particular:

\begin{prop}
  For any precategories $\CT$ and $\DT$ and a functor $F : \CT \to
  \DT$, $F$ is fully faithful and split essentially surjective if and
  only if it is an equivalence.
\end{prop}
\begin{proof}
  See the HoTT book~\citep[Lemma 9.4.5]{hottbook}.  Intuitively, the
  \emph{split} essential surjectivity gives us exactly what we need to
  unambiguously \emph{construct} an inverse functor $G : \DT \to \CT$:
  the action of $G$ on $D : \DT$ is defined to be the $C$---which
  exists constructively---such that $F\ C \iso D$.
\end{proof}

That is, a fully faithful, essentially surjective functor is an
equivalence given AC; a fully faithful, \emph{split} essentially
surjective functor is an equivalence \emph{without} AC.

\begin{prop}
  $\fin -$ is essentially surjective.
\end{prop}
\begin{proof}
  Given $(S,s,f) : \BT$, we must show that there merely exists some $n
  : \PT$ such that $\fin n \iso S$---but this is precisely the
  content of the $\isFinite$ proof $f$.
\end{proof}

On the other hand, it would seem that $\fin -$ is not split
essentially surjective, since that would require extracting finiteness
proofs from the propositional truncation, which is not allowed in
general.  However:

\begin{prop}[\protect{\citep[Lemma 9.4.7]{hottbook}}]
  If $F : \CT \to \DT$ is fully faithful and $\CT$ is a category, then
  for any $D : \DT$ the type $(C : \CT) \times (F\ C \iso D)$ is a
  mere proposition.
\end{prop}

\begin{proof}[Proof (sketch)]
  From $F\ C \iso D$ and $F\ C' \iso D$ we derive $F\ C \iso F\
  C'$, and thus $C \iso C'$ (since $F$ is fully faithful), and $C =
  C'$ (since $\CT$ is a category).  The transport of the isomorphism
  $(F\ C \iso D)$ along this derived path $C = C'$ is precisely the
  isomorphism $(F\ C' \iso D)$.
\end{proof}

Intuitively, for a fully faithful functor $F : \CT \to \DT$ out of a
category $\CT$, there is ``only one way'' for some object $D : \DT$ to
be isomorphic to the image of an object of $\CT$.  That is, if it is
isomorphic to the image of multiple objects of $\CT$, then those
objects must in fact be equal.

This brings us to the punchline:

\begin{cor}
  If $\CT$ is a category, a fully faithful functor $F : \CT \to \DT$
  is essentially surjective if and only if it is split essentially surjective.
\end{cor}

Thus, since $\fin -$ is a fully faithful and essentially surjective
functor out of a category, it is in fact \emph{split} essentially
surjective and thus an equivalence.  In particular, it has an inverse
(up to natural isomorphism) which we call $\size : \BT \to \PT$.

The larger intuition here is about an answer to the question: when can
one define a function $\ptrunc{A} \to B$, when $B$ is \emph{not} a
mere proposition?  When $B$ is a mere proposition, it suffices to give
a function $A \to B$.  On the other hand, if $B$ is not a mere
proposition, it may seem that there is no useful way to construct a
function $\ptrunc{A} \to B$.  However, this is not true: if one can
\emph{uniquely characterize} a particular value of $B$---that is,
create a mere proposition $(b : B) \times Q(b)$---one can then define
a function $\ptrunc{A} \to (b : B) \times Q(b)$ from a function $A \to
(b : B) \times Q(b)$, and finally project out the $B$ to obtain a
function $\ptrunc A \to B$.  This ``trick'' is detailed in the HoTT
book~\citep[\Sect 3.9]{hottbook}; Exercise 3.19 is an excellent
exercise that also affords some good intuition for this phenomenon.

Computationally speaking, $\size : \BT \to \PT$ does precisely what we
thought was not allowed---its action on morphisms works by extracting
concrete equivalences out of the finiteness proofs in the objects of
$\BT$ and using them to construct the required permutation, just as in
the construction of the anafunctor $\size : \B \to \P$ in
\pref{sec:finiteness-sets}.  Indeed, we are not allowed to project
finiteness evidence out from the propositional truncation when
defining \emph{arbitrary} functors $\BT \to \PT$.  However, we are not
interested in constructing \emph{any old} functor, but rather a very
specific one, namely, an inverse to $\fin - : \PT \to \BT$---and the
inverse is uniquely determined.  In essence, the construction of
$\size$ proceeds by first constructing a functor paired with a proof
that, together with $\fin -$, it forms an equivalence---altogether a
mere proposition---and then projecting out the functor.

When working with species as founded in HoTT, therefore, we are fully
justified in working with them as functors from finite sets of labels,
or from natural number sizes, as convenient---the equivalence $\BT
\iso \PT$ is entirely constructive and allows species to be
converted back and forth between the two views.
