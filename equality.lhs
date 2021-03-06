%% -*- mode: LaTeX; compile-command: "mk" -*-

%include polycode.fmt

\chapter{Equality and Finiteness}
\label{chap:equality}

Before delving into combinatorial species proper, we must first tackle
some foundational issues---in particular, how equality and finiteness
are handled in a constructive setting.  As we will see, these topics
require much more care in a constructive setting than in a
classical one, but the extra care pays off in the form of deeper
insight and even (in the case of finiteness) practical
implementations.

We have already glimpsed some of the complexity surrounding equality
in \pref{chap:prelim}. Indeed, equality is the central focus of HoTT,
and we saw that HoTT allows us to talk about many different notions of
sameness.

This chapter highlights several other places where equality emerges as
the key issue at stake. \pref{sec:AC} begins by discussing the status
of the \term{axiom of choice} (AC), which is frequently used in
practice but inadmissible in a constructive setting.  One of the main
reasons that AC is used frequently in the context of category theory
in particular has to do with the difference between equality and
isomorphism. Several approaches to doing without AC are outlined,
culminating in explaining (\pref{sec:ct-hott},
\pref{sec:finiteness-hott}) why it is unnecessary when
formulating category theory inside of HoTT.

Interwoven with the story of equality and the axiom of choice is a
story about \emph{finiteness} (\pref{sec:finiteness-sets},
\pref{sec:finiteness-hott}).  In a classical setting, the notion of a
\emph{finite} set is relatively uncomplicated.  In a constructive
setting, however, it becomes much more subtle.  One must consider what
counts as \emph{constructive evidence} of finiteness, and how such
evidence may be used.  Finiteness turns out to play an important role
in the theory of species, which are \term{labelled} by finite
sets.

The key contributions of this chapter are
\begin{itemize}
\item a synthesis and presentation of many topics relevant to equality and
  finiteness (the axiom of choice, equivalence of categories,
  anafunctors, cliques, and some relevant results in HoTT) in a way
  accessible to functional programmers;
\item a development of the theory of \term{cardinal-finite sets} in HoTT;
\item development of HoTT-based analogues to the categories $\B$,
  $\P$, and $\L$.
\end{itemize}

\later{Definitional equality. Leibniz equality. Judgmental
  equality. Equivalence.  Principle of equivalence.}

\section{The axiom of choice (and how to avoid it)}
\label{sec:AC}

The (in)famous \emph{axiom of choice} (hereafter, AC) plays a central
role in much of modern mathematics.  In a constructive setting,
however, it is problematic (\pref{sec:generalized-the},
\pref{sec:AC-equivalence}).  Much effort has been expended attempting
to avoid it \citep{makkai1995first, makkai1996avoiding,
  makkai1998towards, voevodskyFoundations}; in a sense, this can be
seen as one of the goals of the univalent foundations program.  In
\pref{sec:ct-hott} and \pref{sec:finiteness-hott} we will see how HoTT
indeed provides an excellent AC-free foundation for the mathematics we
want to do.  First, however, we give an introduction to AC and related
issues in set theory.

\subsection{The axiom of choice and constructive mathematics}
\label{sec:AC-constructive}

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
that it is consistent to add either AC or its negation to ZF.  It is
somewhat controversial since it has some (seemingly) strange
consequences, \eg the Banach-Tarski paradox~\citep{wagon1993banach}.
However, most mathematicians have come to accept it, and work (in
principle) within ZF extended with AC, known as ZFC.

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
implementing a function of this type is a simple \mbox{exercise}!  The
intuitive idea can be grasped by implementing a non-dependent
analogue, say, a Haskell function of type |(i -> (a,c)) -> (i -> a, i
-> c)|.  This is quite easy to implement, and the dependent version is
essentially no harder; only the types get more complicated, not
the implementation.  So what's going on here?  Why is AC so
controversial if it is simply \emph{true} in type theory?

The problem, it turns out, is that we've modelled the axiom of choice
improperly, and it all boils down to how ``non-empty'' is defined.
When a mathematician says ``$S$ is non-empty'', they typically don't
actually mean ``\dots and here is an element of $S$ to prove it''.
Instead, they literally mean ``it is \emph{not the case} that $S$ is
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
then has to manufacture a bunch of elements out of thin air.  In the
context of constructive logic, this is deeply impossible: it turns out
that the axiom of choice implies the law of excluded middle
\citep{diaconescu1975axiom, goodman1978choice}, \citep[Theorem
10.1.14]{hottbook}!  Working as we are in a type theory based on
intuitionistic logic, we must therefore reject the axiom of choice.

\begin{rem}
  It is worth noting that within HoTT, the notion of a ``non-empty''
  set can be defined in a more nuanced way.  The best way to model
  what classical mathematicians mean when they say ``$S$ is
  non-empty'' is probably not with a negation, but instead with the
  \emph{propositional truncation} of the statement that $S$ contains
  an element~\citep[Chapter 3]{hottbook}.  This more faithfully
  mirrors the way mathematicians use it, for example, in reasoning
  such as ``$S$ is non-empty, so let $s \in S$ \dots''.  Non-emptiness
  does in fact imply an inhabitant, but such an inhabitant can only be
  used to prove propositions.
\end{rem}

Unfortunately, traditional category theory (founded in set theory)
makes frequent---though hidden---use of the axiom of choice.  The next
sections explain the places where it occurs and some approaches to
doing without it.

\subsection{Unique isomorphism and generalized ``the''}
\label{sec:generalized-the}

\later{Make the link between ``the'' and ``definite description'' (aka $\iota$,
as well as Hilbert's choice operator, $\epsilon$).}

In category theory, one is typically interested in specifying objects
only \emph{up to (unique) isomorphism}.  In fact, definitions which
make use of actual \emph{equality} on objects are sometimes referred
to (half-jokingly) as \emph{evil}.  More positively, the
\term{principle of equivalence} states that properties of mathematical
structures should be invariant under isomorphism.  This principle
leads naturally to speaking of ``the'' object having some property,
when in fact there may be many objects with the given property but
all such objects are uniquely isomorphic; this cannot cause confusion
if the principle of equivalence is in effect.

Beneath this seemingly innocuous use of ``the'' (often referred to as
\term{generalized ``the''}), however, lurks the axiom of choice!  In
particular, one often wishes to define functors whose action on
objects is defined only up to unique isomorphism, with no way to make
a canonical choice of output object.  In order to define such a
functor one must resort to the axiom of choice to arbitrarily choose
particular outputs.  This seems like a fairly ``benign'' use of AC: if
we have a collection of equivalence classes, where the elements in
each class are all uniquely isomorphic, then using AC to pick one
representative from each really ``does not matter'' in the sense that
we cannot tell the difference between different choices (as long as we
refrain from evil).  Unfortunately, even such ``benign'' use of AC
still poses a problem for computation.

\subsection{AC and equivalence of categories}
\label{sec:AC-equivalence}

As hinted in \pref{sec:ct-fundamentals}, a particular example of the
need for AC relates to equivalence of categories.  The underlying
issue is exactly that described in the previous section: namely, the
need for functors defined only up to unique isomorphism.

Recall, from \pref{sec:ct-fundamentals}, the definition of equivalence
of categories:
\begin{repdefn}{defn:cat-equiv}
  An \term{equivalence} between $\C$
  and $\D$ is given by functors $\BackForth \C F G \D$ which are
  inverse up to natural isomorphism, that is, $1_\C \iso GF$ and $FG
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
  and now it should be clear why: there is no need for a distinct term
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

\begin{rem}
  It should be noted that without AC, protoequivalence is actually not
  even an equivalence relation on categories. To fix this, one must
  pass to the notion of a \term{weak equivalence} of categories, which
  consists of a \emph{span} of protoequivalences
  \citep{nlab-weak-equiv}.
\end{rem}

So AC is required to prove that every protoequivalence is an
equivalence.  In fact, the association goes deeper yet: it turns out
that the statement
\begin{equation}
  \text{every protoequivalence is an equivalence} \tag{AP} \label{eq:AP-eqv}
\end{equation}
(let's call this the ``Axiom of Protoequivalence'', or AP) not only
requires AC, but is \emph{equivalent} to it, in the sense that AC is
derivable given AP as an axiom \citep{nlab-AoC}!

On purely intuitive grounds, however, it still feels like AP
ought to be true.  The particular choice of functor $G : \D \to
\C$ doesn't matter, since it makes no difference up to
isomorphism.  One is therefore left in the awkward position of having
two logically equivalent statements which it seems ought to be
respectively affirmed and rejected.

Obviously this is not a tenable state of affairs; there are (at least)
four options for resolving the situation.

\begin{enumerate}
\item If one is feeling particularly rational, one can simply say,
  ``Since AC and AP are equivalent and I reject AC, I must therefore
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
  \term{anafunctor}~\citep{makkai1996avoiding}.  Essentially, an
  anafunctor is a functor ``defined only up to unique isomorphism''.
  It turns out that the appropriate analogue of AP, where ``functor''
  has been replaced by ``anafunctor'', is indeed true---and neither
  requires nor implies AC.  Anafunctors act like functors in a
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
  \C$ to choose from, with no canonical choice, and it is annoying
  (again, a philosophical rather than technical consideration!) to be
  forced to choose one.

\item Instead of generalizing functors, a more direct solution is to
  \emph{generalize the notion of equality}.  After all, what really
  seems to be at the heart of all these problems is differing notions
  of equality (\ie equality of sets, isomorphism, equivalence \dots).
  Of course, this is precisely what is done in HoTT.\footnote{As a
    historical note, it seems that the original work on anafunctors is
    part of the same intellectual thread that led to the development
    of HoTT: see \url{http://byorgey.wordpress.com/2014/05/13/unique-isomorphism-and-generalized-the/\#comment-13123}.}  It turns out that if one builds up suitable notions of
  category theory on top of HoTT instead of set theory, then AP is
  true, without the need for AC, and even with a \emph{weaker} version
  of essential surjectivity that corresponds more closely to essential
  surjectivity in classical logic, using propositional truncation to
  encode the classical notion of existence. This is discussed in more
  detail in \pref{sec:ct-hott}.
\end{enumerate}

Ultimately, this last option using HoTT is the best.  However, to
fully appreciate it, it is helpful to first explore the notion of
anafunctors, and the closely related notion of cliques.

\subsection{Cliques}
\label{sec:cliques}

As a preface to anafunctors, we begin with a brief outline of the
theory of \term{cliques}, which are a formal way of representing the
informal notion of an ``equivalence class of uniquely isomorphic
objects''. Cliques were introduced by \citet{joyal1991geometry} for
the specialized purpose of relating strict and non-strict monoidal
categories. \citet{makkai1996avoiding} later noted that cliques
are a special case of anafunctors; the precise relationship will be
explained in \pref{sec:anafunctors}.

The theory of cliques (and of anafunctors) amounts to a way of doing
(set-theoretic) category theory without using the axiom of choice.
However, building \mbox{category} theory directly in homotopy type theory
(\pref{sec:ct-hott}), instead of set theory, also obviates the need
for the axiom of choice, but without the extra complication of
anafunctors.  This subsection and the next, therefore, are not
strictly prerequisite to the remainder of this dissertation, but they
help build intuition for the success of homotopy type theory,
explained in \pref{sec:finiteness-hott}.

\begin{defn}
  A \term{clique} $(I,A,u)$ in a category
  $\C$ is given by
  \begin{itemize}
  \item a \emph{non-empty} collection of objects $A = \{A_i \mid i \in
    I\}$, indexed by some collection $I$, and
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
  First, the same object may occur multiple times in the collection
  $A$---that is, multiple different values of $I$ may index the same
  object of $\C$.  Second, the last two conditions together imply
  $u_{ij} = u_{ji}^{-1}$, since $u_{ij} \then u_{ji} = u_{ii} = id$.
\end{rem}

A clique can thus be visualized as a graph-theoretic clique in a
directed graph, with a unique morphism between any two objects: \[
\xymatrix{ A_1 \ar@@<.2em>[d] \ar@@<.4em>[r] \ar@@<.2em>[dr]
  & A_2 \ar[l] \ar@@<.2em>[d] \ar@@<.2em>[dl] \\
  A_3 \ar@@<.2em>[u] \ar[r] \ar@@<.2em>[ur] & A_4 \ar@@<.4em>[l]
  \ar@@<.2em>[u] \ar@@<.2em>[ul] }
\]

Equivalently, a clique may be visualized as a clique in an
\emph{undirected} graph, with each edge representing an isomorphism.
That is, a clique represents a collection of objects in $\C$ which are
all isomorphic, with a single chosen isomorphism between each pair of
objects.

\begin{defn}
  A \term{morphism} between two cliques $(I,A,u)$ and $(J,B,v)$ is
  given by a collection of arrows \[ \{ \xymatrix{A_i \ar[r]^{f_{ij}}
    & B_j} \mid i \in I, j \in J \} \] such that \[ \xymatrix{ A_i
    \ar[r]^{f_{ij}} \ar[d]_{u_{ik}} & B_j \ar[d]^{v_{jl}} \\ A_{k}
    \ar[r]_{f_{kl}} & B_{l}} \] commutes for all $i,k \in I$ and $j,l
  \in J$. In other words, a morphism of cliques maps an entire class
  of isomorphic objects to another class---in particular, mapping each
  representative of the first class to each representative of the
  second---in a way that preserves the isomorphisms.
\end{defn}

As one would expect, the class of cliques and clique morphisms in a
category $\C$ itself forms a category, which we call $\clq \C$.  It is
easy to imagine what the identity morphism of cliques must be---the
one that maps each $A_i$ to $A_j$ via $u_{ij}$.  However, composition
of clique morphisms is more subtle.  Suppose we have three cliques
with morphisms $\xymatrix{(I,A,u) \ar[r]^f & (J,B,v) \ar[r]^g &
  (K,C,w)}$.  We must define a collection of morphisms
$\xymatrix{A_i \ar[r]^{h_{ik}} & C_k}$.  For any given $A_i$ and
$C_k$, we have morphisms from $A_i$ to each of the $B_j$, and from
each of the $B_j$ to $C_k$, with a representative example shown below.
\[ \xymatrixrowsep{1pc}
  \xymatrix{
    & B_1 \ar@@<.2em>[dd] \ar@@<.4em>[r] \ar[drr] \ar@@<.2em>[ddr]
    & B_2 \ar[l] \ar@@<.2em>[dd] \ar[dr]^{g_{2k}} \ar@@<.2em>[ddl] \\
  A_i \ar[ur]^{f_{i1}} \ar[dr]_{f_{i3}} \ar[urr] \ar[drr] &     &     & C_k \\
    & B_3 \ar@@<.2em>[uu] \ar@@<-.4em>[r] \ar[urr] \ar@@<.2em>[uur]
    & B_4 \ar[l] \ar@@<.2em>[uu] \ar[ur]_{g_{4k}} \ar@@<.2em>[uul]
  }
\]
If we pick a fixed $j \in J$, for each $i \in I$ and $k \in K$ we can define $h_{ik} = f_{ij} \then
g_{jk}$.  Moreover, the resulting $h_{ik}$ are independent of the
choice of $j$, since everything in sight commutes.  Specifically,
\begin{sproof}
\stmt{f_{ij} \then g_{jk}}
\reason{=}{$v_{jl} \then v_{lj} = v_{jj} = \id$}
\stmt{f_{ij} \then v_{jl} \then v_{lj} \then g_{jk}}
\reason{=}{$f$, $g$ are clique morphisms}
\stmt{u_{ii} \then f_{il} \then g_{lk} \then w_{kk}}
\reason{=}{$u_{ii} = \id$; $w_{kk} = \id$}
\stmt{f_{il} \then g_{lk}.}
\end{sproof}
Since $J$ is non-empty, it must contain some element $j$ which we may
arbitrarily use to define the $h_{ik}$.
\begin{rem}
  If defining the theory of cliques within HoTT instead of set theory,
  this can be done in an even more principled way: the fact that $J$
  is non-empty should be modeled by its propositional truncation,
  $\ptrunc J$. This means that \emph{in order} to be able to use the
  particular value of $J$ hidden inside the truncation, we \emph{must}
  show that the $h_{ik}$ thus defined are independent of the choice of
  $j$.
\end{rem}
The idea now is to replace functors $\C \to \D$ with functors $\C \to
\clq \D$, which map objects of $\C$ to entire equivalence classes of
objects in $\D$, instead of arbitrarily picking some object from each
equivalence class. \later{example?}  This gets rid of the need for AC
in defining such functors.  However, it is somewhat cumbersome to
replace $\D$ by $\clq \D$ in this way.  To make it tenable, one could
imagine defining a new notion of ``clique functor'' $F : \C
\stackrel{\clq{}}{\to} \D$ given by a regular functor $\C \to \clq
\D$, and showing that these clique functors act like functors in
suitable ways.  For example, it is easy to see that any regular
functor $\C \to \D$ can be made into a trivial functor $\C \to \clq
\D$, by sending each $C \in \C$ to the singleton clique containing
only $F(C)$.  One can also show that clique functors can be composed,
have a suitable notion of natural transformations between them, and so
on\footnote{In fact, $\clq{-}$ turns out to be a (2-)monad, and the
  category of clique functors is its Kleisli category
  \citep{nlab-clique}.}. In fact, it turns out that this is precisely
the theory of \emph{anafunctors}.

\subsection{Anafunctors}
\label{sec:anafunctors}

As an intuition for anafunctors it is helpful to keep in mind the
equivalent concept of functors $\C \to \clq \D$---both represent
functors whose values are specified only up to unique isomorphsim.
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
    [connectOutside' (with & arrowHead .~ noHead) a b || (a,b) <- rel]

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

\begin{defn}[\citet{makkai1996avoiding}] \label{defn:anafunctor}
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
  $F$ acts like a regular functor $\C \to \D$.
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
  between $F_s(C)$ and $F_t(C)$.
\end{rem}

\begin{rem}
  It is not hard to show that cliques in $\D$ are precisely
  anafunctors from $\cat{1}$ to $\D$.  In fact, more is true: the
  class of functors $\C \to \clq \D$ is naturally isomorphic to the
  class of anafunctors $\C \to \D$ (for the proof, see
  \citet[pp. 31--34]{makkai1996avoiding}).
\end{rem}

There is an alternative, equivalent definition of anafunctors, which
is somewhat less intuitive but usually more convenient to work with.

\begin{defn} \label{defn:anafunctor-span} An anafunctor $F : \C \to
  \D$ is a category $\Spec$ together with a span of \emph{functors}
  $\Span \C {\lana{F}} {\Spec} {\rana{F}} \D$ where $\lana{F}$ is
  fully faithful and (strictly) surjective on objects.
\end{defn}

\begin{rem}
  In this definition, $\lana{F}$ must be \emph{strictly}
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
to a zig-zag path \[ \xymatrix@@dr{ & t \ar[d] \ar[r] & E \\ s \ar[d]
  \ar[r] & D \\ C } \]  In
order to \emph{specify} such a path it suffices to give the pair
$(s,t)$, which determines $C$, $D$, and $E$.  Note, however, that not
every pair in $S \times T$ corresponds to a valid path, but only those
which agree on the middle object $D \in \D$.  Thus, we
may take $\{ (s,t) \mid s \in S, t \in T, \rana{F}(s) = \lana{G}(t)
\}$ as the set of specifications for the composite $F \then G$, with
$\lana{F \then G}(s,t) = \lana{F}(s)$ and $\rana{F \then G}(s,t) =
\rana{G}(t)$. On morphisms, $(F \then G)_{(s,t),(u,v)}(f) =
G_{t,v}(F_{s,u}(f))$.  One can check that this satisfies the
anafunctor laws.

The same thing can also be defined at a higher level in terms of
spans: \[ \xymatrix@@dr{ \Spec \times_\D \bbb{T} \ar[d]_{\lana F'}
  \ar[r]^{\rana G'} & \bbb{T} \ar[d]_{\lana G} \ar[r]^{\rana G} & \E
  \\ \Spec \ar[d]_{\lana F} \ar[r]^{\rana F} & \D \\ \C } \] $\Cat$ is
complete, and in particular has pullbacks, so we may construct a new
anafunctor from $\C$ to $\E$ by taking a pullback of $\rana F$ and
$\lana G$ and then composing appropriately, as illustrated in the
diagram.

One can go on to define ananatural transformations between
anafunctors, and show that together these constitute a $2$-category
$\mathbf{AnaCat}$ which is analogous to the usual $2$-category of
(small) categories, functors, and natural transformations; in
particular, there is a fully faithful embedding of $\mathbf{Cat}$ into
$\mathbf{AnaCat}$, which moreover is an equivalence if AC holds.  See
\citet{makkai1996avoiding} for details.

To work in category theory based on set theory and classical logic,
while avoiding AC, one is therefore justified in ``mixing and
matching'' functors and anafunctors as convenient, but discussing them
all as if they were regular functors (except when \mbox{defining} a
particular anafunctor).  Such usage can be formalized by turning
everything into an anafunctor, and translating functor operations and
properties into corresponding operations and properties of
anafunctors.  However, this is tediously complex (imagine if an
introductory category theory textbook followed up the definition of
categories with the definition of anafunctors!) and, as we will see,
ultimately unnecessary. By founding category theory on
HoTT instead of set theory, we can avoid the axiom of choice without
incurring such complexity overhead.  In a sense, HoTT takes all the
added complexity of anafunctors and moves it into the background
theory, so that ``normal'' functors secrectly become anafunctors.

\section{Category theory in HoTT}
\label{sec:ct-hott}

Category theory works much better when founded in HoTT instead of set
theory.  Primarily, this is because in set theory the only
notion of equality (extensional equality of sets) is too
impoverished---one really wants to work up to \emph{isomorphism}
rather than literal equality, and the mismatch between isomorphism and
strict equality introduces all sorts of difficulties and extra work.
For example, many concepts have subtly different ``strict'' and/or
``weak'' variants, having to do with the sort of equality used in the
definition.  In contrast, via the univalence axiom, HoTT has a very
rich---yet coherent---notion of equality that is able to encompass
isomorphism in categories.

This section lays out a few relevant definitions along with some
intuition and commentary.  A fuller treatment may be found in Chapter
9 of the HoTT book~\citeyearpar{hottbook}.  Generally, the term
``\hott{widget}'' is used to refer to widgets as defined in HoTT, to
distinguish from widgets as defined in set theory.  There is
nothing fundamentally new in this section, but it is valuable to
collect and synthesize the particularly relevant bits of information
which are otherwise scattered throughout the HoTT book.

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
  and extra laws become necessary.  Down this path lie $n$-categories
  or even $(\infty,1)$-categories; but to model traditional
  ($1$-)categories, it suffices for $\hom X Y$ to be a $0$-type.  In
  particular, this means that the identity and associativity laws,
  being equalities between elements of a $0$-type, are themselves
  $(-1)$-types, \ie mere propositions.
\end{rem}

One might wonder why the term \term{precategory} is used for something
that seems to be a direct port of the definition of a category from
set theory into HoTT.  The reason is that the usual formal definition
of categories as expressed in set theory is incomplete:
categories in fact come equipped with an extra \emph{social} convention
regarding their use---namely, ``don't be evil'', \ie don't violate the
principle of equivalence.  In HoTT, we can formally encode this social
convention as an axiom, which makes categories much nicer to work with
in practice (after all, the social convention is not arbitrary, but
encodes what category theorists have found to be a particularly nice
way to do category theory).

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
automatic; in particular, it does not follow from univalence, due to
the distinction between $X \iso Y$ and $X \equiv Y$. However,
requiring the other direction as an axiom is what allows us to
formalize the principle of equivalence: isomorphic objects in a
category should be truly interchangeable.

\begin{defn}
  An \term{\hott{category}} is a precategory $\CT$ together with the
  additional univalence-like axiom that for all $X,Y : \CT$, \[ (X \iso
  Y) \equiv (X = Y). \] We write $\isotoid : (X \iso Y) \to (X = Y)$
  for the left-to-right direction of the equivalence.
\end{defn}

An \hott{groupoid} is an \hott{category} where every morphism is an
isomorphism. The following example will play an important role later.

\begin{defn}
  Any $1$-type $T$ gives rise to an \hott{groupoid} $\tygrpd{T}$ where
  the objects are values $a : T$ and morphisms are equalities $\hom a
  b \hdefeq (a = b)$, that is, morphisms from $a$ to $b$ are paths $p
  : a = b$.
\end{defn}

\begin{proof}
  The fact that $T$ is a $1$-type means that $\hom a b$ is a $0$-type
  for $a, b : T$, as required.  Identity morphisms, composition, the
  identity laws, associativity, and the fact that every morphism is an
  isomorphism all follow directly from properties of propositional
  equality.  Since isomorphisms are already paths, $\isotoid$ is just
  the identity.
\end{proof}

Another important example of an \hott{category} is an analogue to the
usual category \Set of sets and functions.

\begin{defn}[HoTT book, 9.1.5, 9.1.7]
  $\ST$ denotes the \hott{category} of sets, that is, the category
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
  \equiv (f : A \to B) \times \qinv(f)$, where $\qinv(f) \hdefeq (g : B
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
  An \hott{natural transformation} $\gamma$ between \hott{functors} $F,G :
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

It may not be readily apparent from the definitions, but as claimed
earlier, this turns out to be a much nicer framework in which to carry
out category theory.  An extended example is given in
\pref{sec:finiteness-hott}.  For now we describe two smaller (but
also relevant) examples.

\subsection{Monoidal categories in HoTT}
\label{sec:monoidal-cats-hott}

The first example is the theory of \term{monoidal categories}.  Recall
that a monoidal category $\C$ is one with a bifunctor $\otimes : \C^2
\to \C$, an identity object $1 \in \C$, and natural isomorphisms
$\alpha$, $\lambda$, and $\rho$ expressing the associativity and
identity laws (along with some extra coherence laws).  In set theory,
there is also a notion of a \term{strict} monoidal category, where
associativity and the identity laws hold up to \emph{equality} rather
than just isomorphism.  In HoTT-based category theory, however,
functors between \hott{categories}---as opposed to precategories---are
naturally isomorphic if and only if they are equal (HoTT book, Theorem
9.2.5).  Thus, there is no difference between strict and
non-strict monoidal \hott{categories}.

\subsection{Coends in HoTT}
\label{sec:coends-hott}

The second example is the notion of a \term{coend}.  Recall that a coend over
a functor $T : \C^\op \times \C \to \D$ is an object of $\D$, denoted
$\coend C T(C,C)$, together with a family of morphisms $\omega_X :
T(X,X) \to
\coend C T(C,C)$ for each $X \in \C$, such that
\begin{equation} \label{eq:coend-diagram}
  \xymatrix@@dr{ T(X',X) \ar[r]^{T(1,f)} \ar[d]_{T(f,1)} & T(X',X') \ar[d]^{\omega_{X'}} \\
  T(X,X) \ar[r]_{\omega_X} & \coend C T(C,C) }
\end{equation} commutes for all $X,
X' : \C$ and $f : X \to X'$.  In set theory, recall that $\biguplus_C
T(C,C)$, together with the obvious family of injections $\omega_C\ t =
(C,t)$, comes close to being the right implementation of $\coend C
T(C,C)$, but fails to satisfy \eqref{eq:coend-diagram}: in particular,
the outputs of $\omega_X$ and $\omega_{X'}$ are never equal when $X
\neq X'$, precisely because $\uplus_C$ denotes a \emph{disjoint}
union.  Instead, we must quotient this disjoint union by the
equivalence relation induced by \eqref{eq:coend-diagram}.

\newcommand{\llangle}{\langle\!\langle}
\newcommand{\rrangle}{\rangle\!\rangle}
\newcommand{\hcoendI}[2]{\llangle #1 , #2 \rrangle}

In HoTT, given some categories $\CT$ and $\DT$ and a functor $T :
\CT^\op \times \CT \to \DT$, we can directly encode this quotient as a
higher inductive type $\exists T$.  We first introduce a data
constructor \[ \hcoendI{-}{-} : (X : \CT) \to T(X,X) \to \exists T. \]
So far this is equivalent to the $\Sigma$-type $\sum_C T(C,C)$, which
corresponds to the disjoint union $\biguplus_C T(C,C)$.  However, we
also introduce a path constructor with type \[ (X,X' : \CT) \to (t :
T(X',X)) \to (f : \hom X {X'}) \to \hcoendI X {T(f,1)\ t} =
\hcoendI{X'}{T(1,f)\ t} \] which ensures that the commutative diagram
\eqref{eq:coend-diagram} is satisfied.

It is already convenient to be able to work directly with a data type
representing a coend.  The special case where $\CT$ is a groupoid is
even more convenient.  In a groupoid, any morphism $f :
\hom X X'$ is automatically an isomorphism, $f : X \iso X'$, and hence
there is a path $\isotoid\ f : X = X'$.  Moreover, one can show that
\[ (\isotoid\ f)_*(T(f,1)\ t) = T(1,f)\ t \] ($(\isotoid\ f)_*$
applies $f$ covariantly and $f^{-1}$ contravariantly), and therefore
the above path constructor comes for free!  In other words, when $\CT$
is a groupoid and $T : \CT^\op \times \CT \to \DT$, the coend type
$\exists T$ defined above is equivalent to the simple $\Sigma$-type
$\sum_C T(C,C)$---that is, the extra higher path constructor is
entirely redundant. The equalities which were missing in set theory
are supplied automatically by HoTT's richer system of equality.

\section{Finiteness in set theory}
\label{sec:finiteness-sets}

Finally, we can assemble the foregoing material on anafunctors and
category theory in HoTT into a coherent story about \term{finiteness},
first using set-theoretic foundations, and then using HoTT.  The material
in this section and the next (other than the lemmas and theorems cited
from the HoTT book) is novel.

Recall that $\B$ denotes the groupoid of finite sets and bijections,
and $\P$ the groupoid of natural numbers and permutations.  In
classical category theory, $\P$ is a \term{skeleton} of
$\B$---roughly, we may think of it as the result of replacing each
equivalence class of isomorphic objects in $\B$ with a single object.
In this case, we identify each equivalence class of isomorphic finite
sets with a natural number \emph{size}---size being the one property
of sets which is invariant under isomorphism.  The relationship
between $\B$ and $\P$ is central to the concept of finiteness: passing
from $\B$ to $\P$ corresponds to taking the \emph{size} of finite
sets, and passing from $\P$ to $\B$ corresponds to constructing
canonical finite sets of a given size.  The study of $\B$ and $\P$ is
also critical for the theory of species; as we will shortly see in
\pref{chap:species}, traditional species are defined as functors $\B
\to \Set$.

It is a simple result in classical category theory that every category
is equivalent to its skeletons.  This equivalence allows one to pass
freely back and forth between functors $\B \to \Set$ and functors $\P
\to \Set$, and this is often implicitly exploited in the literature on
species.  However, we are interested in the \emph{computational}
content of this equivalence, and it is here that we run into trouble.
After the foregoing discussion of cliques and anafunctors, the idea of
quotienting out by equivalence classes of isomorphic objects ought to
make us squeamish---and, indeed, the proof that $\B$ and $\P$ are
equivalent requires AC.

In more detail, it is easy to define a functor $\fin - : \P \to \B$
which sends the natural number $n$ to the finite set $\fin n$ and
preserves morphisms; defining an inverse functor $\size - : \B \to
\P$, however, is more problematic. We can send each set $S$ to its
size $\size S$, but we must send each bijection $S \bij T$ to a
permutation $\fin{\size S} \bij \fin{\size T}$, and there is no
obvious way to pick one.  For example, suppose $S = \{\text{cat},
\text{dog}, \text{moose}\}$ and $T = \{
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
it must be sent to a permutation on $\{0,1,2\}$---but to which
permutation should it be sent?  Knowing that the size of
$\{\text{cat}, \text{dog}, \text{moose}\}$ is $3$ does not tell us
anything about how to match up animals with $\{0,1,2\}$.

Abstractly, $\fin - : \P \to \B$ is fully faithful and essentially
surjective (every finite set is in bijection with $\fin n$ for some
$n$); this yields an equivalence of categories, and hence an inverse
functor $\size - : \B \to \P$, only in the presence of AC.  More
concretely, we can use AC to choose an arbitrary bijection $\varphi_S
: S \bij \fin{\size S}$ for each finite set $S$, somehow matching up
$S$ with the canonical set of size $\size S$. Given $\alpha : S \bij
T$ we can then construct \[ \xymatrix{ \fin{\size S}
  \ar[r]^-{\varphi_S^{-1}} & S \ar[r]^\alpha & T \ar[r]^-{\varphi_T} &
  \fin{\size T}}. \] This use of AC is ``benign'' in the sense that
all choices yield equivalent functors; this construction using AC thus
in some sense yields a well-defined functor but has no computational
interpretation.

We can avoid the use of AC by constructing an \emph{anafunctor} $\size
- : \B \to \P$ instead of a functor.  In particular, as the class of
specifications $S_{\size{}}$, we choose the class of sets paired with
bijections to canonical finite sets of the appropriate size, \[
\sum_{T \in \B} (T \bij \fin{\size T}). \] The function $\lana
{\size{}} : S_{\size{}} \to \Ob \B$ simply forgets the chosen
bijection, that is, $\lana{\size{}}\ (T,\varphi) = T$, and
$\rana{\size{}} : S_{\size{}} \to \Ob \P$ sends finite sets to their
size, $\rana{\size{}}\ (T,\varphi) = \size T$.  Note that both
$\lana{\size{}}$ and $\rana{\size{}}$ ignore $\varphi$, which is
instead needed to define the action of $\size{}$ on morphisms.  In
particular, given $\alpha : S \bij T$ in $\B$, we define
$\sizesymb_{(S,\varphi_S), (T,\varphi_T)}(\alpha) = \varphi_S^{-1}
\then \alpha \then \varphi_T$, which can be visualized as
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

As a side note, it is worth mentioning an alternate way around the use
of AC in this particular case, using the theory of \term{hereditarily
  finite} sets.
\begin{defn}
  A \term{hereditarily finite} set is a finite set, all of whose
  elements are hereditarily finite.
\end{defn}
This definition gets off the ground since the empty set is vacuously
hereditarily finite.  As is usual in set theory, this definition is
interpreted inductively, so there cannot be any infinitely descending
membership chains.  Hereditarily finite sets are thus identified with
finitely-branching, finite-depth trees (with no inherent order given
to sibling nodes).

Now consider the groupoid $\cat{H}$ obtained by replacing ``finite''
with ``hereditarily finite'' in the definition of $\B$.  That is, the
elements of $\cat{H}$ are hereditarily finite sets, and the morphisms
are bijections.  This is no great loss, since given some finite set we
are not particularly interested in the intensional properties of its
elements, but only in its extensional properties (how many elements it
has, which elements are equal to other elements, and so on).

Unlike the class of all sets, however, the class of all hereditarily
finite sets (normally written $V_\omega$) has a well-ordering.  For
example, we can compare two hereditarily finite sets by first
inductively sorting their elements, and then performing a
lexicographic comparison between the two ordered sequences of
elements.  This means that every hereditarily finite set has an
induced ordering on its elements, since the elements are themselves
hereditarily finite. In other words, picking a well-ordering of
$V_\omega$ is like making a ``global'' choice of orderings, assigning
a canonical bijection $S \bij \fin{\size S}$ for every hereditarily
finite set $S$.

However, this construction is somewhat arbitrary, and has no natural
counterpart in type theory, or indeed in a structural set theory.  The
concept of hereditary finiteness only makes sense in a material set
theory such as ZF.  To determine the canonical ordering on, say,
$\{\text{dog}, \text{cat}, \text{moose}\}$, we need to know the
precise identity of the set used to encode each animal---but knowing
their precise encoding as sets violates the principle of equivalence,
since there may be many possible encodings with the right properties.

\section{Finiteness in HoTT}
\label{sec:finiteness-hott}

We now turn to developing counterparts to the groupoids $\P$ and $\B$
in type theory.  \pref{sec:finiteness-prelims} presents some necessary
lemmas and defines $\PT$ as a type-theoretic analogue to
$\P$. \pref{sec:cardinal-finiteness} then presents the theory of
cardinal-finiteness in HoTT and uses it to define $\BT$, a
type-theoretic analogue to $\B$. This leads to an interesting tangent
exploring ``manifestly finite'' sets and their relation to linear
orders in \pref{sec:manifestly-finite}; finally, \pref{sec:P-B-equiv}
ties things together by considering the equivalence of $\PT$ and
$\BT$, in particular showing how using HoTT as a foundation allows us
to avoid the axiom of choice.

\subsection{Preliminaries}
\label{sec:finiteness-prelims}

\begin{lem} \label{lem:equiv-pres-set}
  Equivalence preserves set-ness, that is, if $A$ and
  $B$ are sets, then so is $A \equiv B$.
\end{lem}
\begin{proof}
  $(A \equiv B) \equiv ((f : A \to B) \times \cons{isequiv}(f))$, where
  $\cons{isequiv}(f)$ is a mere proposition expressing the fact that
  $f$ is an equivalence (\ie has a suitable inverse).  This is a set
  since $\cons{isequiv}(f)$ is a mere proposition (and hence a set),
  $A \to B$ is a set whenever $B$ is, and $\times$ takes sets to sets
  [HoTT book, Lemma 3.3.4, Examples 3.1.5 and 3.1.6].
\end{proof}

\begin{cor} \label{cor:path-pres-set}
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
  \item In the case when both are a successor, we have $\Fin{(\suc\
      n_1')} \equiv \Fin{(\suc\ n_2')}$, which is equivalent to $\top
    + \Fin{n_1'} \equiv \top + \Fin{n_2'}$.  If we can conclude that
    $\Fin{n_1'} \equiv \Fin{n_2'}$, the inductive hypothesis then
    yields $n_1' = n_2'$, from which $\suc\ n_1' = \suc\ n_2'$ follows
    immediately.  The implication $(\top + \Fin{n_1'} \equiv \top +
    \Fin{n_2'}) \to (\Fin{n_1'} \equiv \Fin{n_2'})$ is true, but not
    quite as straightforward to show as one might think! In
    particular, an equivalence $(\top + \Fin{n_1'} \equiv \top +
    \Fin{n_2'})$ may not match the $\top$ values with each other.  As
    illustrated in \pref{fig:gcbp-Maybe}, given $e : (\top +
    \Fin{n_1'} \equiv \top + \Fin{n_2'})$, it suffices to define
    $e'(e^{-1}\ \unit) = e\ \unit$, with the rest of $e' : \Fin{n_1'}
    \equiv \Fin{n_2'}$ defined as a restriction of $e$. \later{Formal
      proof that the resulting $e'$ is an equivalence?}  This
    construction corresponds more generally to the \term{Gordon
      complementary bijection principle}~\citep{gordon1983sieve},
    whereby a bijection $A_1 \bij B_1$ can be constructively
    ``subtracted'' from a bijection $(A_0 + A_1) \bij (B_0 + B_1)$,
    yielding a bijection $A_0 \bij B_0$.  (Unfortunately, I do not
    currently know of a good way to encode a proof of the fully
    general bijection principle in a constructive logic.)
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

\begin{rem}
  It seems somewhat strange that the above proof has so much
  computational content---the required manipulations of equivalences
  are quite nontrivial---when the end goal is to prove a mere
  proposition.  I do not know whether there is a simpler proof.
\end{rem}

Constructing a type-theoretic counterpart to $\P$ is
now straightforward.
\begin{defn}
  $\PT$ is the \hott{groupoid} where
  \begin{itemize}
  \item the objects are values of type $\N$, and
  \item the morphisms $\hom m n$ are equivalences of type $\Fin m \equiv
    \Fin n$.
  \end{itemize}
\end{defn}
It is easy to check that this satisfies the axioms for an
\hott{category}, the salient points being that $\Fin m \equiv \Fin n$ is
a set by \pref{lem:equiv-pres-set} and that $\isotoid$ follows from
\pref{lem:fin-iso-equal}.

\subsection{Cardinal-finiteness}
\label{sec:cardinal-finiteness}

Developing a counterpart to $\B$ is more subtle.  The first order of
business is to decide how to port the concept of a ``finite set''.
Generally, ``a set with property X'' ports to type theory as ``a type
paired with constructive evidence of property X'' (or perhaps ``a
$0$-type paired with evidence of X'', depending how seriously we want
to take the word \emph{set}); so what is constructive evidence of
finiteness? This is not \latin{a priori} clear, and indeed, there are
several possible answers \citep{finite}. However, the discussion of
\pref{sec:finiteness-sets}, where bijections $S \bij \fin{\size S}$
played a prominent role, suggests that we adopt the simplest option,
\term{cardinal-finiteness}.
\begin{defn}
  A set $A$ is \term{cardinal-finite} iff there exists some $n \in \N$
  and a bijection $A \bij \fin n$; $n$ is called the size or
  cardinality of $A$.
\end{defn}
Our first try at encoding this in type theory is
\[ \FinType \hdefeq (A : \Type) \times (n : \N) \times (A \equiv \Fin n). \]

We would like to build a groupoid having such finite types as objects,
and equivalences between them as morphisms.  Recall that, given some
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

The situation can be pictured as shown in \pref{fig:fin-equiv}. The
elements of types $A_1$ and $A_2$ are shown on the sides; the evidence
of their finiteness is represented by bijections between their
elements and the elements of $\Fin n$, shown along the bottom.  The
catch is that the diagram necessarily contains only triangles:
corresponding elements of $A_1$ and $A_2$ must correspond to the same
element of $\Fin n$ on the bottom row.  Therefore, there are only two
degrees of freedom. Once the evidence of finiteness is determined for
$A_1$ and $A_2$, there is only one valid correspondence between
them---but there ought to be $n!$ such correspondences.
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

\begin{prop} \label{prop:U-fin-set}
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
\fin n$, but merely that $A$ \emph{can be} put in bijection with $\fin
n$, with no mention of a specific bijection.  This is justified by the
fact that, up to isomorphism, any bijection $A \bij \fin n$ is just as
good as any other.

This suggests a better encoding of finiteness in type theory.
\begin{defn} \label{defn:FinSetT}
  The type of finite sets is given by \[ \FinSetT \hdefeq (A : \Type)
  \times \isFinite(A), \] where \[ \isFinite(A)
  \hdefeq \ptrunc{(n : \N) \times (A \equiv \Fin n)}. \]
\end{defn}
Here we make use of propositional truncation to encode the fact that
there \emph{merely exists} some size $n$ and an equivalence between
$A$ and $\Fin n$, but without exposing a precise choice.  The
finiteness evidence is now irrelevant to paths in $\FinTypeT$, since
there is always a path between any two elements of a truncated type.

In an abuse of notation, we will often write $A : \FinSetT$ instead of
$(A,f) : \FinSetT$ where $f : \isFinite(A)$. We first record a few
properties of $\FinSetT$.

\begin{prop}
  $\FinSetT$ is a $1$-type.
\end{prop}
\begin{proof}
  We first show that if $(A,f) : \FinSetT$, then $A$ is a
  set. Being a set is a mere proposition, so we may use the
  equivalence $A \equiv \Fin n$ hidden inside $f$.  But $\Fin n$ is a
  set, and equivalence preserves set-ness (\pref{lem:equiv-pres-set}),
  so $A$ is a set as well.

  Finally, since $\isFinite(A)$ is a mere proposition, paths between
  $\FinSetT$ values are characterized by paths between their
  underlying types. Since those types must be sets, \ie $0$-types,
  $\FinSetT$ is consequently a $1$-type.
\end{proof}

\begin{prop} \label{prop:size-not-trunc}
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
  truncation, which is a mere proposition by construction.

  In the other direction, define \[ g(\ptruncI{(n, e)}) = (n,\ptruncI
  e), \] which is clearly inverse to $f$.  It remains only to show
  that the implicit use of recursion for propositional truncation is
  justified, \ie that $(n : \N) \times \ptrunc{A
    \equiv \Fin n}$ is a mere proposition.

  We must show that any two values $(n_1, e_1), (n_2, e_2) : (n : \N)
  \times \ptrunc{A \equiv \Fin n}$ are propositionally equal.  Since
  $e_1$ and $e_2$ are mere propositions, it suffices to show that $n_1
  = n_2$.  This equality is itself a mere proposition (since $\N$ is a
  set; see \pref{sec:n-types}), so we may apply the recursion
  principle for propositional truncation to $e_1$ and $e_2$, giving us
  equivalences $A \equiv \Fin n_1$ and $A \equiv \Fin n_2$ to work
  with.  By symmetry and transitivity of equivalences, $\Fin n_1
  \equiv \Fin n_2$, and thus $n_1 = n_2$ by \pref{lem:fin-iso-equal}.
\end{proof}

Although it is not possible to explicitly extract the equivalence with
$\Fin n$ from a finite set, it can still be implicitly used for
certain purposes, such as deciding the equality of any two elements.
\begin{prop}
  If $(A,f) : \FinSetT$, then $A$ has decidable equality.
\end{prop}
\begin{proof}
Let $x,y : A$; we must show $(x=y) + \lnot (x=y)$.  We first show that
$(x=y) + \lnot (x=y)$ is a mere proposition, and then show how to use
the equivalence $A \equiv \Fin n$ contained in $f$ to construct the
desired value.

Since $A$ is a set, $x=y$ is a mere proposition; $\lnot (x=y)$ is also
a mere proposition since $\lnot Q$ is always a mere proposition for
any $Q$.  Now let $p,q : (x=y) + \lnot (x=y)$, and consider a case
analysis on $p$ and $q$.  If one is $\inl$ and the other $\inr$, then
we can derive $\bot$, and hence $p=q$ since anything follows.  If both
are $\inl$ or both $\inr$, then $p = q$ again, since $x=y$ and $\lnot
(x=y)$ are both mere propositions.  We therefore conclude that $(x=y)
+ \lnot(x=y)$ is itself a mere proposition.

Since we are constructing a mere proposition, we may make use of the
equivalence $A \equiv \Fin n$ contained in $f$.  In particular, $\Fin
n$ has decidable equality, which we may transport along the
equivalence (using univalence for convenience, although its use here
is not strictly necessary) to obtain decidable equality for $A$.  That
is, computationally speaking, given $x,y : A$, one may send them
across the equivalence to find their corresponding $\Fin n$ values,
and then decide the equality of those $\Fin n$ values.
\end{proof}

Using $\FinSetT$, we can now finally define a HoTT counterpart to
$\B$.

\begin{defn}
  $\BT$ is defined by \[ \BT \hdefeq \tygrpd{\FinSetT}, \] the
  groupoid of cardinal-finite sets and paths between them.
\end{defn}

\begin{rem}
  It is worth pointing out that with this definition of $\BT$, we have
  ended up with something akin to the category of specifications
  $\Spec_{\size{}}$ used to define the anafunctor $\size : \B \to \P$
  in \pref{sec:finiteness-sets}, rather than something corresponding
  directly and na\"ively to $\B$ itself. The main difference is that
  $\BT$ uses a propositional truncation to ``hide'' the explicit
  choice of finiteness evidence.
\end{rem}

\subsection{Manifestly finite sets and linear orders}
\label{sec:manifestly-finite}

We now return to our first attempt at encoding cardinal-finiteness, \[
\FinType \hdefeq (A : \Type) \times (n : \N) \times (A \equiv \Fin
n). \] Recall that $\FinType$ turned out to be unsuitable as a basis
for $\B$ because it has at most one path between any two elements.
However, $\FinType$ turns out to be quite interesting in its own
right; instead of a counterpart to $\B$, it yields a counterpart to
$\L$, the category whose objects are finite sets \emph{equipped with
  linear orders}, and whose morphisms are \emph{order-preserving}
bijections.

For ease of reference, we will call $\FinType$ the type of
\term{manifestly finite} sets.  The claim is that manifestly finite
sets are the same as linearly ordered finite sets.  In one direction,
the evident linear order on $\Fin n$ induces a corresponding linear
order on $A$ via transport through the equivalence $A \equiv \Fin
n$. Conversely, given a linear order on a \emph{finite} set $A$, we
may construct an equivalence with $\Fin n$ by matching the smallest
element to $0$, the second smallest to $1$, and so on.  More formally:

\begin{prop}
  Manifestly finite sets are equivalent to linear orderings of finite
  sets, that is,
  \[ \SetL \equiv (A : \FinSetT) \times \linOrd(A), \] where
  $\linOrd(A)$ is suitably defined as the (constructive) existence of
  an antisymmetric, transitive, total binary relation on $A$.
\end{prop}
\begin{proof}
  As described above, the left-to-right direction is easy: there is a
  canonical inhabitant of $\linOrd(\Fin n)$, which we can turn into an
  inhabitant of $\linOrd(A)$ via transport.

  The right-to-left direction, while not hard to understand
  intuitively, is more subtle from a constructive point of view.  The
  key observation is that the smallest element of $A$ (according to
  the given linear order) is uniquely determined, and hence we are
  justified in ``peeking'' at the specific isomorphism contained in
  the propositional truncation in order to construct it (see
  \pref{sec:truncation}).  By induction on the size $n$, we can thus
  enumerate the elements of $A$ in order to find the smallest.  We
  then proceed to recursively construct the isomorphism corresponding
  to the linear order with the smallest element removed, and then to
  add back the smallest element, incrementing the indices of the
  remaining elements.
\end{proof}

Paths between elements of $\SetL$ are thus necessarily
order-preserving, since they correspond to paths between elements of
$(A : \FinSetT) \times \linOrd(A)$. (Note that this constitutes an
alternate proof of the fact that there is at most one path between any
two elements of $\SetL$.)  We can now define a counterpart to $\L$:

\begin{defn}
  Let $\LT$ denote \[ \LT \hdefeq \tygrpd{\SetL}, \] the groupoid of
  manifestly finite---\ie linearly ordered---sets, and
  (order-preserving) paths between them.
\end{defn}

\subsection{Equivalence of $\PT$ and $\BT$}
\label{sec:P-B-equiv}

Finally, we turn to the equivalence of $\PT$ and $\BT$, with a goal of
defining inverse functors $\fin - : \PT \to \BT$ and $\size : \BT \to
\PT$.  We begin with $\fin -$.

\begin{defn} \label{defn:functor-fin}
  The functor $\fin - : \PT \to \BT$ is defined as follows; the
  essential idea is to send the natural number $n$ to the canonical
  finite set $\Fin n$, and permutations to paths.
  \begin{itemize}
  \item On objects, $\fin n \hdefeq (\Fin n, \ptruncI{(n, \id)})$,
    where $\id : \Fin n \equiv \Fin n$ witnesses the finiteness of
    $\Fin n$.
  \item Recall that a morphism $\psi : \hom[\PT] m n$ is an
    equivalence $\psi : \Fin m \equiv \Fin n$. Thus $\ua\ \psi : \Fin
    m = \Fin n$, and we define $\fin \psi \hdefeq u\ (\ua\ \psi) :
    \fin m = \fin n$, where $u$ is some function witnessing the fact,
    mentioned immediately following \pref{defn:FinSetT}, that paths
    in $\FinSetT$ are characterized by paths between their underlying
    types.
  \end{itemize}
\end{defn}

Before turning to $\size : \BT \to \PT$, we note the following
property of $\fin -$:

\begin{lem}
  $\fin - : \PT \to \BT$ is full and faithful.
\end{lem}
\begin{proof}
  For any $m, n : \PT$, we must exhibit an equivalence between
  $(\hom[\PT] m n) \jeq (\Fin m \equiv \Fin n)$ and $(\hom[\BT] {\fin
    m} {\fin n}) \jeq (\fin m = \fin n) \equiv (\Fin m = \Fin
  n)$. such an equivalence is given by univalence.
\end{proof}

On the other hand, it is not at all obvious how to directly define a
functor $\size : \BT \to \PT$. Just as with $\B \to \P$, defining its
action on morphisms requires a specific choice of equivalence $A
\equiv \Fin n$. The objects of $\BT$ contain such equivalences, in the
proofs of finiteness, but they are propositionally truncated; the type
of functors $\BT \to \PT$ is decidedly not a mere proposition, so it
seems the recursion principle for truncation does not apply.

However, all is not lost!  We could try porting the concept of
anafunctor into HoTT, but it turns out that there is a better way.
Recall that in set theory, every fully faithful, essentially
surjective functor is an equivalence \emph{if and only if} the axiom
of choice holds.  In HoTT the situation turns out much better, thanks
to the richer notion of equality and the extra axiom associated with a
category.

First, there are two relevant notions of essential surjectivity (taken
from the HoTT book):

\begin{defn}
  A functor $F : \CT \to \DT$ between precategories $\CT$ and $\DT$ is
  \term{split essentially surjective} if for each object $D : \DT$
  there \emph{constructively exists} an object $C : \CT$ such that $F\
  C \iso D$. That is, \[ \msf{splitEssSurj}(F) \hdefeq (D : \DT) \to (C :
  \CT) \times (F\ C \iso D). \]
\end{defn}

\begin{defn}
  A functor $F : \CT \to \DT$ between precategories $\CT$ and $\DT$ is
  \term{essentially surjective} if for each object $D : \DT$ there
  \emph{merely exists} an object $C : \CT$ such that $F\ C \iso D$. That
  is, \[ \msf{essSurj}(F) \hdefeq (D : \DT) \to \ptrunc{ (C : \CT)
    \times (F\ C \iso D) }. \]
\end{defn}

It turns out that being split essentially surjective is a rather
strong notion.  In particular:

\begin{prop} \label{prop:splitEssSurj-equiv}
  For any precategories $\CT$ and $\DT$ and functor $F : \CT \to
  \DT$, $F$ is fully faithful and split essentially surjective if and
  only if it is an equivalence.
\end{prop}
\begin{proof}
  See the HoTT book~\citeyearpar[Lemma 9.4.5]{hottbook}.  Intuitively, the
  \emph{split} essential surjectivity gives us exactly what we need to
  unambiguously \emph{construct} an inverse functor $G : \DT \to \CT$:
  the action of $G$ on $D : \DT$ is defined to be the $C$---which
  exists constructively---such that $F\ C \iso D$.
\end{proof}

That is, a fully faithful, essentially surjective functor is an
equivalence given AC; a fully faithful, \emph{split} essentially
surjective functor is an equivalence even without AC.

Now, what about $\fin - : \PT \to \BT$?  We have the following:

\begin{prop}
  $\fin -$ is essentially surjective.
\end{prop}
\begin{proof}
  Given $(S,f) : \BT$, we must show that there merely exists some $n
  : \PT$ such that $\fin n \iso S$---but this is precisely the
  content of the $\isFinite$ proof $f$.
\end{proof}

On the other hand, it would seem that $\fin -$ is not split
essentially surjective, since that would require extracting finiteness
proofs from the propositional truncation, which is not allowed in
general.  However:

\begin{prop}[HoTT book, Lemma 9.4.7]
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

\begin{cor} \label{cor:essSurj-splitEssSurj}
  If $\CT$ is a category, a fully faithful functor $F : \CT \to \DT$
  is essentially surjective if and only if it is split essentially surjective.
\end{cor}

\begin{cor} \label{cor:BT-iso-PT}
Since $\fin -$ is a fully faithful and essentially surjective
functor out of a category, it is in fact \emph{split} essentially
surjective and thus an equivalence.  In particular, it has an inverse
(up to natural isomorphism) which we call $\size : \BT \to \PT$, and
thus \[ \size{} : \BT \iso \PT : \fin -. \]
\end{cor}

As a final remark, note that this is at root an instance of the
``trick'' explained at the end of \pref{sec:truncation}, whereby a
function $\ptrunc A \to B$ may be defined, even if $B$ is not a mere
proposition, as long as the value of $B$ produced can be uniquely
characterized.  Computationally speaking, $\size : \BT \to \PT$ does
precisely what we thought was not allowed---its action on morphisms
works by extracting concrete equivalences out of the finiteness proofs
in the objects of $\BT$ and using them to construct the required
permutation, just as in the construction of the anafunctor $\size : \B
\to \P$ in \pref{sec:finiteness-sets}.  Indeed, we are not allowed to
project finiteness evidence out from the propositional truncation when
defining \emph{arbitrary} functors $\BT \to \PT$.  However, we are not
interested in constructing any old functor, but rather a very
specific one, namely, an inverse to $\fin - : \PT \to \BT$---and the
inverse is uniquely determined.  In essence, the construction of
$\size$ proceeds by first constructing a functor paired with a proof
that, together with $\fin -$, it forms an equivalence---altogether a
mere proposition---and then projecting out the functor.

\section{Conclusion}
\label{sec:equality-conclusion}

In this chapter we have seen that encoding category theory and the
notion of finiteness in a constructive type theory is more subtle than
one might expect.  The difficulty with both---as often in type
theory---can be traced back to the foundational notion of equality.
Homotopy type theory, with its richer notion of equality, gives us
exactly the framework we need in which to encode category theory
without the use of the axiom of choice. Via propositional truncation,
we can also constructively encode the notion of finiteness such that
we can ``have our cake and eat it too''---with concrete,
computationally relevant isomorphisms witnessing finiteness that
nonetheless do not ``leak'' information inappropriately.  The close
connection between the encodings of $\B$ and $\L$, when viewed via
HoTT, came as a surprise, and yields new insight into equipotence as
well as $\L$-species (discussed in \pref{sec:L-species}).  In fact,
the work on homotopy type theory itself came as a fortuitous
surprise---I had been grappling with some of the questions in this
chapter, off and on, for several years before the publication of the
HoTT book.

The next chapter explains the formal definition of species, and puts
together the tools developed in this chapter into an encoding of
species within homotopy type theory.
