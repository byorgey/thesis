%% -*- mode: LaTeX; compile-command: "mk" -*-

%include thesis.fmt

\chapter{Species variants}
\label{chap:variants}

One of the goals of the previous chapter was to determine the
properties needed to define operations on ``variant species'', \ie
functors in some category $(\fc \Lab \Str)$.  We have seen a few
variants already:
\begin{itemize}
\item $\fc \B \Set$
\item $\fc \B \FinSet$, a more traditional notion of species
  which is more appropriate for doing combinatorics.
\item $\fc \P \Set$, species as families of shapes organized by
  \emph{size} instead of by labels.
\item $\fc \BT \ST$, species as constructed in HoTT.
\end{itemize}
There are quite a few other possible variants, some of which we
explore in this chapter. First, \pref{sec:copartial-species-sec} and
\pref{sec:partial-species} develop two novel species variants based on
the idea of replacing bijections between labels with injections (or
coinjections). Such species variants are conjectured to be especially
useful for modelling data structures that takes memory allocation and
layout into account.  Multisort species (\pref{sec:multisort}) are a
standard species variant that can also be seen as functors between
certain categories other than $\B$ and $\Set$.  Multisort species are
discussed in some detail, and also enable a discussion of recursive
species and the Implicit Species Theorem (\pref{sec:recursive}).
Finally, some other standard species variants (such as $\L$-species)
are mentioned in \pref{sec:L-species} and
\pref{sec:other-species-variants}.

\section{Generalized species properties}
\label{sec:generalized-species-properties}

We first gather and summarize the properties needed on $\Lab$ and
$\Str$ to support the operations we have studied.  The data are
summarized in \pref{tab:properties}.  At the head of each column is an
operation or group of operations.  In general, $\odot$-E denotes the
eliminator for $\odot$; in some cases the eliminator for a given
operation requires different or additional properties than the
operation itself.  $\partial$ indicates (higher) differentiation.  The
rows are labelled by properties, to be elaborated below.

\newcommand{\dayops}{$\cdot$, $\aprod$, $\comp$, $\partial$}
\newcommand{\dayelims}{$\cdot$-E, $\aprod$-E}

\begin{table}
\centering
\begin{tabular}{lc||c||c||c||c||c}
                                     & $+$, $\times$ & $+$-E      & $\times$-E & \dayops    & \dayelims  & $\comp$-E  \\
                                     &               &            &            &            &            &            \\
  $\Str$ monoidal                    & \checkmark    & \checkmark & \checkmark & \checkmark & \checkmark & \checkmark \\
  \dots coproduct                    &               & \checkmark &            &            &            &            \\
  \dots symm., pres. colimits        &               &            &            & \checkmark & \checkmark & \checkmark \\
  \dots left adjoint                 &               &            &            &            &            & \checkmark \\
  $\Lab$ locally small               &               &            & \checkmark &            &            &            \\
  $\Str$ complete, Cart. closed      &               &            & \checkmark &            &            &            \\
  $\Lab$ monoidal                    &               &            &            & \checkmark & \checkmark & \checkmark \\
  $\Lab$ enriched over $\Str$        &               &            &            & \checkmark & \checkmark & \checkmark \\
  $\Str$ has coends over $\Lab$      &               &            &            & \checkmark & \checkmark & \checkmark \\
  $\fc \Lab \Str$ enriched over self &               &            &            &            & \checkmark & \checkmark
\end{tabular}
\caption{Properties of $(\fc \Lab \Str)$ needed for species operations}
\label{tab:properties}
\end{table}
\later{When/why is it required for $\Lab$ to be a groupoid??}

\begin{itemize}
\item All operations require $\Str$ to be monoidal.  Some require
  additional properties of this monoidal structure:
  \begin{itemize}
  \item The eliminator for $+$ assumes that it is derived from the
    actual coproduct in $\Str$.
  \item All the operations built on Day convolution or something
    similar require the monoidal structure on $\Str$ to be symmetric
    and to preserve colimits.  It suffices, but is not necessary, for
    the monoidal product to be a left adjoint.
  \item On the other hand, the eliminator for $\comp$ really does
    require the monoidal product to be a left adjoint.
  \end{itemize}
\item The eliminator for Cartesian product, which corresponds to
  the Cartesian closure of $(\fc \Lab \Str)$, requires that $\Lab$ be
  locally small and $\Str$ complete and Cartesian closed.
\item Again, the operators defined via Day convolution and related
  operators require that $\Lab$ be monoidal and enriched over $\Str$,
  and that $\Str$ have coends over $\Lab$.
\item Finally, eliminators for partitional and arithmetic product and
  for composition require $(\fc \Lab \Str)$ to be enriched over
  itself: for example, in the context of $(\fc \B \Set)$ we end up
  treating a species morphism as itself being a species.
\end{itemize}

In each of the following sections we describe a particular species
variant, identifying the categories $\Lab$ and $\Str$, and verifying
which of the above properties hold.

\section{Copartial species}
\label{sec:copartial-species-sec}

As a larger example, which will also recur in \pref{chap:labelled}, we
develop the theory of species based on injections (and their dual,
coinjections, in the subsequent section).  The development will be
carried out in HoTT, though it works equally well in set theory.

\subsection{Copartial bijections}
\label{sec:copartial-bijections}

We begin by exploring the notion of a \term{copartial bijection}, a
bijection which is allowed to be partial in the backwards direction,
as illustrated in \pref{fig:copartial-bijection}.  Clasically, a
copartial bijection is the same as an injection; constructively, we
must take care to distinguish them.

\begin{rem}
  A \term{bijection} in HoTT is taken to be a pair of inverse
  functions. Recall that in general, this may not be the same as an
  \emph{equivalence}, although in the specific case of sets
  ($0$-types) the notions of bijection and equivalence do coincide.
  The following discussion sticks to the terminology of
  ``bijections'', but the reader should bear in mind that
  ``equivalences'' could also be used with no difference.
\end{rem}

The basic idea is to introduce a type of evidence witnessing the fact
that one set ($0$-type) is a ``subset'' of another, written $A
\cpbij B$.\footnote{There should be no problem in generalizing
  copartial bijections to copartial equivalences which work over any
  types, using an appropriate notion of copartial adjoint equivalences.
  However, there is no need for such generalization in the present
  work, so we stick to the simpler case of $0$-types.} Of course there
is no subtyping in HoTT, so there is no literal sense in which one
type can be a subset of another. However, the situation can be
modelled using constructive evidence for the embedding of one type
into another.  In order to focus the discussion, we begin with copartial
bijections between arbitrary sets, and only later restrict to finite
ones.

\begin{defn} \label{defn:pbij}
  A \term{copartial bijection} $f : A \cpbij B$ between two sets $A$
  and $B$ is given by:
\begin{itemize}
\item an embedding function $\embed f : A \to B$ (we will often simply
  use $f$, rather than $\embed f$, to refer to the embedding
  function),
\item a projection function $\project f : B \to \TyOne + A$,
\end{itemize}
together with two round-trip laws:
\begin{itemize}
\item $\project f \comp \embed f = \inr$, and
\item for all $a: A$ and $b : B$, if $\project f\ b = \inr\ a$
  then $\embed f\ a = b$.
\end{itemize}
\end{defn}

That is, $A \cpbij B$ witnesses that there is a $1$-$1$
correspondence between all the elements of $A$ and \emph{some}
(possibly all) of the elements of $B$, as pictured in
\pref{fig:copartial-bijection}. This concept is also known as a
\term{prism} in the Haskell \pkg{lens} library~\citep{lens}.

There is also a more elegant, though perhaps less intuitive,
formulation of the round-trip laws in \pref{defn:pbij}.

\begin{prop} \label{prop:rt-adj} The round-trip laws given in
  \pref{defn:pbij} are equivalent to
  \begin{equation} \label{eq:rt-adj}
    \all {a b} (\embed f\ a = b) \leftrightarrow (\inr\ a = \project f\ b).
  \end{equation}
\end{prop}

\begin{proof}
  Since the laws in question are all mere propositions, it suffices to
  show that they are logically equivalent; moreover, since the
  right-to-left direction of \eqref{eq:rt-adj} is precisely the second
  round-trip law, it suffices to show that the left-to-right direction
  is logically equivalent to the first round-trip law.  In one direction,
  \eqref{eq:rt-adj} implies the first round-trip law, by setting $b =
  \embed f\ a$. Conversely, given the first round trip law,
  \begin{sproof}
    \stmt{\embed f\ a = b}
    \reason{\implies}{apply $\project f$ to both sides}
    \stmt{\project f\ (\embed f\ a) = \project f\ b}
    \reason{\iff}{first round-trip law}
    \stmt{\inr\ a = \project f\ b.}
  \end{sproof}
\end{proof}

% \begin{rem}
%   Equation \eqref{eq:rt-adj} is strongly reminiscent of an adjunction.  However,
%   I do not know whether there is a suitable sense in which it can
%   actually be seen as one.
%   \later{from Derek Elkins: This may not be viewable as an adjunction,
%     but it's easily cast as an instance of parameterized
%     representability, namely b.inr a = f<-(b) is represented by f->(a)
%     parametric in a. This means f-> is characterized by a universal
%     property.  The universal arrow (the unit) is inr a ~ f<-(f->(a)).
%     The first round-trip law is this universal arrow; the second is
%     the existence part of the "there exists a unique f such that ..."
%     of the standard universal property dance.  Uniqueness is a given
%     for mere propositions.}
% \end{rem}

\begin{figure}
  \centering
  \begin{diagram}[width=150]
import           SpeciesDiagrams

dia = hcat' (with & sep .~ 3) [mkSet [0 :: Int .. 3], mkSet "abcdef"]
  # drawPBij pb1
  # applyAll (map toTop "cf")
  # lwO 0.7
  # frame 0.5

toTop n = withName n $ \s ->  -- $
  let topPt = location s .+^ (1.2 *^ unitX)
      aOpts = pBijAOpts & arrowTail .~ noTail & shaftStyle %~ dashingL [2,2] 0
  in  atop ((arrowBetween' aOpts (location s) topPt) <> text "⊤" # scale 0.3 # moveTo topPt)
  \end{diagram}
  \caption{A typical copartial bijection}
  \label{fig:copartial-bijection}
\end{figure}

As an aid in discussing copartial bijections we define $\pInv(f)$ which
together with $f : A \to B$ constitutes a copartial bijection $A
\cpbij B$.

\begin{defn}
  A \term{partial inverse} $\pInv(f)$ to $f : A \to B$ is defined so
  that \[ (A \cpbij B) \jeq (f : A \to B) \times \pInv(f), \] that
  is, \[ \pInv(f) \hdefeq (g : B \to \TyOne + A) \times (\all {a b}
  (f\ a = b) \lequiv (\inr\ a = g\ b)). \]
\end{defn}

We also define some notation to make working with copartial bijections
more convenient.

\begin{defn}
  First, for any types $A$ and $B$, there is a canonical copartial
  bijection $A \cpbij A + B$, which we denote simply by $\inl$;
  similarly, $\inr : B \cpbij A + B$.

  For the remainder, assume there is a copartial bijection $p : K \cpbij
  L$.
  \begin{itemize}
  \item $\embed p\ K$ denotes the image of $K$ under $p$, that is, the
    set of values in $L$ in the range of $\embed p$; we often simply
    write $p\ K$ instead of $\embed p\ K$.
  \item $\restr K p : K \bij p\ K$ denotes the bijection
    between $K$ and the image of $K$ in $L$.
  \item When some $q : K' \cpbij K$ is understood from the context, we
    also write $\restr {K'} p$ as an abbreviation for $\restr {K'} {(p
      \comp q)}$, the bijection between $K'$ and the image of $K'$ in
    $L$ under the composite $(p \comp q)$.
  \item $\extra p = \{ l : L \mid \project l = \inl\ \unit \}$ denotes
    the ``extra'' values in $L$ which are not in the image of $K$.
  \item $\extrabij p$ denotes the canonical bijection $K + \extra p
    \bij L$. \later{better notation for this?}
  \end{itemize}
\end{defn}

We now turn to the category structure on copartial bijections.

\begin{prop}
  Copartial bijections compose, that is, there is an associative
  operation \[ - \comp - : (B \cpbij C) \to (A \cpbij B) \to (A
  \cpbij C). \]
\end{prop}

\begin{figure}
  \centering
  \begin{diagram}[width=300]
import SpeciesDiagrams

sets = [mkSet [100 :: Int, 101], mkSet [0 :: Int .. 3], mkSet "abcdef"]

composite = hcat' (with & sep .~ 3) sets
  # drawPBij pb1 # drawPBij pb2

result = hcat' (with & sep .~ 3) [sets !! 0, sets !! 2]
  # drawPBij (pbComp pb1 pb2)

dia = hcat' (with & sep .~ 2)
  [ composite
  , text "="
  , result
  ]
  # lwO 0.7
  # frame 0.5
  \end{diagram}
  \caption{Composition of copartial bijections}
  \label{fig:copartial-bij-compose}
\end{figure}

\begin{proof}
  This can be intuitively grasped by studying a diagram such as the
  one shown in \pref{fig:copartial-bij-compose}.

  More formally, we set $\embed{(g \comp f)} = \embed g \comp \embed f$ and
  $\project{(g \comp f)} = \project f \kcomp \project g$, where $-
  \kcomp -$ denotes Kleisli composition for the $\TyOne + -$ monad
  (\ie |(<=<) :: (b -> Maybe c) -> (a -> Maybe b) -> (a -> Maybe c)|
  in Haskell). Associativity thus follows from the associativity of
  function composition and Kleisli composition.  In the following
  proof we also make use of $(-)^* : (A \to \TyOne + B) \to (\TyOne + A
  \to \TyOne + B)$, \ie |(=<<)| in Haskell.

  To show the required round-trip property we reason as follows.
  \begin{sproof}
    \stmt{\embed{(g \comp f)}\ a = c}
    \reason{\iff}{definition}
    \stmt{(\embed g \comp \embed f)\ a = c}
    \reason{\iff}{take $b = \embed f\ a$}
    \stmt{\exist b \embed f\ a = b \land \embed g\ b = c}
    \reason{\iff}{round-trip laws for $f$ and $g$}
    \stmt{\exist b \inr\ a = \project f\ b \land \inr\ b = \project g\
      c}
    \reason{\iff}{definition of $(-)^*$; case analysis}
    \stmt{\inr\ a = (\project f)^*\ (\project g\ c)}
    \reason{\iff}{Kleisli composition}
    \stmt{\inr\ a = (\project f \kcomp \project g)\ c}
    \reason{\iff}{definition}
    \stmt{\inr\ a = \project {(g \comp f)}\ c}
  \end{sproof}
\end{proof}

\begin{prop}
  Copartial bijections form an \hott{category}, $\STSub$, with sets as
  objects.
\end{prop}

\begin{proof}
  The identity morphism $\id : A \cpbij A$ is given by $\embed \id
  = \id$ and $\project \id = \inr$.  The identity laws follow from the
  fact that $\id$ is the identity for function composition, and $\inr$
  is the identity for Kleisli composition.

  $\STSub$ is thus a precategory.  It remains only to show that
  isomorphism is equivalent to equality.  An isomorphism $A \iso B$ is
  given by $f : A \cpbij B$ and $g : B \cpbij A$ such that $f
  \comp g = \id = g \comp f$.  Note that we have $\embed f : A \to B$
  and $\embed g : B \to A$ with $\embed f \comp \embed g = \embed{(f
    \comp g)} = \embed \id = \id$, and likewise for $\embed g \comp
  \embed f$.  Thus, $\embed f$ and $\embed g$ constitute a bijection
  $A \bij B$; since $A$ and $B$ are sets, this is the same as an
  equivalence $A \equiv B$, and hence by univalence an equality $A =
  B$.
\end{proof}

\begin{rem}
  Note that a bijection $f : A \bij B$ can be made into a copartial
  bijection $h : A \cpbij B$ trivially by setting $\embed h = f$ and
  $\project h = \inr \comp f^{-1}$, and moreover that this is a
  homomorphism with respect to composition; that is, the category of
  bijections embeds into the category of copartial bijections as a
  subcategory.  We will usually not bother to note the conversion,
  simply using bijections as if they were copartial bijections when
  convenient.\footnote{In fact, using the \pkg{lens} library---and
    more generally, using a van Laarhoven formulation of
    lenses~\citep{jaskelioff2014representation}---this all works out
    automatically: the representations of bijections (isomorphisms)
    and copartial bijections (prisms) are such that the former simply
    \emph{are} the latter, and they naturally compose via the standard
    function composition operator.}
\end{rem}

\subsection{Finite copartial bijections}
\label{sec:fin-copartial-bijections}

Finally, we turn to the theory of copartial bijections on \emph{finite}
sets. In the case of finite sets, it turns out that copartial bijections
$A \cpbij B$ can be more simply characterized as injective
functions $A \inj B$.  This might seem obvious, and indeed, it is
straightforward in a classical setting.  One direction, namely,
converting a copartial bijection into an injection, is straightforward
in HoTT as well (\pref{lem:pbij-is-inj}). However, to produce a
copartial bijection from an injection, we must be able to recover the
computational content of the backwards direction, and this depends on
the ability to enumerate the elements of $A$.  Recall that the
computational evidence for the finiteness of $A$ is propositionally
truncated (\pref{defn:FinSetT}), so it is not \latin{a priori} obvious
that we are allowed do this.  However, given a function $f : A \to B$,
its partial inverse (if any exists) is uniquely determined,
independent of the evidence for the finiteness of $A$
(\pref{lem:pinv-mere-prop}), so such evidence may be used in the
construction of a partial inverse (\pref{lem:inj-is-pbij}).

\begin{defn} \label{defn:injection} The type of \term{injections} $A
  \inj B$ is defined in HoTT analogously to the usual definition in
  set theory:
  \[ A \inj B \hdefeq (f : A \to B) \times \isInjective(f), \]
  where \[ \isInjective(f) \hdefeq \prod_{a_1, a_2 : A} (f\ a_1 = f\ a_2)
  \to (a_1 = a_2). \]
\end{defn}

\begin{rem}
  Note that $\isInjective(f)$ is a mere proposition when $A$ is a set:
  given $i, j : \isInjective(f)$, for all $a_1, a_2 : A$ and $e : f\ a_1
  = f\ a_2$, we have $i\ a_1\ a_2\ e = j\ a_1\ a_2\ e$ (since they are
  parallel paths between elements of a set) and hence $i = j$ by
  function extensionality.
\end{rem}

\begin{lem} \label{lem:pbij-is-inj}
  Every copartial bijection is an injection, that is, $(A \cpbij B)
  \to (A \inj B)$.
\end{lem}

\begin{proof}
  Let $f : A \cpbij B$.  Then $\embed f : A \to B$ is
  injective:
  \begin{sproof}
    \stmt{\embed f\ a_1 = \embed f\ a_2}
    \reason{\implies}{apply $\project f$ to both sides}
    \stmt{\project f\ (\embed f\ a_1) = \project f\ (\embed f\ a_2)}
    \reason{\iff}{$f$ is a copartial bijection}
    \stmt{\inr\ a_1 = \inr\ a_2}
    \reason{\iff}{$\inr$ is injective}
    \stmt{a_1 = a_2.}
  \end{sproof}
\end{proof}

\begin{lem} \label{lem:pinv-mere-prop}
  If $A$ and $B$ are sets and $f : A \to B$, then $\pInv(f)$ is a mere
  proposition.
\end{lem}

\begin{proof}
  Let $(g, p), (g', p') : \pInv(f)$.  That is, $g, g' : B
  \to \TyOne + A$, and
  \begin{itemize}
  \item $p : \all {a b} (f\ a = b) \lequiv (\inr\ a = g\ b) $, and
  \item $p' : \all {a b} (f\ a = b) \lequiv (\inr\ a = g'\ b)$.
  \end{itemize}
  We must show that $(g, p) = (g', p')$.  To this end we
  first show $g = g'$.  By function extensionality it suffices to show
  that $g\ b = g'\ b$ for arbitrary $b : B$.  We proceed by case
  analysis on $g\ b$ and $g'\ b$:
  \begin{itemize}
  \item If $g\ b = g'\ b = \inl\ \unit$ we are done.
  \item If $g\ b = \inr\ a$ then by $p$ and $p'$ we also have $g'\ b =
    \inr\ a$ and hence $g\ b = g'\ b$; a symmetric argument handles
    the case $g'\ b = \inr\ a$.
  \end{itemize}

  Letting $r : g = g'$ denote the equality just constructed, we
  complete the argument by noting that $r_*(p)$ and $p'$ are parallel
  paths between elements of a set, and hence equal.
\end{proof}

\begin{lem} \label{lem:inj-is-pbij}
  If $A$ is a finite set and $B$ a set with decidable equality,
  then \[ (A \inj B) \to (A \cpbij B). \]
\end{lem}

\begin{proof}
  Let $f : A \to B$ be an injective function; we must construct $h : A
  \cpbij B$.  First, we set $\embed h = f$.  It remains to
  construct $\pInv(\embed h)$, which is a mere proposition by
  \pref{lem:pinv-mere-prop}.  Thus, by the recursion principle for
  propositional truncation, we are justified in using the constructive
  evidence of $A$'s finiteness, that is, its cardinality $n : \N$ and
  bijection $\sigma : A \equiv \Fin n$.  We define $\project h : B \to
  \TyOne + A$ on an input $b : B$ as follows: by recursion on $n$,
  find the smallest $k : \Fin n$ such that $\embed h\ (\sigma^{-1}\ k) =
  b$.  If such a $k$ exists, yield $\inr\ (\sigma^{-1}\ k)$; otherwise,
  yield $\inl\ \unit$.

  Finally, we establish the round-trip law $\all {a b} (\embed h\ a = b)
  \leftrightarrow (\inr\ a = \project h\ b)$.
  \begin{itemize}
  \item[$(\rightarrow)$] Suppose $\embed h\ a = b$.  Then
    $\project h\ b$ will certainly find some $k : \Fin n$ with
    $\embed h\ (\sigma^{-1}\ k) = b$, and thus $\project h\ b = \inr\
    (\sigma^{-1}\ k)$; since $\embed h$ is injective it must actually be
    the case that $\sigma^{-1}\ k = a$.
  \item[$(\leftarrow)$] This follows directly from the definition
    of $\project h$.
  \end{itemize}
\end{proof}

\begin{prop} \label{prop:inj-equiv-pbij}
  For $A$ a finite set and $B$ a set with decidable equality,
  \[ (A \inj B) \equiv (A \cpbij B). \]
\end{prop}

\begin{proof}
  \pref{lem:pbij-is-inj} and \pref{lem:inj-is-pbij} establish
  functions in both directions.  It is easy to see that they act as
  the identity on the underlying $f : A \to B$ functions, and the
  remaining components are mere propositions by
  \pref{lem:pinv-mere-prop} and the remark following
  \pref{defn:injection}.  Thus the functions defined by
  \pref{lem:pbij-is-inj} and \pref{lem:inj-is-pbij} are inverse.
\end{proof}

\begin{defn}
  Denote by $\BTSub$ the \hott{category} of finite sets and copartial
  bijections (\ie injections).  That is, objects in $\BTSub$ are
  values of type $\FinSetT \jeq (A : \Type) \times
  \isFinite(A)$, and morphisms $\hom[\BTSub] {(A,f_A)}
  {(B,f_B)}$ are copartial bijections $A \cpbij B$.  Showing that
  this is indeed an \hott{category} is left as an easy exercise.
\end{defn}

$\BTSub$ also has a corresponding skeleton category, just like $\BT$:

\begin{defn}
  Denote by $\PTSub$ the \hott{category} whose objects are natural
  numbers and whose morphisms are given by $\hom[\PTSub] m n \hdefeq \Fin m
  \inj \Fin n$. The proof that this is an \hott{category} is also left
  as an exercise.
\end{defn}

\begin{rem}
  $\PTSub$ has $m!\binom{n}{m}$ distinct morphisms $\hom m n$, since
  there are $\binom n m$ ways to choose the $m$ distinct objects in
  the image of the morphism, and $m!$ ways to permute the mapping.
  Note this this means there are zero morphisms when $m > n$, and
  exactly $n!$ morphisms $\hom n n$.
\end{rem}

\begin{prop} \label{prop:btsub-iso-ptsub}
  $\BTSub \iso \PTSub$.
\end{prop}

\begin{proof}
  The proof is similar to the proof that $\BT$ is equivalent to $\PT$
  (\pref{cor:BT-iso-PT}).  We define a functor $\fin{-}_{\cpbij} :
  \PTSub \to \BTSub$ which sends $n$ to $(\Fin n, \ptruncI{(n,\id)})$
  (just like the functor $\fin - : \PT \to \BT$ defined in
  \pref{defn:functor-fin}), and which sends $\iota : \hom[\PT] m n
  \jeq \Fin m \inj \Fin n$ to the corresponding copartial bijection
  (\pref{prop:inj-equiv-pbij}).  It is not hard to show that this
  functor is full, faithful, and essentially surjective, which by
  \pref{prop:splitEssSurj-equiv} and \pref{cor:essSurj-splitEssSurj}
  implies that $\fin{-}_{\cpbij} : \PTSub \to \BTSub$ is one half of an
  equivalence. \later{actually flesh this out?}
\end{proof}

\subsection{Copartial species}
\label{sec:copartial-species-subsec}

The point of all this machinery is that we can now use the
category $\BTSub$ as the category of labels for a new notion of
species.

\begin{defn}
  A \term{copartial species} is a functor $F : \BTSub \to \ST$.  We
  denote by $\PSpe = \fc \BTSub \ST$ the functor category of copartial
  species.
\end{defn}

\begin{rem}
  Since $\BTSub \iso \PTSub$ (\pref{prop:btsub-iso-ptsub}) copartial
  species are also equivalent to functors $\PTSub \to \ST$.
\end{rem}

Since the objects of \BTSub\ are the same as the objects of \BT, the
object mapping of a copartial species is similar to that of a normal
species.  That is, one can still think of a copartial species as mapping
a finite set of labels to a set of structures ``built from'' those
labels.

A copartial species $F$ also has an action on morphisms: it must lift
any copartial bijection $K \cpbij L$ to a function $F\ K \to F\ L$.  Of
course, bijections are (trivially) copartial bijections, so this includes the
familiar case of ``relabelling''; bijections are isomorphisms in
$\BTSub$, and functors necessarily preserve isomorphisms, so
bijections on labels are still sent to bijections between structures.

The case of strictly copartial bijections, that is, $K \cpbij L$ where
$\size K < \size L$, is more interesting.  Each structure in the set
$F\ K$, with labels in $K$, must map to a structure in $F\ L$, given
an embedding of $K$ into $L$.  Intuitively, this can be thought of as
introducing extra labels which must be incorporated into the
structure in a suitably canonical way.  However, the copartial bijection
$p : K \cpbij L$ affords no structure whatsoever on the extra
labels (that is, those $l \in L$ for which $\project p\ l = \inl\ 
\unit$).  So it is not acceptable, for example, to prepend the extra
labels to the front of a list structure, since there is no canonical
way to choose an ordering on the extra labels.  The only feasible
approach is to simply attach the extra labels in a \emph{set}, as
illustrated in \pref{fig:lift-strict-pbij}.

\begin{figure}
  \centering

  \begin{diagram}[width=200]
import           Data.Char
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams
import           Structures                     (pair)

t = BNode 1 (leaf 3) (BNode 2 (leaf 0) Empty)

c2i = subtract (ord 'a') . ord

s = hcat' (with & sep .~ 3) [mkSet' (scale 0.3 . mloc) [0 :: Int .. 3], mkSet' (scale 0.3 . mloc . c2i) "abcdef"]
  # drawPBij pb1
  # lwO 0.7
  # frame 0.5

t4 = scale 0.5 . drawBinTree' tOpts . fmap (mloc) $ t  -- $
t6 = scale 0.5 . drawBinTree' tOpts . fmap (mloc . c2i . applyPBij pb1) $ t  -- $
t6' = pair t6 (hcat' (with & sep .~ 0.5) (scale 0.5 [mloc 2, mloc 5]))

tOpts = with & slHSep .~ 4 & slVSep .~ 3

ts = hcat' (with & sep .~ 0.5) . map centerY $   -- $
  [t4, arrow 2, t6']

dia = (vcat' (with & sep .~ 1) . map centerX) [s # scale 1.5, ts]
  # frame 0.5
  # lwO 0.7
  \end{diagram}
  \caption{Lifting a strictly copartial bijection}
  \label{fig:lift-strict-pbij}
\end{figure}

Moreover, note that one cannot adjoin a \emph{new} set of labels with
every lift.  Performing multiple lifts would then result in multiple
sets of extra labels (\eg a list of such sets), but this fails to be
functorial, since separately lifting two copartial bijections
(resulting in a list of two extra sets) would be different than
lifting their composition (resulting in only one).  So the only option
is to have \emph{every} copartial species structure accompanied by a set
of ``extra'' labels (which may be empty). Transporting along a
strictly copartial bijection results in some labels being added to the
set.

Intuitively, every normal species $F$ gives rise to a copartial species
$\prt F$ which acts like the species $F \cdot \Bag$.  In fact,
along these lines we can formally define a fully faithful embedding of
\Spe into \PSpe.

\begin{defn}
  The functor $\prt - : \Spe \to \PSpe$ is defined as follows.

  First consider the action of $\prt -$ on objects, that is, species
  $F : \BT \to \ST$.  We define $\prt F : \BTSub \to \ST$ as the
  copartial species which
  \begin{itemize}
  \item sends the finite set of labels $K$ to the set of structures
    $(F \cdot \Bag)\ K$, and
  \item lifts the copartial bijection $p : K \cpbij L$ to a function
    $\prt p : \prt F\ K \to \prt F\ L$.  \later{insert picture here?}
    This function takes as input a structure of type $(F \cdot \Bag)\
    K$, that is, a tuple \[ (K_1, K_2, f, \unit, \sigma) \] where $f :
    F\ K_1$ is a $K_1$-labelled $F$-structure, the unit value $\unit$
    represents a $K_2$-labeled set, and $\sigma : K \bij K_1 + K_2$
    witnesses that $K_1$ and $K_2$ form a partition of the label set
    $K$.  As output, $\prt p$ yields \[ (L_1, L_2 + \extra p, F\
    (\restr{K_1}{p_1})\ f, \unit, \psi), \] where:
    \begin{itemize}
    \item $p_1$ is the ``restriction of $p$ to $K_1$'', that is, the
      composite copartial bijection
      \[ p_1 : \xymatrix{K_1 \ar[r]^-{\cpbij}_-{\inl} & K_1 + K_2
        \ar[r]^-{\sim}_-{\sigma^{-1}} & K \ar[r]^{\cpbij}_{p} & L}. \]
      Similarly, $p_2 : K_2 \cpbij L$.
    \item $L_1 = p_1\ K_1$ is the image of $K_1$ under the restricted
      copartial bijection $p_1$.  Similarly, $L_2 = p_2\ K_2$. Note that
      we ``throw in the extra labels'' by using the coproduct $L_2 +
      \extra p$ as the second set of labels.
    \item Recall that $\restr {K_1} {p_1} : K_1 \bij p_1\ K_1$; thus
      $F\ (\restr {K_1} {p_1})\ f$ denotes the relabelling of the
      $F$-structure $f$ from $K_1$ to $p\ K_1 = L_1$.
    \item $\psi : L \bij L_1 + (L_2 + \extra p)$ is given by the composite
    \[ \xymatrixcolsep{4pc} \xymatrix{L \ar[r]^-{\sim}_-{\extrabij p} & p\ K +
      \extra p}. \]
    \end{itemize}
  \end{itemize}
  \later{We must verify that this defines a valid functor $\BTSub \to
  \ST$.}

  Next, consider the action of $\prt -$ on morphisms, that is, natural
  transformations $\varphi : \all L F\ L \to G\ L$ where $F$ and $G$
  are species.  Define $(\prt \varphi)_L : \prt F\ L \to \prt G\ L$
  by \[ (L_1, L_2, f, \unit, \sigma) \mapsto (L_1, L_2, \varphi_{L_1}\
  f, \unit, \sigma). \] For this to be natural, the following square
  must commute for all $F, G : \BT \to \ST$, all $\varphi : \all L F\
  L \to G\ L$, and all $p : K \cpbij L$:
  \[ \xymatrix
       { \prt F\ K \ar[d]_{\prt F\ p} \ar[r]^{(\prt \varphi)_K}
       & \prt G\ K \ar[d]^{\prt G\ p}
      \\ \prt F\ L                    \ar[r]_{(\prt \varphi)_L}
       & \prt G\ L
       }
  \]
  Consider an arbitrary element $(K_1, K_2, f, \unit, \sigma)$ of the
  top-left corner.  Note that the action of $\prt \varphi$ on a
  five-tuple only affects the middle value, and likewise note that the
  action of $\prt F\ p$ and $\prt G\ p$ are identical on all but the
  middle value (that is, the middle value is the only one affected by
  $F$ or $G$ specifically).  Thus, it suffices to consider only the
  fate of $f$ as it travels both paths around the square.
  Travelling around the left and bottom sides yields
  \[ \varphi_{L_1}\ (F\ (\restr{K_1}{p_1})\ f), \] whereas the top and
  right sides yield \[ G\ (\restr{K_1}{p_1})\ (\varphi_{K_1}\ f). \]
  These are equal by naturality of $\varphi$.

  Finally, it is easy to verify that $\prt -$ itself satisfies the
  functor laws, since the mapping \[ (L_1, L_2, f, \unit, \sigma)
  \mapsto (L_1, L_2, \varphi_{L_1}\ f, \unit, \sigma) \] clearly
  preserves identity and composition of natural transformations.
\end{defn}

% \begin{prop}
%   $\prt - : \Spe \to \PSpe$ is full.
% \end{prop}

% \begin{proof}
%   \later{prove me}
% \end{proof}

% \begin{prop}
%   $\prt - : \Spe \to \PSpe$ is faithful.
% \end{prop}

% \begin{proof}
%   \later{prove me}
% \end{proof}

\later{Is the functor $\prt -$ monoidal? Intuitively, yes for $+$, no
  for $\cdot$.  Probably not for $\comp$.}

\later{Prove this.}
\begin{conj}
  $\prt -$ is full and faithful.
\end{conj}

The above discussion might lead one to believe that $\prt -$ must also
be essentially surjective, \ie that there is an equivalence of
categories $\Spe \iso \PSpe$.  However, this is not the case. To see
why, we consider the connection between species, copartial species,
and generating functions.

According to our intuition so far, a copartial species corresponds to
a regular species with a set of extra labels possibly attached.
Consider, therefore, the relationship of the species $F$ to the
species $F \cdot \Bag$.  An $(F \cdot \Bag)$-shape of size $n$
consists of an $F$-shape, of \emph{any} size from $0$ to $n$, paired
with a (unique) $\Bag$-shape on the remaining labels.  $F \cdot \Bag$
thus represents a sort of ``prefix sum'' of $F$, where the collection
of $(F \cdot \Bag)$-shapes of size $n$ consists of the sum of all
$F$-shapes of sizes $0$ through $n$.  This is illustrated in
\pref{fig:prefix-sum}.
\begin{figure}
  \centering
  \begin{diagram}[width=300]
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams
import           Structures                     (pair)

genBTreeShapes :: Int -> [BTree ()]
genBTreeShapes 0 = [Empty]
genBTreeShapes n = [ BNode () l r
                   || k <- [0..n-1]
                   , l <- genBTreeShapes k
                   , r <- genBTreeShapes (n - k - 1)]

dot c = circle 1 # fc c
emptyDia = square 1 # fc black # frame 0.5

drawBinTreeWE :: Diagram B R2 -> SymmLayoutOpts (Diagram B R2) -> BTree (Diagram B R2) -> Diagram B R2
drawBinTreeWE e _ Empty = e
drawBinTreeWE _ opts t = drawBinTree' opts t

genTreeDias n = genBTreeShapes n
  # map (drawT n)

drawT n = drawBinTreeWE emptyDia (with & slHSep .~ 3 & slVSep .~ 3)
        . fmap (const (dot (colors !! n)))

f = map genTreeDias [0 .. 3]
  # map (alignL . hcat' (with & sep .~ 1.5))
  # vcat' (with & sep .~ 2)
  # frame 0.5
  # lwO 0.7

genTreeBagDias n = map (genTreeBagDias' n) [0 .. n]
                 # hcat' (with & sep .~ 1)
                 # alignL
  where
    genTreeBagDias' n k = genBTreeShapes (n - k)
      # map (\t -> drawT (n-k) t # if k == 0 then id else flip pair (mkS k))
      # hcat' (with & sep .~ 1)
      # alignT
    mkS 0 = mempty
    mkS 1 = dot mlocColor
    mkS 2 = (vcat' (with & sep .~ 1) (replicate 2 (dot mlocColor)))
    mkS k = position (zip (regPoly k 3) (repeat (dot mlocColor)))

fe = map genTreeBagDias [0..3]
   # vcat' (with & sep .~ 2)

dia = vcat' (with & sep .~ 6) (map centerX [f, fe])
  # frame 1
  # lwO 0.7
  \end{diagram}
  \caption{$\Bin \cdot \Bag$ (bottom) is the prefix sum of $\Bin$ (top)}
  \label{fig:prefix-sum}
\end{figure}
In terms of generating functions, the operator $- \cdot \Bag(x) = -
\cdot e^x$ indeed corresponds to a prefix sum on coefficients: \[ -
\cdot e^x : (a_0 + a_1x + a_2x^2 + \dots) \mapsto (a_0 + (a_0 + a_1)x
+ (a_0 + a_1 + a_2)x^2 + \dots). \] Note that as an operator on
generating functions, this has an inverse, given by
\begin{equation} \label{eq:prefix-sum-inverse}
  (b_0 + b_1x
  + b_2x^2 + \dots) \mapsto (b_0 + (b_1 - b_0)x + (b_2 - b_1)x^2 +
  \dots).
\end{equation}

Consider, then, an attempted proof that $\prt - : \Spe \to \PSpe$ is
essentially surjective.  Given a copartial species $S \in \PSpe$, this
would require us to produce some $F \in \Spe$ such that $\prt F \iso
S$.  If we think of $\prt F$ as intuitively acting like $F \cdot
\Bag$, we see that $S$ should correspond to a ``prefix sum'' of $F$.
Then we should ideally be able to construct $F$ via an operation
similar to \eqref{eq:prefix-sum-inverse}.  That is (passing to $\fc \P
\Set$ and $\fc \PTSub \ST$), we would define
\begin{align*}
F\ 0 &\defeq S\ 0 \\
F\ (n+1) &\defeq S\ (n+1) - S\ n.
\end{align*}
However, we must make sense of this subtraction.  We cannot simply
take a set difference (indeed, set difference makes no sense in the
context of HoTT).  What is needed is some sort of canonical injection
$\iota : S\ n \inj S\ (n+1)$, in which case we could make sense of $S\
(n+1) - S\ n$ as the elements of $S\ (n+1)$ not in the image of
$\iota$.  In the case of species of the form $F \cdot \Bag$, there
indeed exists such a canonical injection, which sends each shape in
$(F \cdot \Bag)\ n$ to the same shape with the extra label $n$
adjoined to the set.  The whole point, however, is that we are
\emph{trying to prove} that every $S \in \PSpe$ is of this form.  We
must therefore come up with some injection $S\ n \inj S\ (n+1)$
without any intensional knowledge about $S$.

This is precisely where we get stuck.  There is, of course, a
canonical injection $\Fin n \inj \Fin {n+1}$, but the functoriality of
$S$ only guarantees that this lifts to a \emph{function} $S\ n \to S\
(n+1)$---functors may preserve isomorphisms, but in general, they need
not preserve monomorphisms.  This insight guides us to a
counterexample.  Consider the $(\fc \BTSub \ST)$-species whose shapes
\emph{of size $5$ or smaller} consist of a binary tree paired with a
set, and \emph{on larger sizes} simply consist of a
set (\pref{fig:copartial-species-collapse}).

\begin{figure}
  \centering
  \begin{diagram}[width=200]
import           Data.Char
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams
import           Structures                     (pair)

t = BNode 1 (leaf 3) (leaf 2)

c2i = subtract (ord 'a') . ord

s = hcat' (with & sep .~ 3) [mkSet' (scale 0.3 . mloc) [0 :: Int .. 3], mkSet' (scale 0.3 . mloc . c2i) "abcdef"]
  # drawPBij pb1
  # lwO 0.7
  # frame 0.5

t3 = scale 0.5 . drawBinTree' tOpts . fmap (mloc) $ t  -- $
t4' = pair t3 (scale 0.5 (mloc 0))

set6 = enclose 0.5 0.5 (position (zip (pentagon 1.5 # rotateBy (2/5)) (map (scale 0.5 . mloc) [0..4])))

tOpts = with & slHSep .~ 4 & slVSep .~ 3

collapse = hcat' (with & sep .~ 0.5) . map centerY $   -- $
  [t4', arrow 2, set6]

dia = (vcat' (with & sep .~ 1) . map centerX) [s # scale 1.5, collapse]
  # frame 0.5
  # lwO 0.7
  \end{diagram}
  \caption{A copartial species which loses information}
  \label{fig:copartial-species-collapse}
\end{figure}

One may verify that this does, in fact, describe a valid functor
$\BTSub \to \ST$.  However, it does not preserve information:
above size $5$ the shapes all collapse, and information about
smaller shapes is lost.  The intuition that all copartial species
shapes must come equipped with a set of labels is correct, in a
sense, but there is some latitude in the way the rest of the shape is
handled.

We may also, therefore, consider the subcategory $\BTSub
\hookrightarrow \ST$ of \emph{monomorphism-preserving} functors $\fc
\BTSub \ST$; along the lines sketched above, we can indeed prove an
equivalence between this category and $\Spe$.  At present, the pros
and cons of considering $\PSpe$ versus this subcategory are not clear
to me.

Finally, we consider which of the properties from
\pref{tab:properties} hold for $\fc \BTSub \ST$.
\begin{itemize}
\item Since the target category is just $\ST$ we automatically get all
  the properties required of $\Str$ alone (\eg monoidal, complete, and
  Cartesian closed); $\ST$ is also cocomplete and so has coends over
  $\BTSub$.
\item $\BTSub$ is locally small.
\item $\BTSub$ is monoidal: though it does not have products or
  coproducts, it is not hard to see that it has monoidal structures
  corresponding to the Cartesian product and disjoint union of finite
  sets.  Given injections $f : S_1 \inj T_1$ and $g : S_2 \inj T_2$ we
  can use them to form the evident injections $S_1 \uplus S_2 \inj T_1
  \uplus T_2$ and $S_1 \times S_2 \inj T_1 \times T_2$.
\item $\BTSub$ is enriched over $\Str$, since its morphisms can be
  seen as injective functions.
% \item \later{$\fc \BTSub \ST$ enriched over itself?}
\end{itemize}

\section{Partial species}
\label{sec:partial-species}

We now consider the dual category $\BTSub^\op$, whose objects are
finite sets and whose morphisms are partial bijections, \ie
coinjections, and written $K \supseteq L$.  These can be thought of as
partially defined functions which are both injective and surjective.

Species corresponding to $\fc {\BTSub^\op} \ST$ were studied by
\citet{schmitt93hopfalgebras} (under the name ``species with
restriction'', or ``$R$-species'') and correspond to species with a
natural notion of ``induced subspecies''.  That is, $F : \BTSub^\op
\to \ST$ must lift morphisms of the form $K \supseteq L$ to functions
$F\ K \to F\ L$.  Instead of adding more labels, this operation may
\emph{delete} labels.  Examples include the species of lists, where
labels may simply be deleted, keeping the rest of the labels in the
same order; similarly, the species of cycles; and the species of
simple graphs, where the lifting operation corresponds to forming
induced subgraphs. \later{make a picture}

When we consider the properties in \pref{tab:properties}, however, we
find in particular that $\BTSub^\op$ is not enriched over $\ST$.
Coinjections are not, in general, total functions, so there is no way
to canonically treat morphisms in $\BTSub^\op$ as objects of $\ST$.
Instead of $\ST$, we actually want to consider the category $\STp$ of
sets and \emph{partial} functions. One may check that $\STp$ is
monoidal, complete, and Cartesian closed, that it has coends over
$\BTSub^\op$, and that $\BTSub^\op$ is indeed enriched over $\STp$.

\section{Multisort species}
\label{sec:multisort}

Multisort species are a generalization of species in which the labels
are classified according to multiple \term{sorts}.  We often use $\X$,
$\Y$, $\ZZ$ or $\X_1$, $\X_2$, \dots to denote sorts.  In particular,
(say) $\Y$ denotes the species, analogous to $\X$, for which there is
a single shape containing a single label \emph{of sort $Y$} (and none
of any other sort).  More generally, multisort species correspond to
multivariate generating functions. See \citet[\Sect 4.2]{bll} for a
precise, detailed definition.  For now, an intuitive sense is
sufficient; we will give a more abstract definition later.

\begin{ex}
  Consider \[ \frak{T} = \Y + \X \cdot \frak{T}^2, \] the two-sort
  species of binary trees with internal nodes and leaves labelled by
  distinct sorts.  \pref{fig:bin-two-sort} illustrates an example
  shape of this species, with one label sort represented by blue
  circles, and the other by green squares.
  \begin{figure}
    \centering
    \begin{diagram}[width=200]
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

t = nd 0 (nd 3 (lf 1) (nd 1 (lf 0) (lf 3))) (nd 2 (lf 2) (lf 4))
  where
    nd x l r = BNode (Left x) l r
    lf x = BNode (Right x) Empty Empty

drawSort (Left i) = mloc i
drawSort (Right i) = text (show i) <> square 1.6 # fc (colors !! 2)

dia = (drawBinTree' (with & slVSep .~ 3 & slHSep .~ 4) . fmap drawSort $ t) -- $
  # frame 0.5
  # lwO 0.7
    \end{diagram}
    \caption{A two-sort species of binary trees}
    \label{fig:bin-two-sort}
  \end{figure}
\end{ex}

\begin{ex}
  $\Cyc \comp (\X + \Y)$ is the species of \term{bicolored cycles},
  \ie cycles whose labels are colored with one of two colors
  (\pref{fig:bicolored-cycle}).
  \begin{figure}
    \centering
    \begin{diagram}[width=150]
import           SpeciesDiagrams

elts = [mlocColor, colors !! 2, mlocColor, colors !! 2, mlocColor]

dia = cyc' (map (\c -> circle 0.3 # fc c) elts) 1
  # frame 0.5
  # lwO 0.7
    \end{diagram}
    \caption{A bicolored cycle}
    \label{fig:bicolored-cycle}
  \end{figure}
\end{ex}

\begin{ex}
  Recall the example from \pref{sec:basic-diff}, in which open terms
  of the untyped lambda calculus are modeled using the species \[
  \Lambda = \elts + \Lambda^2 + \Lambda'. \] However, this species
  does not correctly model the size of lambda calculus terms.
  \pref{sec:basic-diff} suggested instead using the multisort
  species \[ \Xi = \X \cdot \Bag + \Y \cdot \Xi^2 + \Y \cdot
  \frac{\partial}{\partial \X} \Xi. \] An even better idea is to use a
  three-sort species, as in \[ \Xi = \X \cdot \Bag + \Y \cdot \Xi^2 + \ZZ
  \cdot \frac{\partial}{\partial \X} \Xi, \] where $\X$ stands in for
  variables, $\Y$ for applications, and $\ZZ$ for lambdas.

  In general, any algebraic data type may be modelled by a multisort
  species, with one sort corresponding to each constructor.  The
  singletons of a given sort count occurrences of the corresponding
  construct and ensure that species structures of a finite size
  correspond to data structures that take only a finite amount of
  memory.
\end{ex}

\later{Graphs with labelled vertices and edges. Not obvious how to
  write down an algebraic expression for it; see BLL 2.4.}
% \begin{ex}
%   As another example, consider the two-sort species of simple graphs
%   whose vertices are labelled by one sort, and edges by another
%   (illustrated in ...)
% \end{ex}

\citet{bll} detail how to extend operations such as sum, partitional
product, and composition to multisort species.  For example,
partitional product is straightforward: an $(F \cdot G)$-shape over a
given collection of labels (of multiple sorts) corresponds to a pair
of an $F$-shape and $G$-shape over a binary partition of the
collection (which can also be thought of as a collection of binary
partitions over each sort).  Composition can also be extended to
multisort species---although, as we will see, it does not follow quite
as naturally from the single-sort setting.  If $F$ is an $m$-sort
species, and $(G_1, \dots, G_m)$ is an $m$-tuple of $n$-sort species,
then $F \comp (G_1, \dots, G_m)$ is an $n$-sort species whose shapes
consist of a top-level $F$-shape with $G_i$-shapes substituted for
each label of sort $i$.  Of course, this presentation assumes a linear
ordering on the sorts of $F$; more generally, if the sorts of $F$ are
indexed by some finite set $S$, then $F$ can be composed with an
$S$-indexed tuple of $T$-sort species, resulting in a $T$-sort
species.

\later{Example of generalized composition?}
% \begin{ex}
%   \later{Need an example of generalized composition.}
% \end{ex}

\begin{rem}
  Multisort species are often notated using ``multi-argument
  function'' notation, for example, \[ \H(\X,\Y) = \X + \Y^2. \] This
  makes clear which singleton species are being used to represent the
  various sorts, and makes it possible to refer to them positionally
  as well.  This notation also meshes well with the notion of
  generalized composition just introduced: writing something like
  $\H(F,G)$ can be interpreted as $\H \comp (F,G)$ and corresponds
  exactly to the substitution of $F$ and $G$ for $\X$ and $\Y$.
\end{rem}

Defining multisort species and all the operations on them (such as
composition) from scratch is unnecessary; they can be defined
abstractly as objects in a certain functor category, and hence fit
into the abstract framework developed in \pref{chap:species} and
outlined in \pref{sec:generalized-species-properties}.  \citet{bll}
acknowledge as much in Exercise 2.4.6, but only as something of an
afterthought; the following development is yet more general than the
intended solution to the exercise.

Let $S$ be a finite set, thought of as a collection of names for
sorts; that is, each element $s \in S$ represents a different sort.
Let $\Lab$ be a category, thought of as a category of labels (\eg
$\B$).  Now consider the functor category $\Lab^S$ (with $S$
considered as a discrete category, as usual).  Objects of $\Lab^S$ are
functors $S \to \Lab$, that is, assignments of an object from $\Lab$
to each $s \in S$. Morphisms in $\Lab^S$ are natural transformations,
that is, $S$-indexed families of $\Lab$-morphisms between
corresponding objects of $\Lab$.  For example, in the case $\Lab =
\B$, objects of $\B^S$ are just $S$-tuples of finite sets, and
morphisms are $S$-tuples of bijections between them.

\begin{rem}
  Recall that $\Set^S \iso \Set/S$ (\pref{sec:ct-fundamentals}).  It
  is not the case that $\B^S \iso \B/S$, since objects of $\B/S$
  consist of a finite set $L$ paired with a \emph{bijection} $L \bij
  S$, which only allows one label of each sort.  However, it is
  possible to consider the category whose objects are finite sets $L$
  paired with a \emph{function} $\chi : L \to S$, as in $\Set/S$, but
  whose morphisms $(L_1,\chi_1) \to (L_2,\chi_2)$ are
  \emph{bijections} $\sigma : L_1 \bij L_2$ such that $\chi_2 \comp
  \sigma = \chi_1$.  In other words, the objects are finite sets with
  sorts assigned to their elements, and the morphisms are
  sort-preserving bijections. This category is indeed equivalent to
  $\B^S$.

  However, this construction only works because the objects of $\B$
  are sets; in the general case we must stick with $\Lab^S$.
\end{rem}

\begin{defn}
  For a finite set $S$, define \term{$S$-sorted ($\Lab$,$\Str$)-species}
  as functors \[ \Lab^S \to \Str. \]
\end{defn}

One can verify that taking $\Lab = \B$, $\Str = \Set$, and $S = \fin
k$ for some $k \in \N$, we recover exactly the definition of $k$-sort
species given by Bergeron \etal

The payoff is that we can now check that $\Lab^S$ inherits the
relevant properties from $\Lab$, and thus conclude that $(\Lab^S,
\Str)$-species inherit operations from $(\Lab,\Str)$-species.  Simply
unfolding definitions is then enough to describe the action of the
operations on $S$-sorted species.

\begin{itemize}
\item $\Lab^S$ inherits all the monoidal structure of $\Lab$, as seen
  in \pref{sec:lifting-monoids}.
\item $\Lab^S$ is a groupoid whenever $\Lab$ is.
\item If $\Lab$ is enriched over $\Str$ and $\Str$ has finite
  products, then $\Lab^S$ can be seen as enriched over $\Str$ as well:
  morphisms in $\Lab^S$ are represented by $S$-indexed products of
  morphisms in $\Lab$.
\item $\Lab^S$ is locally small whenever $\Lab$ is.
\item $\Str$ has coends over $\Lab^S$ as long as it has products and
  coends over $\Lab$, which we can argue as follows. Since $S$
  is discrete, everything in $\Lab^S$ naturally decomposes into
  discrete $S$-indexed collections.  For example, a morphism in
  $\Lab^S$ is isomorphic to an $S$-indexed collection of morphisms in
  $\Lab$, a functor $\Lab^S \to \Str$ is isomorphic to an $S$-indexed
  product of functors $\Lab \to \Str$, and so on.  Note that
  $(\Lab^S)^\op \times \Lab^S \iso (\Lab^\op)^S \times \Lab^S \iso
  (\Lab^\op \times \Lab)^S$, so a functor $T : (\Lab^S)^\op \times
  \Lab^S \to \Str$ can also be decomposed in this way.  In particular,
  this means that, as long as $\Str$ has $S$-indexed products, we may
  construct the coend $\coend L T(L,L)$ componentwise, that is, \[
  \coend L T(L,L) \defeq \prod_{s \in S} \coend K T_s(K,K), \] where
  $T_s$ denotes the $s$-component of the decomposition of $T$.  One
  can check that this defines a valid coend.
\item By a similar argument, $\fc {\Lab^S} \Str$ is enriched over
  itself as long as $\fc \Lab \Str$ is enriched over itself, and
  $\Str$ (and hence $\fc \Lab \Str$) has products.
\end{itemize}

We can thus instantiate the generic definitions to obtain notions of
sum, Cartesian, arithmetic, and partitional product, and
differentiation (along with corresponding eliminators) for $S$-sorted
species.  For example, the notion of partitional product obtained in
this way is precisely the definition given above.

One operation that we do \emph{not} obtain quite so easily is
composition: the generic definition relied on a definition of the
``$K$-fold partitional product'' $G^K$ where, in this case, $G :
\Lab^S \to \Str$ and $K \in \Lab^S$.  It is not \latin{a priori} clear
what should be meant by the $K$-fold partitional product of $G$ where
$K$ itself is a collection of labels of different sorts.  We could
ignore the sorts on $K$, using a monoidal structure on $\Lab$ to
reduce $K$ to an object of $\Lab$; for example, in $\fc {\B^S}{\Set}$,
given some collection of finite sets $K$, each corresponding to a
different sort, we can simply take their coproduct.  This results in a
notion of composition $F \comp G$ where we simply ignore the sorts on
the labels of $F$, replacing each with a (sorted) $G$-shape.  This
certainly yields a monoid on $\fc {\Lab^S}{\Str}$, but one that does
not really make use of the sorts at all.

The generalized notion of composition defined earlier, on the other
hand, is not a monoid on $\fc {\Lab^S}{\Str}$ (indeed, it is not a
monoid at all).  Instead, it has the type \[ - \comp - : (\fc
{\Lab^S}{\Str}) \to (\fc {\Lab^T} \Str)^S \to (\fc {\Lab^T}{\Str}). \]
This seems somewhat reminiscent of a relative monad
\citep{altenkirch2010monads}; exploring the connection is left to
future work.

\subsection{Recursive species}
\label{sec:recursive}

Multisort species make it possible to give a precise semantics to
recursively defined species, which have been used in examples
throughout this document.  Given a recursive equation of the
form \[ F = \dots F \dots, \] we can turn the right-hand side into a
two-sort species $\H(\X,\Y)$, with $\Y$ replacing the recursive
occurrences of $F$.  For example, the recursive equation \[ \Rose \iso
\X \cdot (\List \comp \Rose) \] corresponds to the two-sort species
$\H(\X,\Y) = \X \cdot (\List \comp \Y)$.  We then define $\Rose$ as
the least fixed point (if it exists) of $\H(\X,-)$, that is, a
solution to $\Rose \iso \H(\X,\Rose)$. The following theorem expresses
the conditions on $\H$ under which such fixed point solutions exist.
\begin{thm}[Implicit Species Theorem, \citep{joyal, bll}]
  Let $\H$ be a two-sort species satisfying
  \begin{itemize}
  \item $\H(\Zero,\Zero) \iso \Zero$
  \item $\displaystyle \frac{\partial \H}{\partial \Y}(\Zero, \Zero) \iso \Zero$
\end{itemize}
Then there exists a species $F$, unique up to isomorphism,
satisfying \[ F \iso \H(X,F), \] with $F(\Zero) \iso \Zero$.
\end{thm}

\begin{rem}
  Recall that the notation $\H(\Zero,\Zero) = \H \comp (\Zero,\Zero)$
  denotes the composition of the two-sort species $\H$ with the pair
  of one-sort species $(\Zero,\Zero)$.  These criteria are thus
  expressed in the form of species isomorphisms, but in this
  particular case they could equally well be expressed in terms of the
  action of $\H$ on empty label sets, \eg $\H(\varnothing,
  \varnothing) = \varnothing$.
\end{rem}

The proof essentially proceeds by constructing $F$ as the infinite
expansion \[ F = \H(\X, \H(\X, \H(\X, \dots))). \] The conditions on
$\H$ ensure that this is well-defined.  In particular, since
$(\partial \H / \partial \Y)$-shapes have a single hole in the place
of a $\Y$, which is the placeholder for recursive occurrences of $F$,
$\frac{\partial \H}{\partial \Y}(\Zero,\Zero) \iso \Zero$ means that
there are no $\H(\X,\Y)$-shapes consisting solely of (some constant
multiple of) a $\Y$.  Such shapes would allow a recursive step that
did not ``use'' any $\X$'s, resulting in infinitely large shapes of
size $0$.  For details of the proof, see \citet[\Sect 3.2]{bll}.  The
implicit species theorem can also be suitably generalized to systems
of mutually recursive equations; see \citet{bll} as well as
\citet{Pivoteau2012}.

Many common examples of recursively defined species, such as $\List =
\One + \X \cdot \List$, or $\Bin = \One + \X \cdot \Bin^2$, do not
actually satisfy the premises of the implicit species theorem, in
particular the requirement that $\H(\Zero,\Zero) \iso \Zero$.  In both
the above cases we instead have $\H(\Zero,\Zero) \iso \One$.  The
Implicit Species Theorem only gives sufficient, but not necessary,
conditions for well-foundedness; we would like to have a different
theorem that tells us when equations such those governing $\List$ and
$\Bin$ are well-founded. \citet{Pivoteau2012} prove quite a general
theorem which is applicable to this case, and is also applicable to
mutually recursive systems.  Its very generality somewhat obscures the
essential ideas, however, so we give a ``baby'' version of the theorem
here.

The basic idea can be seen by considering the case of $\List = \One +
\X \cdot \List$.  Decompose $\List$ as $\List = \One + \List_+$, so
$\List_+ = \X \cdot \List \iso \X \cdot (\One + \List_+)$.  Then
$\H(\X,\Y) = \X \cdot (\One + \Y)$ does satisfy the premises of the
Implicit Species Theorem, so $\List_+$ is well-defined, and hence so
is $\List = \One + \List_+$.  This approach is used, implicitly and in
an ad-hoc manner, by \citet{bll}; see, for example, Example 3.2.3 on
p. 195.  It also appears in a sketchy form in my Haskell Symposium
paper \citep{yorgey-2010-species}.

\begin{thm}[Implicit Species Theorem II]
  Let $\H(\X,\Y)$ be a two-sort species satisfying \[ \H(\Zero,\Y)
  \iso n, \] where $n \in \N$ represents the species $\underbrace{\One
    + \dots + \One}_n$ with $n$ shapes of size $0$.  Then there exists
  a species $F$, unique up to isomorphism, satisfying \[ F \iso
  \H(\X,F) \] with $F(\Zero) \iso n$.
\end{thm}

\begin{proof}
  Since $\H(\Zero,\Y) \iso n$, there is some two-sort species
  $\H_+$ such that $\H$ can be uniquely decomposed as
  \[ \H(\X,\Y) \iso n + \H_+(\X,\Y) \] (this follows from an analogue
  of the molecular decomposition theorem for multisort species).  Note
  that $\H_+(\Zero,\Y) \iso \Zero$ and $\partial \H/\partial \Y
  = \partial \H_+ / \partial \Y$.

  Moreover, $\H(\Zero,\Y) \iso n$ means that, other than the constant
  term $n$, every term of the molecular decomposition of $\H$ must
  contain a factor of $\X$.  In other words, $\H_+(\X,\Y) \iso \X
  \cdot \mcal G(\X,\Y)$ for some species $\mcal G$.  Thus we have
  $\frac{\partial \H}{\partial \Y}(\X,\Y) = \X \cdot \frac{\partial
    \mcal G}{\partial \Y}(\X,\Y)$, and in particular $\frac{\partial
    \H}{\partial \Y}(\Zero,\Y) \iso \Zero$ as well.

  Now define \[ \H_{n+}(\X,\Y) \defeq \H_+(\X,n + \Y). \] Note that
  \[ \frac{\partial \H_{n+}}{\partial \Y}(\X,\Y) = \frac{\partial
    \H_+}{\partial \Y}(\X,n+\Y) = \frac{\partial \H}{\partial
    \Y}(\X,n+\Y) \] (the first equality follows from the chain rule
  for differentiation).  Thus \[ \frac{\partial \H_{n+}}{\partial
    \Y}(\Zero,\Zero) = \frac{\partial \H}{\partial \Y}(\Zero, n) =
  \Zero. \]

  We also have \[ \H_{n+}(\Zero,\Zero) = \H_+(\Zero,n) \iso \Zero. \]
  Thus, $\H_{n+}$ satisfies the criteria for the Implicit Species
  Theorem, and we conclude there uniquely exists a species $F_+$
  satisfying $F_+ \iso \H_{n+}(\X,F_+)$, with $F_+(\Zero) \iso \Zero$.

  Finally, let $F \defeq n + F_+$, in which case
  \begin{align*}
    F &= n + F_+ \\
    &\iso n + \H_{n+}(\X, F_+) \\
    &= n + \H_+(\X, n + F_+) \\
    &\iso \H(\X, n + F_+) \\
    &= \H(\X,F).
  \end{align*}

  So $F = n + F_+$ is a solution to $F = \H(\X,F)$.  The uniqueness of
  $F$ follows from the uniqueness of $F_+$: if $F_1$ and $F_2$ are
  both solutions to $F = \H(\X,F)$, then they both decompose as $F_i =
  n + F_i^+$, and the $F_i^+$ both satisfy $F_i^+ =
  \H_{n+}(\X,F_i^+)$; hence $F_1^+ \iso F_2^+$ but then $F_1 \iso
  F_2$.
\end{proof}

\begin{rem}
  The condition $\H(\Zero,\Y) \iso n$, as opposed to the weaker
  condition $\H(\Zero,\Zero) \iso n$, is critical.  For example,
  consider the implicit equation \[ Q = \One + \X + Q^2. \] In this
  case $\H(\X,\Y) = \One + \X + \Y^2$ satisfies $\frac{\partial
    \H}{\partial \Y}(\Zero,\Zero) \iso \Zero$ and $\H(\Zero,\Zero)
  \iso \One$, but $\H(\Zero,\Y) \iso \One + \Y^2 \not \iso n$.  In
  fact, $Q$ is ill-defined: by always picking the $Q^2$ branch and
  never $\X$, and putting $\One$ at the leaves, one can construct
  infinitely many trees of size $0$.
\end{rem}


\section{$\L$-species}
\label{sec:L-species}

Consider the category $\L$ of linear orders and order-preserving
bijections (discussed previously in \pref{sec:manifestly-finite}).  An
\term{$L$-species} is defined as a functor $\L \to \Set$.  The theory
of $\L$-species is large and fascinating; for example, it allows one
to solve differential equations over species, and to define a notion
of intergration dual to differentiation.  More practically, it allows
modelling data structures with ordering constraints, such as binary
search trees and heaps.  Unfortunately there is not time or space to
include more on the theory here.  For now, we simply note that $(\fc
\L \Set)$ has many of the required properties:

\begin{itemize}
\item $\L$ is indeed monoidal; in fact, there are many interesting
  choices regarding how to combine linear orders. \later{expand on this?}
\item $\L$ is clearly a groupoid, locally small, and enriched over $\Set$.
\item $\Set$ is cocomplete and hence has coends over $\L$.
\item $(\fc \L \Set)$ is enriched over itself, for reasons similar to
  $(\fc \B \Set)$.
\item Since objects in $\L$ are finite sets, the indexed partitional
  product $G^K$ can be defined in exactly the same way as in the case
  of $\fc \B \Set$.
\end{itemize}

\section{Other species variants}
\label{sec:other-species-variants}

Many other examples of species variants appear in the literature. For
example:
\begin{itemize}
\item $\Vect$-valued species, \ie
  functors $\B \to \Vect$, which send finite sets of labels to
  \emph{vector spaces} of shapes. Joyal had these in mind from the
  beginning \citep{joyal86}, and they play a central role in
  more recent work as well (see, for example,
  \citet{aguiar2010monoidal}), though I do not yet have a good
  intuition for them.
\item $\Cat$-valued species, \ie functors $\B \to \Cat$ which send
  finite sets of labels to \emph{categories} of shapes. Intriguingly,
  in the case of groupoids in particular, a suitable notion of
  cardinality/Euler characteristic can be defined for categories
  \citep{baez2000finite}, allowing $\Cat$-valued species to be seen as
  a categorification of generating functions with positive
  \emph{rational} coefficients.
\item \citet{Fiore08} define a generalized notion of species,
  parameterized over arbitrary small categories $A$ and $B$, as
  functors in the category \[ \fc {\B A} {(\Hom {B^\op} \Set)}. \] $\B
  A$ is a generalization of $\B$ such that $\B \cat{1} \iso \B$; the
  objects are tuples of objects from $A$, labelled by the elements of
  some finite set from $\B$, and the morphisms permute the labelled
  $A$-objects according to some bijection on the finite set elements.
  They go on to show that this functor category has all the same
  important properties as $\fc \B \Set$.
\item \citet[\Sect 2.3]{bll} define a notion of \term{weighted species},
where each shape is assigned a \term{weight} from some polynomial ring
of weights $\W$.
%   For example, consider the weighted species of binary
% trees where the weight of each tree is its number of leaves.  This can
% be represented by the species $\Bin_\ell$,
% \begin{align*}
% \Bin_\ell &= \One + \Bin_{\ell+} \\
% \Bin_{\ell+} &= \X_\ell + \Sp{2} \cdot \X \cdot \Bin_{\ell+} + \X \cdot \Bin_{\ell+}^2.
% \end{align*}
% That is, a leaf-weighted tree is either empty, or a nonempty
% leaf-weighted tree; a nonempty leaf-weighted tree is either a single
% node with weight $\ell$ (here $\ell$ is a formal parameter
% representing the weight of a single leaf), or a node paired with a
% single nonempty leaf-weighted tree (in two ways---either as the left
% or right child), or a node paired with two nonempty leaf-weighted
% trees.  Given $\X_\ell(x) = \ell x$, one can compute the egf for
% $\Bin_\ell$ as \[ \Bin_\ell(x) = 1 + \ell x + 2\ell x^2 + (4 \ell +
% \ell^2) x^3 + (8\ell + 6 \ell^2) x^4 + \dots \] A term of the form
% $a_{i,n}\ell^i x^n$ indicates that there are $a_{i,n}$ labelled trees
% with $i$ leaves and size $n$.  One can verify that, for example, eight
% of the size-$4$ binary trees have only a single leaf (namely, the
% trees consisting of a single unbranching chain of nodes, with three
% binary choices of direction at the internal nodes for a total of $2^3
% = 8$), and six have two leaves.  Substituting $\ell = 1$ recovers the
% unweighted egf $\Bin(x) = 1 + 1 + 2x^2 + 5x^3 + 14x^4 + \dots$ In
% general, weighted species thus correspond to refinements of unweighted
% species.
\newcommand{\A}{\bbb{A}}
It seems that it should be possible to fit weighted species into this
framework as well, by considering a slice category $\Str/A$.
We can interpret objects of $\Str/A$ as objects of $\Str$ paired with
a weighting; morphisms in $\Str/A$ are thus weight-preserving
morphisms of $\Str$.  Traditional weighted species would then correspond to
functors $\fc \B {(\Set/\A)}$ for some polynomial ring $\A$; more
generally, one can add weighting to any species variant $\fc \Lab
\Str$ by passing to $\fc \Lab {(\Str/A)}$ for some appropriate choice
of $A \in \Str$.  Verifying this construction, in particular the
properties of $A$ which give rise to the appropriate species
operations on weighted species, is left to future work.

% The first thing to note is that $\Str/A$ inherits coproducts from
% $\Str$: given two weighted objects $(X, \omega_X)$ and $(Y,
% \omega_Y)$, we can uniquely construct a weighting $(X+Y, [\omega_X,
% \omega_Y])$:
% \[ \xymatrix{ X \ar[dr]_{\omega_X} \ar[r]^-{\iota_1} & X + Y
%   \ar[d]||{[\omega_X, \omega_Y]} & Y \ar[l]^-{\iota_2}
%   \ar[dl]^{\omega_Y} \\ & A & } \] To see that this is indeed the
% coproduct $(X,\omega_X) + (Y,\omega_Y)$ in $\Str/A$, \later{finish}

% Products in $\Str/A$ are pullbacks in $\Str$.  For example, given two
% weighted sets $(X, \omega_X)$ and $(Y, \omega_Y)$ in $\Set/A$, their
% categorical product in $\Set/A$ is the set $\{(x,y) \mid x \in X, y
% \in Y, \omega_X(x) = \omega_Y(y)\}$.  However, this is not a very
% useful notion of product in this context: intuitively, taking a
% product of weighted objects should yield a combined object with some
% sort of combined weight, instead of limiting us to cases where the
% weights match.

% Instead of requiring $\Str$ to have pullbacks, we can define a
% different sort of monoidal product on $\Str/A$ if we assume that
% $\Str$ has products and $A$ is a monoid object, that is, there exist
% morphisms $\eta : 1 \to A$ and $\mu : A \times A \to A$ satisfying
% \later{finish}.  In this case, we may define $(X, \omega_X) \otimes (Y,
% \omega_Y)$ by
% \[\xymatrixcolsep{4pc} \xymatrix{ X \times Y \ar[r]^-{\omega_X \times \omega_Y} & A
%   \times A \ar[r]^-\mu & A. } \]  The identity for $\otimes$ is given
% by $\eta$.
% %% xymatrix{ \singleton \ar[r]^{!} & 1 \ar[r]^\eta & A. } \]
% One can check that $\otimes$ inherits monoidal structure from
% $A$. \later{Finish this proof.}

% \later{Show that this gives the usual notion of weighted species.}

% \later{Show that this construction preserves the properties we care
%   about.}

% \later{Give some examples.}

\end{itemize}

In each case, one can verify the required properties and automatically
obtain definitions of the various operations.

