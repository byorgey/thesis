%% -*- mode: LaTeX; compile-command: "mk" -*-

%include thesis.fmt

\chapter{Combinatorial species}
\label{chap:species}

\todo{Gentler introduction, with some more intuition (and examples?),
  explanation of the diagrams, and pointers to further reading.}

Species are defined as functors $\B \to \Set$ \citep{bll}.
Intuitively, the action of a species on objects takes a finite set of
``labels'' to a set of ``structures''; the action on morphisms
requires the action on objects to be ``invariant under relabelling''.

This is a simple and convenient definition, but there are several
reasons that compel us to generalize it.  First, \B and \Set enjoy
many special properties as categories (for example, \Set is
cartesian closed, has all limits and colimits, and so on).  It is
enlightening to see precisely which properties are required in which
situations, and we miss this entirely if we start with the kitchen
sink.

More subtly, we wish to work in a constructive, computational setting,
and the specific categories \B and \Set are
inappropriate. \todo{reference stuff from finiteness section
  previously.}  We will wish to work with more computationally
concrete categories based in type theory, such as $\BT$, but in order
to do so we need to show that they have the right properties.

\todo{Note we will often use the intuition of ``sets of labels'' but
  of course in more general settings the objects of the category
  $\Lab$ might not ``have elements'' at all. More generally we can
  just think of structures indexed by objects of $\Lab$, rather that
  structures ``containing labels''.}

\section{Species from scratch}
\label{sec:species-scratch}

The idea is to start ``from scratch'' and build up a generic notion of
species which supports the operations we want.  Along the way, we will
also get a much clearer picture of where the operations ``come from''.

\todo{cite ``Operads of J.P. May'', ``Cartesian Closed Bicategory of
  Generalised Species of Structure'', ``Monoidal Functors, Species, and
  Hopf Algebras''}

We begin by considering functor categories in general.  Given two
categories $\Lab$ and $\Str$, what can we say about functors $\Lab \to
\Str$, and more generally about the functor category $[\Lab, \Str]$?
Of course, there is no point in calling functors $\Lab \to \Str$
``species'' for just any old categories $\Lab$ and $\Str$.  But what
properties must $\Lab$ and $\Str$ possess to make this interesting and
worthwhile?

\todo{should talk about motivation from memory locations and structures.}

In each of the following sections we will discuss some specific
constructions on species (considered as functors $\B \to \Set$), and
then generalize to arbitrary functor categories to see what properties
are needed in order to define them---\ie\ where the constructions
``come from''---and give some specific examples.

\section{Sum}
\label{sec:sum}

One of the simplest operations on species is the \emph{sum} of two
species.  Given species $F, G : \B \to \Set$, we may form their sum $F
+ G$, defined on objects by \[ (F + G)\ L \defeq F\ L + G\ L, \] where
the $+$ on the right hand side denotes disjoint union of sets.  That
is, a labelled $(F + G)$-shape is either a labelled $F$-shape or a
labelled $G$-shape (\pref{fig:sum}). \todo{Say something about action
  on arrows/functoriality.}

  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import SpeciesDiagrams

theDia
  = hcat' (with & sep .~ 1)
    [ struct 5 "F+G"
    , text' 1 "="
    , vcat
      [ struct 5 "F"
      , text' 1 "+"
      , struct 5 "G"
      ]
      # centerY
    ]

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Species sum}
    \label{fig:sum}
  \end{figure}

We may also define the \term{zero} or \term{empty} species, $\Zero$,
as the unique species with no shapes whatsoever, that is,

\begin{equation*}
  \Zero\ L \defeq \varnothing
\end{equation*}

% As a simple example, the species $\One + \X$ corresponds to the
% familiar |Maybe| type from Haskell, with $\lab{\inl} \lab{\One}$
% playing the role of |Nothing| and $\lab{\inr} \comp \lab{\cons{x}}$
% playing the role of |Just|.  Note that $\LStr {\One + \X} L A$ is
% only inhabited for certain $L$ (those of size $0$ or $1$), and moreover that
% this size restriction determines the possible structure of an
% inhabitant.
%
% Note, can't include the above if we haven't talked about 1 or X
% yet.  And I now think a better way to organize things is by talking
% about each fundamental monoidal construction along with its unit.
% As for introduction forms, it's pretty trivial.

It's not hard to check that $(+,\Zero)$ forms a commutative monoid
structure on species (up to isomorphism).  Stepping back a bit, we can
see that this monoidal structure on species arises from a
corresponding monoidal structure on sets in an entirely
straightforward way: the sum of two functors is defined as the
pointwise sum of their outputs, and likewise \Zero, the identity for
the sum of species, is defined as the functor which constantly, \ie
pointwise, returns $\varnothing$, the identity for the sum of sets.

This generalizes straightforwardly: any monoidal structure on a
category $\Str$ lifts pointwise to a corresponding monoidal structure
on the functor category $[\Lab, \Str]$. \todo{find a reference for
  proof?} (Note that this is exactly the same idea as the standard
Haskell type class instance
\begin{spec}
instance Monoid a => Monoid (e -> a) where
  mempty         = \ _ -> mempty
  f `mappend` g  = \a -> f a `mappend` g a
\end{spec}
but quite a bit more general.)  Moreover, this lifting preserves
commutativity, and products and coproducts on a category $\Str$ lift
to products and coproducts on $[\Lab, \Str]$.  Since $(+,\varnothing)$
is a coproduct structure on $\Set$, it follows that $(+, \Zero)$ is in
fact a coproduct structure on the category of species.

\todo{Give some examples other than $\B \to \Set$.  $\PT \to
  \Type$. Simpler things.}

\section{Cartesian/Hadamard product}
\label{sec:cartesian}

Disjoint union is not the only monoidal structure on $\Set$. In
addition to coproducts $\Set$ also has products, where the product of
two sets $S$ and $T$ is given by the Cartesian product, $S \times T =
\{ (s,t) \mid s \in S, t \in T \}$, with any one-element set as the
identity (for convenience, we may suppose there is some canonical
choice of one-element set, $\{\star\}$).
\begin{defn}
  By the discussion of the previous section, this automatically lifts
  to a pointwise product structure on species, known as the
  \term{Cartesian} or \term{Hadamard product}: \[ (F \times G)\ L = F\
  L \times G\ L. \]
\end{defn}
In the same way that an $(F + G)$-shape is either an
$F$-shape \emph{or} a $G$-shape on a given set of labels, an $(F
\times G)$-shape is both an $F$-shape \emph{and} a $G$-shape, on
\emph{the same set of labels} (\pref{fig:Cartesian-product}).
\begin{figure}
  \centering
  \todo{Make a diagram.}
  \caption{Cartesian species product}
  \label{fig:Cartesian-product}
\end{figure}

\begin{defn}
  Lifting the identity element pointwise gives the species \[ \E\ L =
  \{\star\}, \] usually called the \term{species of sets}, which is the
  identity for Cartesian product of species.
\end{defn}
\begin{rem}
  It is called the species of sets since there is exactly one
  structure on any set of labels, which can intuitively be thought of
  as the set of labels itself, with no additional structure.  In fact,
  since all one-element sets are isomorphic, we may as well define \[
  \E\ L = \{L\}. \]
\end{rem}

Cartesian product can produce structures with multiple copies of each
label.  Insofar as we view labels as pointers or names for memory
locations, this allows \emph{explicitly} modelling value-level
sharing---this is explored more in \pref{sec:sharing}.

Of course, since Cartesian product is the categorical product in \Set,
Cartesian/Hadamard product is also the product in the category of
species.  Interestingly, there is a different notion of species
product (though not a categorical product) which is in some sense more
natural/useful than Cartesian product, even though it is more
complicated; it will be explored in the next section.

In addition to having products, \Set is Cartesian closed. However,
lifting does not necessarily preserve closedness. \todo{Is this right?
  If so, why not?} In particular, the category $[\B, \Set]$ of species
is not Cartesian closed---we cannot (in general) model function types
with species. \todo{Though we can in some specific situations---see
  ...?}

\todo{give some examples with other categories.}

\todo{\Set is distributive, in the sense that the canonical morphism
  $X \times Y + X \times Z \to X \times (Y + Z)$ is an isomorphism.
  Is $[\B, \Set]$ distributive in the same way?  If so, does lifting
  monoids always preserve distributivity? Answers: yes, and yes.}

\section{Partitional/Cauchy product}
\label{sec:product}

There is another notion of product for species, the \term{partitional}
or \term{Cauchy} product, which is more generally useful than
Cartesian product, even though it is much more complex to define.  In
particular, when species are extended to labelled structures
(\pref{chap:labelled}) it is the partitional product, rather than
Cartesian, which gives rise to the usual notion of product on
algebraic data types.  For this reason partitional product is
often simply referred to as ``product'', without any modifier,
although as we have seen it is Cartesian product, rather than
partitional product, which is actually a categorical product.

\begin{defn}
  The partitional product $F \sprod G$ of two species $F$ and $G$
  consists of paired $F$- and $G$-shapes, but with a twist: instead of
  being replicated, as in Cartesian product, the labels are
  \emph{partitioned} between the two shapes (\pref{fig:product}).
\end{defn}
  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import SpeciesDiagrams

theDia
  = hcat' (with & sep .~ 1)
    [ struct 5 "F•G"
    , text' 1 "="
    , vcat' (with & sep .~ 0.2)
      [ struct 2 "F"
      , struct 3 "G"
      ]
      # centerY
    ]

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Partitional species product}
    \label{fig:product}
  \end{figure}

%%% XXX remove me
\newcommand{\under}[1]{\floor{#1}}
\newcommand{\lift}[1]{\ceil{#1}}
\newcommand{\lab}[1]{\langle #1 \rangle}
\newcommand{\LStr}[3]{#1 #2 #3}

\begin{equation*}
  (F \sprod G)\ L = \sum_{L_1 \uplus L_2 = L} F\ L_1 \times G\ L_2
\end{equation*}
The intuition behind partitioning the labels in this way is that each
label represents a unique ``location'' which can hold a data value, so
the locations in the two paired shapes should be disjoint.

Generalizing partitional product over arbitrary functor categories is
much more complex than generalizing sum and Cartesian product, and
requires turning to a construction known as \term{Day convolution}.

\section{Day convolution}
\label{sec:day-convolution}

The essential idea of Day convolution, first described by Brian
Day~\cite{day-convolution}, is to construct a monoidal structure on a
functor category $[\Lab, \Str]$ out of a monoidal structure on the
\emph{domain} category $\Lab$.  In particular, Day convolution
requires
\begin{itemize}
\item a monoidal structure $\oplus$ on $\Lab$;
\item that $\Lab$ be \emph{enriched over} $\Str$, \ie there is a way
  to interpret morphisms in $\Lab$ as objects in $\Str$;
\item a symmetric monoidal structure $\otimes$ on $\Str$;
\item that $\Str$ be \todo{(finitely?)} cocomplete, and in particular
  have coends.
\end{itemize}

\bay{Maybe don't use same letter $L$ for generic definition as we do for $L
  \in \B$?}
\begin{defn}
  Given the above conditions, the Day convolution product of $F, G \in
  [\Lab, \Str]$ is given by \[ (F \oast G)\ L = \int^{L_1, L_2} F\ L_1
  \otimes G\ L_2 \otimes \Lab(L_1 \oplus L_2, L). \]
\end{defn}
\todo{Make sure I got all of this right.}

\todo{Explain.  Give some intuition.}

\todo{Instantiate with $\B$ and $\Set$, show they have the right
  properties, and show where partitional product comes from.}

\todo{Turn the following paragraph into an example with different
  categories}

Another
good way to gain intuition is to imagine indexing species not by label
types, but by natural number sizes.  Then it is easy to see that we
would have \[ (F \sprod G)_n \defeq \sum_{n_1, n_2 : \N} (n_1 + n_2 = n)
\times F_{n_1} \times G_{n_2}, \] that is, an $(F \sprod G)$-shape of
size $n$ consists of an $F$-shape of size $n_1$ and a $G$-shape of
size $n_2$, where $n_1 + n_2 = n$.  Indexing by labels is a
generalization (a \emph{categorification}, in fact) of this
size-indexing scheme, where we replace natural numbers with finite
types, addition with coproduct, and multiplication with product.

\todo{Do example with $\P$.}

\todo{Show that $\BT/\PT$ along with \Type\ have the right properties,
instantiate framework to show how it comes out.}

\section{Arithmetic product}
\label{sec:arithmetic-product}

There is another monoidal structure on $\B$ (and similarly on $\P$ and
$\N$) corresponding to the \emph{product} of sets/natural numbers.
What happens if we instantiate the framework of Day convolution with
this product-like monoidal structure instead of the coproduct-like
structure used to define partitional product?

\bay{How can we say that we are using ``the same'' ``product-like''
  monoidal structure in all these different categories?  Are they
  related by monoidal functors?}

Beginning with a simple example, \todo{example using $\N$}

Using the standard formulation of the category of species as $[\B,
\Set]$, we get \todo{finish. This is called \term{arithmetic product},
and was recently described by (XXX cite), although they say nothing
about Day convolution.}

\todo{pictures, intuition.}

\section{Composition}
\label{sec:composition}

\section{Differentiation}
\label{sec:differentiation}

\section{Multisort species}
\label{sec:multisort}

\todo{General introduction to the concept of multisort species}

\newcommand{\lcat}[1]{#1^*}
\newcommand{\emptylist}{[\,]}

\begin{defn}
  Given a category $\C$, define the category $\lcat{\C}$ as follows.
  \begin{itemize}
  \item The objects of $\lcat{\C}$ are finite (possibly empty) lists
    $[C_1, C_2, C_3, \dots]$ of objects from $\C$.
  \item The morphisms from $[C_1, \dots, C_n]$ to $[D_1, \dots, D_n]$
    are lists of morphisms $[f_1, \dots, f_n]$ with $f_i : C_i \to
    D_i$.  Note there are no morphisms $[C_1, \dots, C_m] \to [D_1,
    \dots, D_n]$ when $m \neq n$.
  \end{itemize}
\end{defn}

\todo{Need to add more text here motivating these definitions and
  propositions.  Will go much better once I get a better sense of
  where this all is headed exactly, and which of these properties we
  need and why.}

\begin{lem}
  For any category $\C$, $\lcat{\C}$ is monoidal with list
  concatenation |++| as the tensor product and the empty list as
  the identity object.
\end{lem}

\renewcommand{\Cat}{\cat{Cat}}

\todo{Note that $\lcat{-}$ is a functor $\Cat \to \Cat$? (Is it?)}

\begin{defn}
  Define the embedding functor $e : \C \to \lcat{\C}$ which sends $C$
  to the singleton list $[C]$ and $f$ to $[f]$.
\end{defn}

\begin{prop}
  $e$ is full and faithful.
\end{prop}

\begin{defn}
  If $(\C, \otimes, I)$ is a monoidal category, we may define a
  functor $F^\otimes : \lcat{\C} \to \C$ by:
  \begin{itemize}
  \item $F^\otimes\ \emptylist = I$
  \item $F^\otimes\ [C_1, \dots, C_n] = C_1 \otimes \dots \otimes C_n$
  \end{itemize}
  and similarly for morphisms.
\end{defn}

\begin{prop}
  $F^\otimes$ is a (strict) monoidal functor.
  \begin{proof}
    $F^\otimes\ \emptylist = I$ by definition, and it is easy to check
    that $F^\otimes\ (\ell_1 \plus \ell_2) = F^\otimes\ \ell_1 \otimes
    F^\otimes\ \ell_2$.
  \end{proof}
\end{prop}

\begin{rem}
  Note that $F^\otimes$ is not, in general, an isomorphism.  In
  particular, there may exist morphisms $C_1 \otimes \dots \otimes C_n
  \to D_1 \otimes \dots \otimes D_n$ which do not arise as a tensorial
  product of morphisms $f_i : C_i \to D_i$.  For example, in $(\Set,
  +)$ we may define \todo{finish me}.
\end{rem}

Given a functor category of generalized species $[\Lab, \Str]$, we may
now form the category $[\lcat{\Lab}, \Str]$ of generalized multisort
species.  In particular, $[\lcat{\B}, \Set]$ corresponds exactly to
the notion of multisort species defined in \citet{bll}.

\todo{Note conditions under which this preserves the structure we care
  about.  Need $\lcat{\Lab}$ to still be enriched over $\Str$.  We
  have shown above that $\lcat{\Lab}$ preserves relevant monoidal
  structure.  Hmm\dots multisort corresponds particularly to
  interpreting lists using coproduct from underlying category\dots
  where does that come from?}

\section{Weighted species}
\label{sec:weighted}

\section{Virtual species}
\label{sec:virtual}

