% -*- mode: LaTeX; compile-command: "mk" -*-

\documentclass{article}

%include polycode.fmt

\usepackage[outputdir=diagrams/]{diagrams-latex}

\usepackage{hyperref}
\usepackage[textsize=footnotesize,backgroundcolor=blue!20,linecolor=blue]{todonotes}
\usepackage{natbib}
\usepackage[all]{xy}

\usepackage{brent}
\usepackage{species}

\let\oldtodo\todo

\renewcommand{\todo}[1]{\oldtodo{#1}}

\title{Towards a Species-Based Theory of Data Types \\ {\small Dissertation Proposal}}
\author{Brent Yorgey}

\begin{document}

\maketitle

\tableofcontents

% \begin{itemize}
% \item What exact problem, issue, or question is this research concerned with?
% \item What limitations or failings of current understanding, knowledge, methods, or technologies does this research resolve?
% \item How significant is the problem, issue, or question?
% \item What new understanding, knowledge, methods, or technologies will this research generate? How does this address the purpose of the work?
% \item What experiments, studies, or prototypes will be produced to achieve the stated goal?
% \item How will achievement of the goal be demonstrated and the contribution of the work measured?
% \end{itemize}

\newpage

\section{Introduction}
\label{sec:intro}

The theory of \term{algebraic data types} XXX

\todo{Talk generically about the theory of algebraic data types.  Give
  some examples of the sorts of things we'd like to do.}

The theory of \term{combinatorial species} was first described in 1981
by Andr\'{e} Joyal~\cite{joyal} as a framework for understanding and
unifying much of \term{enumerative combinatorics}, the branch of
mathematics concerned with counting abstract structures.  Since then,
the theory has been explored and extended by many other
mathematicians. Like the theory of algebraic data types, it is also
concerned with describing structures compositionally, but is much more
general.

Upon gaining even a passing familiarity with both subjects, one cannot
help but be struck by obvious similarities.  However, there has yet to
be a comprehensive treatment of the precise connections between the
two. \todo{finish}

\subsection{Goals and Outline}
\label{sec:goals}

The overarching goal of the proposed research is to begin answering
the question:
\begin{quote}
  \textbf{What benefits can be derived from using the mathematical
    theory of species as a foundational theory of data structures in
    programming languages?}
\end{quote}
Answers to this question can take many forms.  What would a
programming language with ``species types'' look like?  Can we use
species theory as a tool for working with existing algebraic data
types?  Specifically, the contributions of the proposed research are
threefold:
\begin{enumerate}
\item I see myself primarily as a \emph{teacher} and secondarily as a
  researcher.  For this reason, a significant part of the proposed
  work will consist in presenting relevant parts of the theory of
  species in a way that is accessible to others in the programming
  languages community. The existing literature on species and recent
  related developments~\cite{BLL,keck} are relatively inaccessible to
  PL researchers, since they assume an extensive mathematical
  background and motivations that many PL researchers do not have.

  I have begun a series of blog posts \cite{blog posts} which will
  form the basis for this presentation; \pref{sec:species} contains an
  abridged version.

\item The second goal is to lay the theoretical groundwork for
  understanding species as a foundation for data types.  That is, if
  one wanted to design a programming language with ``species types''
  from the ground up, upon what theory could it be based?
  Section~\ref{sec:species-as-data-types} presents some preliminary
  results in this direction and lays out a roadmap for the remaining
  theory to be developed.

\item Third, the theory of species can be used to build practical
  tools for working with existing algebraic data types.  Towards this
  end I have developed a library, written in Haskell, for computing
  with species and facilitating application of the theory to existing
  data types.  Section~\ref{sec:species-library} explains the current
  features of the library and proposes new features to be added.

\end{enumerate}

\section{Combinatorial Species}
\label{sec:species}

\todo{talk about cardinality restriction somewhere?}
\todo{talk about algebraic laws}
\todo{mention identity elements for operations}

\todo{This isn't really the goal, at least it wasn't the original goal!}
The goal of species is to have a unified theory of \emph{structures}, or
\emph{containers}. By a \emph{structure} we mean some sort of ``shape''
containing \emph{locations} (or \emph{positions}). Here are two
different structures, each with eight locations:

\begin{figure}
\centering
\begin{diagram}[width=250]
import Diagrams
dia = (octo [0..7] |||||| strutX 4 |||||| tree # centerXY)
    # centerXY
    # pad 1.1
\end{diagram}
\caption{Example structures} \label{fig:example-structures}
\end{figure}

One thing that's important to get straight from the beginning is that
we are talking about structures with \emph{labeled locations}. The
\textbf{numbers in \pref{fig:example-structures} are \emph{not} data}
being stored in the structures, but \emph{names} or \emph{labels} for
the locations.  To talk about a \emph{data structure} (\emph{i.e.} a
structure filled with data), we must also specify a mapping from
locations to data, like $\{ 0 \mapsto \texttt{'s'}, 1 \mapsto
\texttt{'p'}, 2 \mapsto \texttt{'e'} \dots \}$, as shown
in~\pref{fig:shape-data}.  This will be made more precise
in~\pref{sec:species-types}.

\begin{figure}
\centering
\begin{diagram}[width=200]
import Diagrams
dia = shapePlusData # centerXY # pad 1.1

shapePlusData = octo [0..7]
  |||||| strutX 2
  |||||| (text "+" # fontSize 3 <> phantom (square 1 :: D R2))
  |||||| strutX 2
  |||||| mapping
  |||||| strutX 2

mapping = centerXY . vcat' with {sep = 0.2} . map mapsto $ zip [0..7] "species!"
mapsto (lab,x) = loc lab ||-|| arrow ||-|| elt x
x ||-|| y = x |||||| strutX 0.5 |||||| y
arrow = (hrule 3 # alignR # lw 0.03)
         <> (eqTriangle 0.5 # rotateBy (-1/4) # fc black # scaleY 0.7)
\end{diagram}
%$
\caption{Data structure = shape + data} \label{fig:shape-data}
\end{figure}

One useful intuition is to think of the labels as \emph{memory
  addresses}, which point off to some location where a data value is
stored. This intuition has some particularly interesting consequences
when it comes to operations like Cartesian product and functor
composition---explained in~\pref{sec:XXX}---since it gives us a way to
model sharing (albeit only in limited ways).

Why have labels at all? In the tree shown
in~\pref{fig:example-structures}, we can uniquely identify each
location by a path from the root of the tree, without referencing
labels at all. However, the other structure illustrates one reason why
labels are needed. The circle is supposed to indicate that the
structure has \emph{rotational symmetry}, so there would be no way to
uniquely refer to any location other than by giving them labels.

\subsection{Definition}
\label{sec:species-definition}

\begin{defn}
A \term{species} $F$ is a pair of mappings which \todo{cite Joyal + BLL}
\begin{itemize}
\item sends any finite set $U$ (of \term{labels}) to a finite set
  $F[U]$ (of \term{structures}), and
\item sends any bijection on finite sets $\sigma : U \bij V$ (a
  \term{relabeling}) to a function $F[\sigma] : F[U] \to F[V]$,
\end{itemize}
satisfying the following conditions:
\begin{itemize}
\item $F[id_U] = id_{F[U]}$, and
\item $F[\sigma \circ \tau] = F[\sigma] \circ F[\tau]$.
\end{itemize}

\end{defn}

Using the language of category theory, this definition can be pithily
summed up by saying that ``a species is a functor from $\B$ to
$\E$'', where $\B$ is the category of finite sets whose morphisms are
bijections, and $\E$ is the category of finite sets whose morphisms
are arbitrary (total) functions.

We call $F[U]$ the set of ``$F$-structures with
labels drawn from $U$'', or simply ``$F$-structures on $U$'', or even
(when $U$ is clear from context) just ``$F$-structures''.  $F[\sigma]$
is called the ``transport of $\sigma$ along $F$'', or sometimes the
``relabeling of $F$-structures by $\sigma$''.

The functoriality of relabeling means that the actual labels used
don't matter; we get ``the same structures'', up to relabeling, for
any label sets of the same size.  We might say that species are
\term{parametric} in the label sets of a given size. In particular,
$F$'s action on all label sets of size $n$ is determined by its action
on any particular such set: if $||U_1|| = ||U_2||$ and we know
$F[U_1]$, we can determine $F[U_2]$ by lifting an arbitrary
bijection between $U_1$ and $U_2$.  So we often take the finite set of
natural numbers $[n] = \{0, \dots, n-1\}$ as \emph{the}
canonical label set of size $n$, and write $F[n]$ (instead of
$F[[n]]$) for the set of $F$-structures built from this set.

% It's not hard to show that functors preserve isomorphisms, so although
% the definition only says that a species $F$ sends a bijection $\sigma
% : U \bij V$ to a \emph{function} $F[\sigma] : F[U] \to F[V]$, in fact,
% by functoriality every such function must be a bijection. \todo{is
%   this really important to say?}

\subsection{Building Species Algebraically}
\label{sec:building-species}

The formal definition of species is wonderfully simple, but working
directly with the definition in practice does not get one very far.
Instead, we use an algebraic theory that lets us compositionally build
a wide variety of species from a collection of primitive species and
operations on species. It's important to note that it does \emph{not}
allow us to build \emph{all} species, but it does allow us to build
many of the ones we care about.

\subsubsection{Primitives}
\label{sec:primitives}

We begin with a few primitive species, which form the building blocks
out of which more complex species can be composed.

\paragraph{Zero}
  The \emph{zero} or \emph{empty} species, denoted $\Zero$, is the
  unique species with no structures whatsoever; that is,
  \begin{align*}
  \Zero[U] &= \varnothing \\
  \Zero[\sigma : U \bij V] &= id_{\varnothing} : \Zero[U] \to \Zero[V].
  \end{align*}
  Of course, $\Zero$ is the identity element for
  the sum operation on species (defined in~\pref{sec:sum}).

\paragraph{One}
  The \emph{unit} species, denoted $\One$, is defined by
  \[ \One[U] =
  \begin{cases}
    \{\star\} & ||U|| = 0 \\
    \varnothing & \text{otherwise}
  \end{cases}
  \]
  That is, there is a unique $\One$-structure indexed by the empty
  set of labels, and no $\One$-structures with any positive number
  of labels. $\One$ lifts bijections in the obvious way, sending
  every bijection to the appropriate identity function.

  Some people initially find this definition surprising, expecting
  something like $\One[U] = \{ \star \}$ for all $U$ instead. That
  is indeed a valid species, and we will meet it below; but as I hope
  you will come to see, it doesn't deserve the name $\One$.

  Of course, one should also verify that this definition satisfies the
  requisite functoriality properties, which is not difficult.

  More abstractly, it's worth mentioning that $\One$ can be defined as
  $\mathbb{B}(\emptyset, -) : \mathbb{B} \to \mathbb{E}$, that is, the
  covariant hom-functor sending each finite set $U \in \mathbb{B}$ to
  the (finite) set of bijections $\emptyset \leftrightarrow U$
  \cite{yeh}. There is, of course, a unique bijection $\emptyset
  \leftrightarrow \emptyset$ and no bijections $\emptyset
  \leftrightarrow U$ for nonempty $U$, thus giving rise to the
  definition above.

  As expected, $\One$ is the identity element for the operation of
  species product, defined in~\pref{sec:product}.

%   \begin{figure}
%     \centering
%     \begin{diagram}[width=25]
% import Species

% dia = drawSpT (nd "1" []) # centerXY # pad 1.1
%     \end{diagram}
%     \caption{Abstract diagram for the unit species}
%     \label{fig:unit}
%   \end{figure}

\paragraph{Singleton}
  The \emph{singleton} species, denoted $\X$, is defined by
  \[ \X[U]
  = \begin{cases} U & ||U|| = 1 \\ \emptyset &
    \text{otherwise} \end{cases}
  \]
  with lifting of bijections defined in the evident manner. That is,
  there is a single $\X$-structure on a label set of size $1$
  (which we identify with the label itself, though we could have also
  defined $\X[U] = \{\star\}$ when $||U|| = 1$), and no
  $\X$-structures indexed by any other number of labels.
%   \begin{figure}
%     \centering
%     \begin{diagram}[width=100]
% import Species
% import Data.Tree

% dia = drawSpT (nd "X" [lf Leaf]) # centerXY # pad 1.1
%     \end{diagram}
%     \caption{Abstract diagram for the species of singletons}
%     \label{fig:singleton}
%   \end{figure}

  As with $\One$, we may equivalently define $\X$ as a
  hom-functor, namely $\X = \mathbb{B}(\{\star\}, -)$.

\paragraph{Bags}
  The species of \emph{bags}\footnote{The species literature calls
    this the species of \emph{sets}, but that's misleading to computer
    scientists, who expect the word ``set'' to imply that elements
    cannot be repeated.}, denoted $\Bag$, is defined by \[ \Bag[U] =
  \{U\}, \] that is, there is a single $\Bag$-structure on any set of
  labels $U$, which we usually identify with the set of labels itself
  (although we could equivalently define $\Bag[U] = \{\star\}$). The
  idea is that an $\Bag$-structure consists solely of a collection of
  labels, with no imposed ordering whatsoever.

As a summary, \pref{fig:prims} contains a graphic showing
$\Zero$-, $\One$-, $\X$-, and
$\Bag$-structures arranged by size (\emph{i.e.}, the size of the
underlying set of labels $U$): a dot indicates a single structure, and
the size of the label set increases as you move to the right.

\begin{figure}
  \centering
\begin{diagram}[width='200']
dot = circle 0.2 # fc black
row p     = hcat' with {sep=0.1} . map (drawOne . p) $ [0..10]
lRow x p  = (text [x] <> phantom (square 1 :: D R2)) |||||| strutX 0.5 |||||| row p
drawOne b = square 1 <> mconcat [dot||b]

dia =
  pad 1.1 .
  centerXY .
  vcat' with {sep = 0.3} $
  [ lRow '0' (const False)
  , lRow '1' (==0)
  , lRow 'X' (==1)
  , lRow 'E' (const True)
  ]
\end{diagram}
%$
  \caption{Primitive species}
  \label{fig:prims}
\end{figure}

\todo{There are others, in fact it is possible to give a complete
  classification.}

\subsubsection{Operations}
\label{sec:operations}

\todo{Say something general about operations here.}

\paragraph{Sum}
  The \term{sum} of two species $F + G$ is a disjoint
  (tagged) union: that is,
  \[ (F+G)[U] = F[U] + G[U], \] where the $+$ on the right denotes the
  coproduct of sets, \[ S + T = \{ \cons{inl}(s) \mid s \in S \} \cup \{
  \cons{inr}(t) \mid t \in T \}. \]  The transport of relabelings
  along a sum works in the evident manner,
  \begin{align*}
    (F+G)[\sigma](\inl(f)) &= \inl(F[\sigma](f)) \\
    (F+G)[\sigma](\inr(g)) &= \inr(G[\sigma](g)).
  \end{align*}

  $\Zero$ is the identity element for species sum,
  though only up to isomorphism (defined in~\pref{sec:unlabeled}).
  Intuitively, if one has either a $\Zero$-structure or an
  $F$-structure, one must in fact have an $F$-structure, since
  $\Zero$-structures do not exist.

  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import Species

theDia = struct 5 "F+G"
         ||||||
         strutX 1
         ||||||
         txt "="
         ||||||
         strutX 1
         ||||||
         ( struct 5 "F"
           ===
           txt "+"
           ===
           struct 5 "G"
         ) # centerY

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Species sum}
    \label{fig:sum}
  \end{figure}

  For example, structures of the species $\One + \X$ are either a unit
  structure (containing no labels) or a singleton structure
  containing a label, along with a tag indicating which.  This
  corresponds to the standard |Maybe| type in Haskell.

  The species $\One + \One$ has precisely two distinct structures,
  $\inl(\star)$ and $\inr(\star)$.  In general, there are $n$ distinct
  structures of the species $\underbrace{\One + \dots + \One}_n$,
  which we abbreviate as $\Sp{n}$.  Instead of writing things like
  $\inr(\inr(\inr(\inl(\star))))$ we often use the natural numbers $0
  \dots (n-1)$ as names for $\Sp{n}$-structures.

\paragraph{Product}
  The \term{product} of species is a bit more interesting.  One
  might na\"ively expect to have
  \[ (F \sprod G)[U] = F[U] \times G[U] \] where $\times$ denotes the
  Cartesian product of sets.  This is a sensible operation on species
  (to be discussed below) but not the most natural notion of product.
  This is because label sets are a generalization of \emph{size}, so an
  $(F \sprod G)$-structure indexed by $U$ should not contain two
  copies of every label.

  Instead, to make an $(F \sprod G)$-structure on $U$, we first
  \emph{split} $U$ into two disjoint subsets $U_1$ and $U_2$ (that is,
  $U_1 \cup U_2 = U$ and $U_1 \cap U_2 = \varnothing$), and then pair
  an $F$-structure on $U_1$ with a $G$-structure on $U_2$.  We get the
  set of \emph{all} $(F \sprod G)$-structures by doing this in all
  possible ways.  More formally, \[ (F \sprod G)[U] = \sum_{U_1 \uplus
    U_2 = U} F[U_1] \times G[U_2]. \]

  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import Species

theDia = struct 5 "F•G"
         ||||||
         strutX 1
         ||||||
         txt "="
         ||||||
         strutX 1
         ||||||
         ( struct 2 "F"
           ===
           strutY 0.2
           ===
           struct 3 "G"
         ) # centerY

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Species product}
    \label{fig:product}
  \end{figure}

  Here are a few examples:
  \begin{itemize}
  \item $\X \sprod \X$ \todo{finish}
  \item $\X \sprod \E$ \todo{pointed sets}
  \item $\E \sprod \E$ \todo{subsets}
  \end{itemize}

  Note that products of ``natural numbers'' (the species $2 = 1 + 1$
  and so on) work exactly as expected; in fact, we get an entire copy
  of the natural numbers $\N$ embedded inside species as a subring.

\paragraph{Composition}
The \term{composition} $F \comp G$ of two species $F$ and $G$,
intuitively, creates ``$F$-structures of $G$-structures''.  Formally,
to create an $(F \comp G)$-structure over a given set of labels $U$,
we first \emph{partition} $U$ into some number of nonempty subsets;
create a $G$-structure over each subset; then create an $F$-structure
\emph{over the resulting set of $G$-structures}.  Doing this in all
possible ways yields the complete set of $(F \comp
G)$-structures over $U$. Formally,
  \[ (F \comp G)[U] = \sum_{\pi \in \Par[U]} F[\pi] \times \prod_{p
    \in \pi} G[p]. \]
\pref{fig:composition} shows an abstract representation of the definition.

  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import Species

theDia = struct 6 "F∘G"
         ||||||
         strutX 1
         ||||||
         txt "="
         ||||||
         strutX 1
         ||||||
         drawSpT
         ( nd (txt "F")
           [ struct' 2 "G"
           , struct' 3 "G"
           , struct' 1 "G"
           ]
         )

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Species composition}
    \label{fig:composition}
  \end{figure}

\todo{examples}

\paragraph{Derivative}

The \term{derivative} $F'$ of a species $F$ is defined by \[ F'[U] =
F[U \union \{\star\}], \] where $\star$ is some new distinguished
label not already present in $U$.  The transport of bijections along
the derivative is defined as expected, leaving the distinguished
element alone and transporting the other labels.  

The derivative of container types is a notion already familiar to many
functional programmers through the work of McBride \todo{and others?}
\cite{XXX}: the derivative of a type is its type of ``one-hole
contexts''.  This can be seen in the definition above; $\star$
represents the distinguished ``hole'' in the $F$-structure.

  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import Species

theDia = struct 5 "F'"
         ||||||
         strutX 1
         ||||||
         txt "="
         ||||||
         strutX 1
         ||||||
         drawSpT
         ( nd (txt "F")
           [ lf Leaf
           , lf Leaf
           , lf Leaf
           , lf Hole
           , lf Leaf
           ]
         )

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Species differentiation}
    \label{fig:derivative}
  \end{figure}

\paragraph{Pointing}

  The \term{pointing} $F^{\bullet}$ of a species $F$ is a derived
  operation defined by \[ F^{\bullet} = \X \sprod F' \].
  \todo{write more}

  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import Species

theDia = struct 5 "F" -- XXX FIXME
         ||||||
         strutX 1
         ||||||
         txt "="
         ||||||
         strutX 1
         ||||||
         drawSpT
         ( nd (txt "F")
           [ lf Leaf
           , lf Leaf
           , lf Leaf
           , lf Point
           , lf Leaf
           ]
         )

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Species pointing}
    \label{fig:pointing}
  \end{figure}

\paragraph{Cartesian product}

The \term{Cartesian product} $F \times G$ of two species $F$ and $G$
is defined as \[ (F \times G)[U] = F[U] \times G[U], \] where the
$\times$ on the right denotes Cartesian product of sets.  This is in
fact the ``na\"ive'' definition of product that was discussed before.

Since we want to consider each label as occurring uniquely, we should
therefore think of an $(F \times G)$-structure as consisting of an
$F$-structure and a $G$-structure \emph{superimposed on the same set
  of labels}.  That is, we should think of labels as memory locations,
so a Cartesian product structure consists of two structures each
containing ``pointers'' to a set of shared memory locations.

\begin{figure}
  \centering
  \begin{diagram}[width=100]
dia = circle 2 -- XXX todo   
  \end{diagram}
  \caption{Cartesian product}
  \label{fig:cartesian}
\end{figure}
\todo{examples}

\paragraph{Functor composition}

The \term{functor composition} $F \fcomp G$ of two species $F$ and $G$
is given by their literal composition as functors: \[ (F \fcomp G)[U]
= F[G[U]]. \] An $(F \fcomp G)$-structure is thus an $F$-structure
over the set of \emph{all possible} $G$-structures on the labels $U$.

\todo{picture}

As an example, the species of simple directed graphs with labeled
vertices can be specified as \[ \mathcal{G} = (\E \sprod \E) \fcomp
(\X^2 \sprod \E), \] describing a graph as a subset ($\E \sprod \E$)
of the set of all ordered pairs chosen from the complete set of vertex
labels ($\X^2 \sprod \E$).

\subsubsection{Recursion}
\label{sec:recursion}

Of course, the theory of algebraic data types would not be very
interesting without recursion, and the same is true for the theory of
species.  Recursion is introduced by allowing \term{implicit
  equations} such as \[ \L = 1 + \X \sprod \L, \] giving them a
least-fixed-point interpretation.  There is a well-developed theory
explaining when such implicit equations have least-fixed-point
solutions which are unique (the implicit species theorem and its
generalizations~\cite{XXX}).

In general, we can allow arbitrary mutually recursive
systems of implicit equations \[ \overline{\F_i = \Phi_i(F_1, \dots,
  F_n)}^n. \]  For example, \todo{series-parallel graphs.}

\todo{say something about connection to $\mu$ operator, etc.?}

\subsection{Equipotence, Isomorphism, and Unlabeled Species}
\label{sec:unlabeled}

We say that two species $F$ and $G$ are \term{equipotent}, denoted $F
\equiv G$, when there exists a family of bijections $\phi_U : F[U]
\bij G[U]$, that is, there are the same number of $F$- and
$G$-structures of each size.  Although this notion is occasionally
useful, it is rather weak.  More useful is the notion of species
\term{isomorphism}: $F$ and $G$ are isomorphic, denoted $F \cong G$,
precisely when they are \term{naturally isomorphic} as functors; that
is, when there exists a family of bijections \[ \phi_U : F[U] \bij
G[U] \] which moreover commute with relabeling. By ``commute with
relabeling'', we mean that for all $\sigma : U \bij V, \phi_V \comp
F[\sigma] = G[\sigma] \comp \phi_U$, as illustrated by the commutative
diagram in~\pref{fig:nat-iso}.
\begin{figure}
\centerline{
\xymatrix{
F[U] \ar[r]^{\phi_U} \ar[d]_{F[\sigma]} & G[U] \ar[d]^{G[\sigma]} \\
F[V] \ar[r]_{\phi_V} & G[V]
}
}
  \caption{Natural isomorphism between species}
  \label{fig:nat-iso}
\end{figure}
For example, $X + (X + X)$ and $3X$ are isomorphic, as witnessed by
the mapping
\begin{align*}
  \inl(u) &\bij (0, u) \\
  \inr(\inl(u)) &\bij (1,u) \\
  \inr(\inr(u)) &\bij (2,u)
\end{align*}
\todo{is there a more perspicuous way to write the above?}
\todo{explain why it commutes with relabeling}

\todo{write about other algebraic laws that hold up to isomorphism}

As an example of species which are equipotent but not isomorphic,
consider the species $\L$ of linear orderings (\ie\ lists) and the
species $\S$ of permutations.  It is well-known that the number of
linear orderings and the number of permutations of $n$ distinct labels
are both $n!$.  However, there is no way to set up a family of
bijections that respects relabeling: any list can be sent to any other
by an appropriate relabeling, but there is no way to send (say) a
permutation with two cycles to a permutation with three cycles just by
relabeling.

\todo{draw picture here of relabeling lists and cycles}

We say that two \emph{structures} of a given species are isomorphic when
there exists a relabeling taking one to the other.  That is, $f_1 \in
F[U]$ and $f_2 \in F[V]$ are isomorphic iff there is some $\sigma : U
\bij V$ such that $F[\sigma](f_1) = f_2$.

\todo{define unlabelled species, with pictures, etc.}
\todo{stuff about regular vs. other species.}

\todo{non-regular, molecular species.}

\subsection{Generating Functions}
\label{sec:gen-funcs}

One of the most beautiful aspects of the algebraic theory of
species---from which it derives much of its power---is its
connection to various types of \term{generating functions}.

In the simplest case, we can associate to each species $F$ an
\term{exponential generating function} (egf) $F(x)$, defined as \[ F(x)
= \sum_{n \geq 0} f_n \frac{x^n}{n!}, \] where $f_n = ||F[n]||$ is the
number of $F$-structures on a label set of size $n$. (Note that we
usually want to think of $F(x)$ as just a \emph{formal power series},
that is, an element of the ring $\Z[[X]]$, and not as a function $\R
\to \R$.  For example, we need not concern ourselves with issues of
convergence.)

As an example, since there is a single \Sp{E}-structure on every label
set, we have \[ \Bag(x) = \sum_{n \geq 0} \frac{x^n}{n!} = 1 + x +
\frac x {2!} + \frac x {3!} + \dots = e^x. \]

Going through the rest of the primitives, it is not hard to verify that
\begin{align*}
  \Zero(x) &= 0 \\
  \One(x)  &= 1 \\
  \X(x)    &= x. \\
\end{align*}

Since the number of $(F+G)$-structures on a given label set is the sum
of the number of $F$-structures and the number of $G$-structures, that
is, $||(F+G)[n]|| = ||F[n]|| + ||G[n]||$, we have \[ (F+G)(x) =
\sum_{n \geq 0} (f_n + g_n) \frac{x^n}{n!} = F(x) + G(x). \]

We also have $(FG)(x) = F(x)G(x)$:
\begin{sproof}
  \stmt{F(x)G(x)}
  \reason{=}{definition}
  \stmt{\displaystyle \left(\sum_{n \geq 0} f_n
      \frac{x^n}{n!}\right) \left( \sum_{n \geq 0} g_n \frac{x^n}{n!} \right)}
  \reason{=}{distribute}
  \stmt{\displaystyle \sum_{\substack{n \geq 0 \\ 0 \leq k \leq n}}
      \frac{f_k}{k!} \frac{g_{n-k}}{(n-k)!} x^n} \\
  \reason{=}{definition of $\binom{n}{k}$}
  \stmt{\displaystyle \sum_{n \geq 0} \left( \sum_{0 \leq k \leq n}
      \binom{n}{k} f_k g_{n-k} \right) \frac{x^n}{n!}}
\end{sproof}
and we can confirm that the number of $FG$-structures on $n$ labels
(that is, pairs of $F$- and $G$-structures with total size $n$) is
indeed equal to \[ \sum_{0 \leq k \leq n} \binom{n}{k} f_k g_{n-k}. \]
For each $0 \leq k \leq n$, we can distribute $k$ of the labels to the
left side of the pair (and the remaining $n - k$ to the right) in
$\binom n k$ ways; we then have $f_k$ choices of an $F$-structure to
be the first element of the pair, and $g_{n-k}$ choices of
$G$-structure for the second.

In fact, it is also the case that
\begin{itemize}
\item $(F\comp G)(x) = F(G(x))$
\item $(F')(x) = (F(x))'$
\end{itemize}

A proof of the equation for derivative is straightforward.  The proof
for composition is omitted from this proposal, but follows a similar
(if somewhat more complicated) pattern as the proof for products
above.  There are similar equations for other operations such as
Cartesian product and functor composition.

To each species we can also associate an \term{ordinary generating
  function} (ogf), \[ \unl{F}(x) = \sum_{n \geq 0} \unl{f}_n x^n, \]
where $\unl{f}_n$ denotes the number of \emph{unlabeled}
$F$-structures (that is, the number of equivalence classes of
isomorphic $F$-structures).  The mapping from species to ogfs
preserves addition, multiplication, and derivative, just as for egfs,
but does \emph{not} preserve composition.  To compute the ogf for a
composed species we can use yet a third type of generating function,
the \term{cycle index series}, which tracks not just sizes of
structures but also information about their symmetry.  The details are
beyond the scope of this proposal, but \todo{finish}

\section{Species as Data Types}
\label{sec:species-as-data-types}

% In particular, we want to extend the theory of algebraic data types to
% a theory of \emph{species data types}. A programming language with
% support for species would raise the level of abstraction available to
% programmers, making it easier for them to express programs that are
% closer to what they really \emph{mean}, instead of being forced to
% ``encode'' their intended meaning using the constructs available to
% them.

Although it seems ``obvious'' that there is a deep connection between
the theory of species and the theory of algebraic data types, care
must be taken to state the precise nature of the relationship.

\subsection{Species types}
\label{sec:species-types}

Species, as defined, are not data types; rather, they represent
labeled shapes.  If we want to treat them as representing data types,
the relationship between species and their corresponding data types
must be defined precisely.

As explained previously, the basic idea is to represent a data
structure as a labeled structure \emph{paired with} a mapping from
labels to values.  However, we must also take care to quotient out by
the labels, since the same data structure may be represented using
many different labelings.

To see how these ideas work, we begin with the very simple universe of
species expressions shown in~\pref{fig:universe}.  For now we have
only regular species and no recursion.

\begin{figure}
  \centering
  \begin{align*}
    S & ::= \Zero \\
      & \mid \One \\
    & \mid \X \\
    & \mid S + S \\
    & \mid S \sprod S \\
    & \mid S \comp S
  \end{align*}
  \caption{A simple universe of species expressions}
  \label{fig:universe}
\end{figure}

\newcommand{\spe}[1]{\ensuremath{\langle #1 \rangle}}

We can interpret these expressions as species, that is, as functors
$\B \to \E$ as described in previous sections.  We will write
$\spe{S}$ to denote the functor $\B \to \E$ corresponding to the
species expression $S$.  But we can also straightforwardly interpret
them as type constructors, as shown in \pref{fig:type-constructors}.

\newcommand{\ty}[2]{\ensuremath{\llbracket #1 \rrbracket}\ #2}

\begin{figure}
  \centering
  \begin{align*}
  \ty{\Zero} A &= 0 \\
  \ty{\One} A &= 1 \\
  \ty{\X} A &= A \\
  \ty{F+G} A &= \ty{F} A + \ty{G} A \\
  \ty{F \sprod G} A &= \ty F A \times \ty G A \\
  \ty{F \comp G} A &= \ty F {(\ty G A)}
  \end{align*}
  \caption{Interpreting species expressions as type constructors}
  \label{fig:type-constructors}
\end{figure}

What is the precise relationship between $\spe{S}$ and $\ty{S}{}$ for
a given expression $S$?

\todo{more explanation leading up to this}

\todo{define $\sim_S$}

\begin{thm}
  For all species expressions $S$,
  \[ \ty{S} A \cong \left( \sum_U \spe{S}[U] \times (U \to A) \right)
  / \sim_S. \]
\end{thm}

\begin{proof}
  \todo{write me}
\end{proof}

Also,
\begin{lem}
  \[ \left( \sum_U \spe{S}[U] \times (U \to A) \right)
  / \sim_S \cong \left( \sum_{n \in \N} \spe{S}[n] \times A^n \right)
  / \sim_S \]
\end{lem}

As a corollary, \[ \ty{S} A \cong \left( \sum_{n \in \N} \spe{S}[n]
  \times A^n \right) / \sim_S, \] which intuitively states that
\todo{explain}.

\todo{who cares? Why is this relevant?}

\todo{write about next directions to take this. Multisort, nonregular,
  recursive.}

\subsection{Eliminators for species types}
\label{sec:eliminators}



\section{The \pkg{species} library}
\label{sec:species-library}

In previous work, I created a Haskell library\footnote{Available from
  Hackage at \url{http://hackage.haskell.org/package/species}} for working with
combinatorial species~\cite{yorgey}.  Its features include
\begin{itemize}
\item computing egf, ogf, and cycle index series for arbitrary species
\item enumerating all structures of a given species ordered by size
\item automatically derive species corresponding to user-defined data types
\end{itemize}

However, there are many features that could yet be added. \todo{talk
  about what some of these features are.}

% \section{Enumerating Unlabeled Structures}
% \label{sec:enumerating}

% \section{Doing Other Stuff}
%
% \todo{Need to figure out what other stuff to propose!  Views? Sharing?
%   L-species? Virtual species? Species + infinity?  Enumerating
%   unlabeled structures?  See NSF proposal for ideas, of course.}

\section{Related Work}
\label{sec:related}

The idea of decomposing data structures as shapes with locations
combined with data is not unique to species. In the computer science
community, the idea goes back, I think, to Jay and Cockett (1994) in
their work on ``shapely types'' (their ``locations'' are always
essentially natural numbers, since they work in terms of shapes and
\emph{lists} of data) and more recently Abbott, Altenkirch, and Ghani
(2003) with their definition of ``containers'' (which, like the theory
of species, has a much more general notion of locations). However, it
should be noted that the literature on species never actually talks
about mappings from labels to data: combinatorialists don't care about
data structures, they only care about structures! \todo{format this
  properly} \todo{also mention references from JG}


point out connections between the theory of
species and computer science~\cite{FlSa95,
  FlajoletSalvyZimmermann1989a}.

Keck work.

\section{Timeline and Conclusion}
\label{sec:timeline}



\end{document}
