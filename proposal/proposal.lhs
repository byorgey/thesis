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

\renewcommand{\todo}[1]{\oldtodo[inline]{#1}}

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

\todo{Talk generically about the theory of algebraic data types.  Give
  some examples of the sorts of things we'd like to do.}

\subsection{Goals and Outline}
\label{sec:goals}

The theory of \term{combinatorial species} was invented in 1981 by
Andr\'{e} Joyal~\cite{joyal} as a framework for understanding and
unifying much of enumerative combinatorics.  Since then, the theory
has been explored and extended by many other mathematicians. Like the
theory of algebraic data types, it is also concerned with describing
structures compositionally, but is much more general.

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
types?  More specifically, the concrete goals of the proposed research
are threefold:
\begin{enumerate}
\item I see myself primarily as a \emph{teacher} and secondarily as a
  researcher.  For this reason, a significant part of the proposed
  work will consist in presenting relevant parts of the theory of
  species in a way that is accessible to others in the programming
  languages community. The existing literature on species and recent
  related developments~\cite{BLL,keck} are relatively inaccessible to
  PL researchers, since they assume an extensive mathematical
  background and motivations that many PL researchers do not have.

  For example, \todo{labeled vs unlabeled}.  I have begun a series of
  blog posts \cite{blog posts} which will form the basis for this
  presentation; \pref{sec:species} contains an abridged version.

\item The second goal is to lay the theoretical groundwork for
  understanding species as a foundation for data types.  That is, if
  one wanted to design a programming language with ``species types''
  from the ground up, upon what theory could it be based?
  \pref{sec:species-types} presents some preliminary results in this
  direction and lays out a roadmap for the remaining theory to be
  developed.

\item Third, the theory of species can be used to build practical
  tools for working with existing algebraic data types.  Towards this
  end I have developed XXX.  \pref{sec:species-library} explains the
  current features of the library and proposes features to be added.
  \todo{more detail here?}

\end{enumerate}

\section{Combinatorial Species}
\label{sec:species}

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
natural numbers $\{0, \dots, n-1\}$ (also written $[n]$) as \emph{the}
canonical label set of size $n$, and write $F[n]$ (instead of
$F[[n]]$) for the set of $F$-structures built from this set.

It's not hard to show that functors preserve isomorphisms, so although
the definition only says that a species $F$ sends a bijection $\sigma
: U \bij V$ to a \emph{function} $F[\sigma] : F[U] \to F[V]$, in fact,
by functoriality every such function must be a bijection. \todo{is
  this really important to say?}

\subsection{Building Species Algebraically}
\label{sec:building-species}

The formal definition of species is wonderfully simple, but working
directly with the definition in practice does not get one very far.
Instead, we use an algebraic theory that lets us compositionally build
a wide variety of species from a collection of primitive species and
operations on species. (It's important to note that it does \emph{not}
allow us to build \emph{all} species, but it does allow us to build
many of the ones we care about.)

\subsubsection{Primitives}
\label{sec:primitives}

We begin with a few primitive species:

\begin{itemize}
\item
  The \emph{zero} or \emph{empty} species, denoted $\mathbf{0}$, is the
  unique species with no structures whatsoever; that is,
  \begin{align*}
  \Zero[U] &= \varnothing \\
  \Zero[\sigma : U \bij V] &= id_{\varnothing} : \Zero[U] \to \Zero[V].
  \end{align*}
  Of course, $\Zero$ is the identity element for
  the sum operation on species (defined in~\pref{sec:sum}).

\item
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

\item
  The \emph{singleton} species, denoted $\X$, is defined by

  $\X[U] = \begin{cases} U & ||U|| = 1 \\ \emptyset & \text{otherwise} \end{cases}$

  with lifting of bijections defined in the evident manner. That is,
  there is a single $\X$-structure on a label set of size $1$
  (which we identify with the label itself, though we could have also
  defined $\X[U] = \{\star\}$ when $||U|| = 1$), and no
  $\X$-structures indexed by any other number of labels.

  As with $\One$, we may equivalently define $\X$ as a
  hom-functor, namely $\X = \mathbb{B}(\{\star\}, -)$.

  It's worth noting again that although $\One$ and $\X$ do
  ``case analysis'' on the label set $U$, they actually only depend on
  the \emph{size} of $U$; indeed, as we
  \href{http://byorgey.wordpress.com/2012/12/06/species-definition-clarification-and-exercises/}{noted
  previously}, by functoriality this is all they can do.
\item
  The species of \emph{bags}\footnote{The species literature calls this
    the species of \emph{sets}, but that's misleading to computer
    scientists, who expect the word ``set'' to imply that elements
    cannot be repeated.}, denoted $\Bag$, is defined by

  $\Bag[U] = \{U\}$,

  that is, there is a single $\Bag$-structure on any set of labels
  $U$, which we usually identify with the set of labels itself (although
  we could equivalently define $\Bag[U] = \{\star\}$). The idea is
  that an $\Bag$-structure consists solely of a collection of
  labels, with no imposed ordering whatsoever.

  If you want to abuse types slightly, one can define $\Bag$ as
  a hom-functor too, namely $\mathbb{E}(-,\{\star\})$. (\citet{yeh}
  actually has $\mathbb{B}(-, \{\star\})$, but that's wrong.)
\end{itemize}

As a summary, \pref{fig:prims} contains a graphic showing
$\mathbf{0}$-, $\One$-, $\X$-, and
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

Just as a teaser, it turns out that $\X$ and $\Bag$ are
identity elements for certain binary operations on species as well,
though you'll have to wait to find out which ones!

\subsubsection{Operations}
\label{sec:operations}

\begin{itemize}
\item The \term{sum} of two species $F + G$ is just a disjoint
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

  \todo{pictures}

  \todo{examples}

  \todo{explain about $2 = 1 + 1$ and so on.  Use natural number
    notation, $0 = \inl(\star)$ (?) and so on.}

\item The \term{product} of species is a bit more interesting.  One
  might na\"ively expect to have
  \[ (F \times G)[U] = F[U] \times G[U] \] where $\times$ denotes the
  Cartesian product of sets.  This is a sensible operation on species
  (to be discussed further below) but not the most natural notion of
  product.  The reason is that \todo{finish}

  \todo{pictures}

  \todo{examples}

  \todo{note that multiplication on naturals works as expected.  Copy
    of $\N$ embedded inside species as a subring.}

\end{itemize}

\subsubsection{Recursion}
\label{sec:recursion}

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

As an example of species which are equipotent but
not isomorphic, consider the species $\L$ of linear orderings (\ie\
lists) and the species $\S$ of permutations.  It is well-known that
the number of linear orderings and the number of permutations of $n$
distinct labels are both $n!$.  However, there is no way to set up a
family of bijections that respects relabeling: any list can be sent to
any other by an appropriate relabeling, but there is no way to send
(say) a permutation with two cycles to a permutation with three cycles
just by relabeling.

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
\label{sec:species-types}

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
