% -*- mode: LaTeX; compile-command: "mk" -*-

\documentclass{article}

\usepackage{showkeys}

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

\graphicspath{{images/}}

\newcommand{\fold}{\ensuremath{\mathit{fold}}}
\newcommand{\map}{\ensuremath{\mathit{map}}}

\newcommand{\spe}[1]{\ensuremath{\langle #1 \rangle}}
\newcommand{\ty}[2]{\ensuremath{\llbracket #1 \rrbracket}\ #2}
\newcommand{\seqv}[2]{\mathord{\sim_{#1,#2}}}

\newcommand{\elim}[3]{#2 \stackrel{#1}{\twoheadrightarrow} #3}

\title{Combinatorial Species and Algebraic Data Types \\ {\small Dissertation Proposal}}
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

The theory of \term{algebraic data types} has had a profound impact on
the practice of programming, especially in functional
languages.  The basic idea is that types can be built up
\term{algebraically} from a small set of primitive types and
combinators: a unit type, base types, sums (\ie\ tagged unions),
products (\ie\ tupling), and recursion.  Most languages with support
for algebraic data types also add various bells and whistles for
convenience (such as labeled products and sums, convenient syntax for
defining types as a ``sum of products'', and pattern matching), but
the basic idea is unchanged. 
  % \scw{Could play up the practical aspects
  % some more. We'll need to investigate how these aspects affect
  % species when we do language design.} \bay{I learned from Jacques
  % Carette (the idea is apparently originally from Bruno Salvy) how to
  % model labeled sums using species -- in fact one can make an argument
  % that they give a \emph{better} way to model what is really going on
  % than the ADT point of view, which makes you forget about the labels.
  % But I don't think it's worth talking about that in the proposal.}

For example, in Haskell~\cite{haskell} we can define a type of binary
trees with integer values stored in the leaves as follows:
\begin{code}
data Tree  =  Leaf Int 
           |  Branch Tree Tree
\end{code}

\newcommand{\Int}{\ensuremath{\mathsf{Int}}}

Algebraically, we can think of this as defining a type $\mu T.\; \Int
+ T \times T$, where $\mu$ denotes a ``least fixed point'' operator.
This description says that a |Tree| is either an |Int| (tagged with |Leaf|) or a
pair of two recursive occurrences of |Trees| (tagged with |Branch|).

This algebraic view of data leads to many benefits. From a theoretical
point of view, recursive algebraic data types can be interpreted as
\emph{initial algebras} (or \emph{final coalgebras}), which gives rise
to an entire theory---both semantically elegant and practical---of
programming with recursive data structures via \term{folds} and
\term{unfolds} \cite{bananas, gibbons-calcfp}. A fold gives a principled way to compute a ``summary
value'' from a data structure; dually, an unfold builds up a data
structure from an initial ``seed value''.  For example, a fold for
|Tree| can be implemented as
\begin{code}
treeFold :: (Int -> a) -> (a -> a -> a) -> Tree -> a
treeFold f _ (Leaf i)     = f i
treeFold f g (Branch l r) = g (treeFold f g l) (treeFold f g r)
\end{code}
The |treeFold| function captures the essential pattern of recursion
over |Tree| data structures.  We can use |treeFold| to, say, compute
the product of all the |Int| values stored in a tree:
\begin{code}
treeProd :: Tree -> Int
treeProd = treeFold id (*)
\end{code}
Indeed, |treeFold| is \emph{universal} in the sense that anything we
might wish to compute from a |Tree| can be accomplished with
|treeFold|.  Such folds are guaranteed to exist for any algebraic data
type---indeed, it is not hard to automatically generate the fold for a
data type, given its algebraic description.  There are
several Haskell libraries which can do this generation, including
|derive|~\cite{derive} and |DrIFT|~\cite{DrIFT}. The Charity
programming language~\cite{charity} was also designed so that all
computation over inductive types was based on automatically-derived
folds.

Folds are ubiquitous---even languages without direct support for
algebraic data types often make use of them.  For example, \emph{How
  to Design Programs}~\cite[\S 9.4]{HTDP}, a popular introductory
programming text using the Scheme (now Racket~\cite{racket})
programming language, teaches students to write folds over recursive
data types (although it does not use that terminology).  The
\emph{visitor pattern}~\cite{GoF,palsberg:essence}, often used in
object-oriented languages, can also be seen as a type of fold.

Folds (and unfolds) satisfy many theorems which aid in transforming,
optimizing, and reasoning about programs defined in terms of them.  As
a simple example, a map (\ie\ applying the same function to every
element of a container) followed by a fold can always be rewritten as
a single fold. These laws, and others, allow Haskell compilers to
eliminate intermediate data structures through an optimization called
deforestation~\cite{Wadler:1988,Gill93ashort}.

An algebraic view of data types also enables \term{datatype-generic
  programming}---writing functions which operate generically over
\emph{any} algebraic data type by examining its algebraic structure.
For example, the following function (defined using Generic
Haskell-like syntax~\cite{generic-haskell}) finds the product of all
the |Int| values contained in a value of \emph{any} algebraic data
type.  It gives the same result as |treeProd| on |Trees| but also
works on lists or any other type.
\begin{spec}
genProd {| Int         |} i        = i
genProd {| Sum t1 t2   |} (Inl x)  = genProd {| t1 |} x
genProd {| Sum t1 t2   |} (Inr x)  = genProd {| t2 |} x
genProd {| Prod t1 t2  |} (x,y)    = genProd {| t1 |} x * genProd {| t2 |} y
genProd {| _           |} _        = 1
\end{spec}
Datatype-generic programming is a powerful technique for reducing boilerplate, made possible
by the algebraic view of data types, and supported by many Haskell
libraries and
extensions~\cite{Jansson:PolyP,Lammel:SYB,Cheney:LIG,weirich:replib,weirich:erasure}.

However, algebraic datatypes can only express types with tree-like
structure. There are many such types, including tuples, records,
options, variants, and lists, but this list does not include all
common data structures. In particular, algebraic data types cannot
directly represent data structures with \term{symmetry} or
\term{sharing}.

A data structure with \term{symmetry} is one whose elements can be
permuted in certain ways without affecting its identity.  For example,
permuting the elements of a bag always results in the same bag.
Likewise, the elements of an ordered cycle may be cyclically permuted
without affecting the cycle.  By contrast, the tree structure
illustrated previously has no symmetry: any permutation of the
elements results in a different tree.  In fact, every algebraic data
structure has no symmetry. Every element in an algebraic structure can
be uniquely identified by a \emph{path} from the root of the structure
to the element, so permuting the elements always results in an
observably different value.

A data structure with \term{sharing} is one in which different parts
of the structure may refer to the same subpart.  For example, consider
the type of undirected, simple graphs, consisting of a set of vertices
together with a set of edges connecting pairs of vertices.  In
general, such graphs may involve sharing, since multiple edges may
refer to the same vertex, and vice versa.

In a language with first-class pointers, creating data structures with
sharing is relatively easy, although writing correct programs that
manipulate them may be another story. The same holds true in languages
without first-class pointers. Creating data structures with sharing in
the heap is not difficult in Haskell, but it may be difficult or even
impossible to express the programs that manipulate them.  

For example, in the following code,
\begin{spec}
t = let t3 = Leaf 1
        t2 = Branch t3 t3
        t1 = Branch t2 t2 
    in Branch t1 t1
\end{spec}
only one ``Leaf'' and three ``Branch'' structures will be allocated in
memory. The tree |t2| will be shared in the node |t1|, which will
itself be shared in the node |t|.  Furthermore, in a lazy language
such as Haskell, recursive ``knot-tying'' allows even cyclic
structures to be created. For example,
\begin{spec}
nums = 1 : 2 : 3 : nums
\end{spec}
actually creates a cycle of three numbers in memory.  

Semantically, however, |t| is a tree, not a dag, and |nums| is an
infinite list, not a cycle.  It is impossible to observe the sharing
(without resorting to compiler-specific
tricks~\cite{Gill-2009-sharing}) in either of these examples. Even
worse, applying standard functions such as |fold| and |map| destroys
any sharing that might have been present and risks nontermination.

When (as often) programmers wish to work with ``non-regular'' data
types involving symmetry or sharing, they must instead work with
suitable \emph{encodings} of them as regular data types.  For example,
a bag may be represented as a list, or a graph as an adjacency matrix.
However, this encoding puts extra burden on the programmer, both to ensure that
invariants are maintained (\eg\ that the adjacency matrix for an
undirected graph is always symmetric) and that functions respect
abstract structure (\eg\ any function on bags should give the same
result when given permutations of the same elements as inputs).

The theory of \term{combinatorial species} was first described in 1981
by Andr\'{e} Joyal~\cite{joyal} as a framework for understanding and
unifying much of \term{enumerative combinatorics}, the branch of
mathematics concerned with counting abstract structures.  Since then,
the theory has been explored and extended by many other
mathematicians. Like the theory of algebraic data types, it is also
concerned with describing structures compositionally, but is much more
general.

Upon gaining even a passing familiarity with both algebraic data types
and combinatorial species, one cannot help but be struck by obvious
similarities in the algebraic approaches to describing structures
(though it is clear that species are much more general). However,
there has yet to be a comprehensive treatment of the precise
connections between the two. \todo{finish}

\todo{say something here about gf's etc.  Richer data types not the
  only benefit.}

\subsection{Goals and outline}
\label{sec:goals}

The overarching goal of the proposed research is to begin answering
the question:
\begin{quote}
  \textbf{What benefits can be derived from using the mathematical
    theory of species as a foundational theory of data structures?}
\end{quote}
Answers to this question can take many forms.  What would a
programming language with ``species types'' look like?  Can we use
species theory as a tool for working with existing algebraic data
types?  Specifically, the contributions of the proposed research are
threefold:
\begin{enumerate}
\item A significant part of the proposed work will consist in
  presenting relevant parts of the theory of species in a way that is
  accessible to others in the programming languages community. This
  will be a significant contribution: the existing literature on
  species and recent related developments~\cite{BLL,keck} are fairly
  inaccessible to PL researchers since they assume an extensive
  mathematical background and motivations that many PL researchers do
  not have.  My strong background in mathematics and experience in
  teaching and writing make me an ideal \todo{finish this sentence?}

  I have begun a series of blog posts \cite{blog posts} which will
  form the basis for this presentation; \pref{sec:species} contains an
  abridged version.

\item The second goal is to lay the theoretical groundwork for
  understanding species as a foundation for data types.  That is, if
  one wanted to design a programming language with ``species types''
  from the ground up---if one was to take the theory of species as the
  starting point rather than the theory of algebraic data types---what
  would it look like, and how would one understand the implementation
  from a theoretical point of view?
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

The theory if species is a unified theory of \emph{structures}, or as
a programmer might say, \emph{containers}. By a \emph{structure} we
mean some sort of ``shape'' containing \emph{locations} (or
\emph{positions}). \pref{fig:example-structures} shows two different
structures, each with eight locations:

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

It is very important to note that we are talking about structures with
\emph{labeled locations}; the numbers in \pref{fig:example-structures}
are \emph{not} data being stored in the structures, but \emph{names}
or \emph{labels} for the locations.  To talk about a \emph{data
  structure} (\ie\ a structure filled with data), we must also
specify a mapping from locations to data, like $\{ 0 \mapsto
\texttt{'s'}, 1 \mapsto \texttt{'p'}, 2 \mapsto \texttt{'e'} \dots
\}$, as shown in~\pref{fig:shape-data}.  This will be made more
precise in~\pref{sec:species-types}.

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
composition---explained in~\pref{sec:operations}---since it gives us a
way to model sharing (albeit only in limited ways).

Why have labels at all? In the tree shown
in~\pref{fig:example-structures}, we can uniquely identify each
location by a path from the root of the tree, without referencing
labels at all. However, the structure on the left illustrates one
reason labels are needed. The circle is supposed to indicate that
the structure has \emph{rotational symmetry}, so there would be no way
to uniquely refer to any location other than by giving them labels.

\subsection{Definition}
\label{sec:species-definition}

\begin{defn}
A \term{species} $F$ is a pair of mappings which
\begin{itemize}
\item sends any finite set $U$ (of \term{labels}) to a finite set
  $F[U]$ (of \term{structures}), and
\item sends any bijection on finite sets $\sigma : U \bij V$ (a
  \term{relabeling}) to a function $F[\sigma] : F[U] \to F[V]$
  (illustrated in \pref{fig:relabeling}),
\end{itemize}
satisfying the following functoriality conditions:
\begin{itemize}
\item $F[id_U] = id_{F[U]}$, and
\item $F[\sigma \circ \tau] = F[\sigma] \circ F[\tau]$.
\end{itemize}

This definition is due to Joyal \cite{joyal}, as described in BLL
\cite{BLL}.
\end{defn}

\begin{figure}
  \centering
  \includegraphics{relabeling}
  \caption{Relabeling}
  \label{fig:relabeling}
\end{figure}

\todo{redraw this with diagrams}

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

To make this more concrete, consider a few examples:
\begin{itemize}
\item The species of \emph{lists} (or \emph{linear orderings}) sends
  every set of labels (of size $n$) to the set of all sequences (of
  size $n!$) containing each label exactly once.  \todo{draw a
    picture}.

\item The species of \emph{(rooted, ordered) binary trees}
  \todo{finish}

\item The species of \emph{series-parallel graphs} \todo{finish}
\end{itemize}

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

\subsection{Equipotence and isomorphism}
\label{sec:isomorphism}

\begin{defn}
We say that two species $F$ and $G$ are \term{equipotent}, denoted $F
\equiv G$, when there exists a family of bijections $\phi_U : F[U]
\bij G[U]$, that is, there are the same number of $F$- and
$G$-structures of each size.  
\end{defn}
Although this notion is occasionally useful, it is rather weak.  More
useful is the notion of species \term{isomorphism}:
\begin{defn}
  Species $F$ and $G$ are isomorphic, denoted $F \cong G$, precisely
  when they are \term{naturally isomorphic} as functors; that is, when
  there exists a family of bijections \[ \phi_U : F[U] \bij G[U] \]
  which moreover \term{commute with relabeling}: that is, $\phi_V
  \comp F[\sigma] = G[\sigma] \comp \phi_U$ for all $\sigma : U \bij
  V$, as illustrated by the commutative diagram in~\pref{fig:nat-iso}.
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
\end{defn}
% For example, $\X + (\X + \X)$ and $\Sp{3} \sprod \X$ are isomorphic, as witnessed by
% the mapping
% \begin{align*}
%   \inl(u) &\bij (0, u) \\
%   \inr(\inl(u)) &\bij (1,u) \\
%   \inr(\inr(u)) &\bij (2,u)
% \end{align*}
% \todo{is there a more perspicuous way to write the above?}
% which commutes with relabeling since there is always exactly one label
% to modify.

For example, the species of rooted, ordered binary trees and the
species of $n$-ary (``rose'') trees are isomorphic, since \todo{finish
  explaining}.

As an example of species which are equipotent but not isomorphic,
consider the species $\L$ of lists and the species $\S$ of
permutations.  It is well-known that the number of linear orderings
and the number of permutations of $n$ distinct labels are both $n!$.
However, there is no way to set up a family of bijections between them
which respect relabeling: put simply, any two lists of length $n$ are
related by some relabeling, but not all permutations of size $n$ are.
More specifically, pick two non-isomorphic permutations built on the
same set of labels---say, pick one consisting of a single cycle and
one consisting of two disjoint cycles.  These permutation structures
must map to some list structures under the family of bijections.  But
those two list structures must be related by some relabeling, and
hence the family of bijections does not commute with
relabeling. \pref{fig:equipotent-not-iso} illustrates the situation
diagrammatically.  \todo{why is this interesting/important for
  thinking about data types?}

\todo{draw picture here of relabeling lists and cycles}

We say that two \emph{structures} of a given species are isomorphic
when there exists a relabeling taking one to the other.  That is, $f_1
\in F[U]$ and $f_2 \in F[V]$ are isomorphic if and only if there is
some $\sigma : U \bij V$ such that $F[\sigma](f_1) = f_2$.

\subsection{Building species algebraically}
\label{sec:building-species}

The formal definition of species is wonderfully simple, but working
directly with the definition does not get one very far in practice.
Instead, we use an algebraic theory that allows compositionally building
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

\paragraph{One}
  The \emph{unit} species, denoted $\One$, is defined by
  \[ \One[U] =
  \begin{cases}
    \{\star\} & ||U|| = 0 \\
    \varnothing & \text{otherwise}
  \end{cases}
  \]
  That is, there is a unique $\One$-structure indexed by the empty set
  of labels, and no $\One$-structures with any nonzero number of
  labels. $\One$ lifts bijections in the obvious way, sending every
  bijection to the appropriate identity function.  Of course, one
  should also verify that this definition satisfies the requisite
  functoriality properties, which is not difficult.

  Some initially find this definition surprising, instead expecting
  something like $\One[U] = \{ \star \}$ for all $U$. (That
  is indeed a valid species, and we will meet it below.)  In a sense,
  the reason for the surprising definition of $\One$ is the surprising
  definition of product, explained in \pref{sec:operations}, which in
  turn is surprising precisely because of the fact that species are
  indexed by size (whereas usual data types are not).

  More abstractly, it's worth mentioning that $\One$ can be defined as
  $\mathbb{B}(\emptyset, -) : \mathbb{B} \to \mathbb{E}$, that is, the
  covariant hom-functor sending each finite set $U \in \mathbb{B}$ to
  the (finite) set of bijections $\emptyset \leftrightarrow U$
  \cite{yeh}. There is, of course, a unique bijection $\emptyset
  \leftrightarrow \emptyset$ and no bijections $\emptyset
  \leftrightarrow U$ for nonempty $U$, thus giving rise to the
  definition above.

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
  (which we identify with the label itself), and no
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
    cannot be repeated. The \emph{labels} in a bag structure cannot be
  repeated, but nothing stops us from mapping labels to data elements
  in a non-injective way.}, denoted $\Bag$, is defined by \[ \Bag[U] =
  \{U\}, \] that is, there is a single $\Bag$-structure on any set of
  labels $U$, which we usually identify with the set of labels itself
  (although we could equivalently define $\Bag[U] = \{\star\}$). The
  idea is that an $\Bag$-structure consists solely of a collection of
  labels, with no imposed ordering whatsoever.

  $\E$ is precisely the species mentioned previously which people
  na\"ively expect as the definition of $\One$.  In fact, $\E$ is
  indeed the identity element for a product-like operation,
  \term{Cartesian product}, to be discussed below.

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

There are other primitive species, some of which we will encounter
later.  In fact, it is possible to give a complete classification of
primitive species (for a suitably formal notion of ``primitive'')---it
is beyond the scope of this proposal, though relevant XXX

\subsubsection{Operations}
\label{sec:operations}

We now turn to \emph{operations} that can be used to compose more
complex species from simpler ones.

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

  Up to isomorphism, $\Zero$ is the identity element for sum.
  Intuitively, if one has either a $\Zero$-structure or an
  $F$-structure, one must in fact have an $F$-structure, since
  $\Zero$-structures do not exist.  Sum is also associative and
  commutative up to isomorphism.

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
  \emph{split} $U$ into two disjoint subsets $U_1$ and $U_2$ (with
  $U_1 \cup U_2 = U$ and $U_1 \cap U_2 = \varnothing$), and then pair
  an $F$-structure on $U_1$ with a $G$-structure on $U_2$.  The set of
  \emph{all} $(F \sprod G)$-structures is obtained by doing this in
  all possible ways.  More formally, \[ (F \sprod G)[U] = \sum_{U_1
    \uplus U_2 = U} F[U_1] \times G[U_2]. \]

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
    \todo{also include jaggedy-line-type picture}

  Here are a few examples:
  \begin{itemize}
  \item $\X \sprod \X$ is the species of \term{ordered pairs}.  The
    only way to obtain an $\X \sprod \X$ structure is to have exactly
    two labels, one going to the first $\X$ and the other to the
    second; as shown in \pref{fig:ord-pairs}, there are exactly two
    ways to do so.
    \begin{figure}
      \centering
    \begin{diagram}[width=200]
import Species

theDia = linOrd [0,1] |||||| strutX 0.5 |||||| linOrd [1,0]
dia = theDia # centerXY # pad 1.1
    \end{diagram}      
      \caption{$\X^2$-structures}
      \label{fig:ord-pairs}
    \end{figure}

  \item $\X \sprod \E$ is the species of \term{pointed sets}, or
    \term{elements}. Structures consist of a single distinguished
    element paired with any number of remaining elements.  Whether
    structures are thought of as ``pointed sets'' or ``elements''
    depends on whether the $\E$-structure is thought of as an integral
    part of the structure, or merely as a ``sink'' for throwing away
    ``unwanted'' elements.

    \todo{picture}
  \item $\E \sprod \E$ is literally the species of ordered pairs of
    sets; but we usually think of it as the species of \term{subsets},
    where the first set picks out the labels of interest and the
    second subset again serves as a ``sink'' for collecting the unused
    labels.

    \todo{picture}
  \end{itemize}

  Note that products of ``natural numbers'' (the species $2 = 1 + 1$
  and so on) work exactly as expected; in fact, we get an entire copy
  of the natural numbers $\N$ embedded inside species as a subring.

  All the usual algebraic laws hold up to isomorphism: $\One$ is the
  identity element for product, $\Zero$ is an annihilator; product is
  associative and commutative and distributes over sum.

\paragraph{Composition}
The \term{composition} $F \comp G$ of two species $F$ and $G$,
intuitively, creates ``$F$-structures of $G$-structures''. To create
an $(F \comp G)$-structure over a given set of labels $U$, we first
\emph{partition} $U$ into some number of nonempty subsets; create a
$G$-structure over each subset; then create an $F$-structure
\emph{over the resulting set of $G$-structures}.  Doing this in all
possible ways yields the complete set of $(F \comp G)$-structures over
$U$. Formally,
\[ (F \comp G)[U] = \sum_{\pi \in \Par[U]} F[\pi] \times \prod_{p \in
  \pi} G[p]. \] where $\Par$ denotes the species of partitions.
\pref{fig:composition} shows an abstract representation of the
definition.

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

  \todo{examples: $\Par = \E_+ \comp \E$. Perfect trees. Others? Say
    something about how this is particularly interesting since
    composition is usually not treated in discussions of algebraic
    data types.}

Up to isomorphism, $\X$ is the identity element for composition.
Composition also satisfies \todo{list some algebraic laws?}

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

\newcommand{\pt}[1]{\ensuremath{#1^{\bullet}}}

  The \term{pointing} $\pt F$ of a species $F$ is a derived
  operation defined by \[ \pt F = \X \sprod F' \].
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
so a Cartesian product structure consists of a pair of structures each
containing ``pointers'' to a single set of shared memory locations.

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
solutions which are unique (the \term{Implicit Species Theorem} and
its generalizations~\cite{XXX}).

In general, we can allow arbitrary mutually recursive
systems of implicit equations \[ \overline{\F_i = \Phi_i(F_1, \dots,
  F_n)}^n. \]  For example, \todo{series-parallel graphs.}

\todo{say something about connection to $\mu$ operator, etc.?}

\subsection{Unlabeled species}
\label{sec:unlabeled}

Although the definition of species assures us that labels ``don't
matter'', we still have to work with explicitly labeled structures.
Much of the time, this explicit labeling is a nuisance.  Even when
restricting ourselves to a chosen canonical set of labels (such as
$[n]$), there can still be many distinct labeled structures that we do
not wish to consider as distinct.  For example,
\pref{fig:labeled-structures} shows six distinct labeled binary tree
structures; for most purposes, as long as each location has a
distinct label it does not matter which particular label is used
for each.

\begin{figure}
  \centering
  \begin{diagram}[width=250]
import Data.Tree
import Diagrams.TwoD.Layout.Tree
import Data.List (permutations)

allTrees = [ Node a [Node b [], Node c []] || [a,b,c] <- permutations [0..2] ]

dTree = renderTree ((<> circle 1 # fc white) . text . show) (~~)
layout = symmLayout' with { slHSep = 4, slVSep = 3 }
trees = hcat' with {sep = 1} . map (dTree . layout) $ allTrees

dia = trees # centerXY # pad 1.1
  \end{diagram}
  %$
  \caption{Six distinct labeled tree structures}
  \label{fig:labeled-structures}
\end{figure}

We can give a precise meaning to the concept of \term{unlabeled
  structures} by defining them as \emph{equivalence classes} of
labeled structures under isomorphism. For example, the six labeled
tree structures in \pref{fig:labeled-structures} are all elements of
the same equivalence class (since for each pair of structures there
exists a permutations $\sigma : [3] \to [3]$ sending one to the
other), and together represent an unlabeled binary tree structure,
which we may draw as in \pref{fig:unlabeled-trees}.

\begin{figure}
  \centering
  \begin{diagram}[width=50]
import Data.Tree
import Diagrams.TwoD.Layout.Tree

tree1 = Node () [Node () [], Node () []]

dTree  = renderTree (const (circle 1 # fc black)) (~~)
layout = symmLayout' with { slHSep = 4, slVSep = 3 }
trees  = dTree . layout $ tree1

dia = trees # centerXY # pad 1.1
  \end{diagram}
  %$
  \caption{An unlabeled tree structure}
  \label{fig:unlabeled-trees}
\end{figure}

\todo{add another unlabeled tree?}

Although unlabeled structures formally consist of equivalence classes
of labeled structures, we can informally think of them as normal
structures built from ``indistinguishable labels''; for a given
species $F$, there will be one unlabeled $F$-structure for each possible
``shape'' that $F$-structures can take.

However, one must be careful not to take this informal intuition too
far.  For example, \pref{fig:unlabeled-cartesian} shows a $(\C \times
(\E \sprod \E))$-structure of size $8$.  It is easy enough to
\emph{draw} it using indistinguishable labels---but to describe it in
a data structure still requires having some way to refer to individual
labels (in order to specify which elements are selected by the
superimposed subset structure). \todo{explain this more?}
\begin{figure}
  \centering
  \begin{diagram}[width=150]
import Species

point' d = d <> drawSpN Hole # sizedAs (d # scale 1.3)

dot :: Diagram Cairo R2
dot = circle labR # fc black
theDia = cyc' [dot, point' dot, point' dot, dot, dot, point' dot, dot,dot] 2

dia = theDia # centerXY # pad 1.1
  \end{diagram}
  \caption{A $(\C \times (\E \sprod \E))$-structure}
  \label{fig:unlabeled-cartesian}
\end{figure}

\subsection{Regular and non-regular species}
\label{sec:regular}

\begin{figure}
  \centering
  \begin{diagram}[width=75]
import Species
dia = cyc [0..4] 1.2 # pad 1.1
  \end{diagram}
  \begin{diagram}[width=60]
import Species
dia = ( roundedRect 2 1 0.2
        <> (lab 0 |||||| strutX 0.3 |||||| lab 3)
           # centerXY
      )
      # pad 1.1
      # lw 0.02
  \end{diagram}
  \begin{diagram}[width=75]
import Species
import Data.Tree
t   = Node Bag [lf (Lab 1), lf (Lab 2), Node Bag [lf (Lab 0), lf (Lab 3)]]
dia = drawSpT' mempty with t # pad 1.1
  \end{diagram}  
  \caption{Non-regular structures}
  \label{fig:non-regular}
\end{figure}

\todo{stuff about regular vs. other species.}

\todo{non-regular, molecular species.}

\subsection{Exponential generating functions}
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

Going through the rest of the primitives, one can verify that
\begin{align*}
  \Zero(x) &= 0 \\
  \One(x)  &= 1 \\
  \X(x)    &= x.
\end{align*}

Since the number of $(F+G)$-structures on a given label set is the sum
of the number of $F$-structures and the number of $G$-structures, that
is, $||(F+G)[n]|| = ||F[n]|| + ||G[n]||$, we have \[ (F+G)(x) =
\sum_{n \geq 0} (f_n + g_n) \frac{x^n}{n!} = F(x) + G(x). \]

We also have $(FG)(x) = F(x)G(x)$, which is worth verifying in detail:
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
indeed equal to \[ \sum_{0 \leq k \leq n} \binom{n}{k} f_k g_{n-k} \]
as follows (illustrated in \pref{fig:product-structures}): for
each $0 \leq k \leq n$, we can distribute $k$ of the labels to the
left side of the pair (and the remaining $n - k$ to the right) in
$\binom n k$ ways; we then have $f_k$ choices of an $F$-structure to
be the first element of the pair, and $g_{n-k}$ choices of
$G$-structure for the second.

\begin{figure}
  \centering
  \begin{diagram}[width=200]
import Diagrams.TwoD.Layout.Tree
import Data.Tree

tri = triangle 0.5 # scaleY 1.5 # alignT

t = Node mempty [Node tri [], Node tri []]

dia = renderTree id (~~) . symmLayout' with { slVSep = 0.5 } $ t
  \end{diagram}
  \caption{Building product structures}
  \label{fig:product-structures}
  %$
\end{figure}
\todo{add text to the above picture --- use diagrams-tikz?}

The foregoing proof illustrates the combinatorial insight gained by
examining the details of the mapping from species to generating
functions.  Not only that, we can assign computational significance to
\todo{finish}.

In fact, the mapping extends still further: it is also the case that
\begin{itemize}
\item $(F\comp G)(x) = F(G(x))$
\item $(F')(x) = (F(x))'$
\end{itemize}

A proof of the equation for derivative is straightforward.  The proof
for composition is omitted from this proposal, but follows a similar
(if somewhat more complicated) pattern as the proof for products
above, and can similarly be viewed computationally to derive a
procedure for enumerating structures from a composition.  There are
similar equations for other operations such as Cartesian product and
functor composition.

In other words, the mapping from species to egfs is a
\term{homomorphism} preserving much of the algebraic structure we care
about.  This means that an algebraic description of a species can
easily and mechanically be turned into a recipe for computing the
corresponding generating function.  It also means that we can take
implicit species equations such as $\L = \One + \X \sprod \L$ and
apply the homomorphism to both sides, yielding $\L(x) = 1 + x\L(x)$,
which can be solved to obtain the closed form $\L(x) = 1/(1-x)$.  In
many cases this leads to asymptotically faster methods for computing
the generating function than simply unrolling the underlying
recurrence. \todo{is there more to it than this?  Newton-Raphson,
  etc.}

The applications of generating functions are numerous:
\begin{enumerate}
\item They can be used to conduct asymptotic analysis of algorithms
  making use of the corresponding structures \cite{AC}
\item They can be used to enable fast random generation of structures
  according to desirable distributions \cite{boltzmann, darasse}.
\item \todo{more?}
\end{enumerate}
\todo{forward reference to species library}

\subsection{Other generating functions and applications}
\label{sec:other-gfs}

To each species we can also associate an \term{ordinary generating
  function} (ogf), \[ \unl{F}(x) = \sum_{n \geq 0} \unl{f}_n x^n, \]
where $\unl{f}_n$ denotes the number of \emph{unlabeled}
$F$-structures, that is, the number of equivalence classes of
isomorphic $F$-structures.  Just as with egfs, the mapping from
species to ogfs preserves addition, multiplication, and derivative,
but unlike egfs, it does \emph{not} preserve composition.  To compute
the ogf for a composed species we can use yet a third type of
generating function, the \term{cycle index series}, which tracks not
just sizes of structures but also information about their symmetry.
The details are beyond the scope of this proposal, but I plan to
include the details---and a computational interpretation thereof---in
my final document.

\todo{write something about applications of generating functions:
  algorithm analysis, random generation.}

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
must be taken to state the precise nature of the relationship.  I
propose to lay out a foundational theory for types based on species,
their eliminators, and generic programming techniques.  In this
proposal I report on some preliminary results and give a roadmap for
what remains to be accomplished.


\subsection{Preliminaries}
\label{sec:prelim}

\newcommand{\pair}[2]{\ensuremath{\left\langle #1, #2 \right\rangle}}

I will make use of a standard presentation of Martin-L\"of type
theory. In particular, the collection of types includes
\begin{itemize}
\item the void type, $\bot$
\item the unit type, $\top$
\item a distinguished type $\Set$
\item When $A$ and $B$ are types, $A + B$ is the sum type formed by
  the tagged union of $A$ and $B$.
\item Dependent sum types are denoted $\Sigma x:A. B(x)$, whose values
  are written $\pair{a}{b}$.  When $A$ is clear from context, we
  sometimes write $\Sigma x. B(x)$.  When $B$ does not depend on $x$
  we write $A \times B$ as an abbreviation for $\Sigma x:A. B$.
\item Dependent function types are denoted $\Pi x:A. B(x)$, whose
  values are written $\lambda x. b$.  When $B$ does not depend on $x$
  we write $A \to B$ as an abbreviation for $\Pi x:A. B$.  We also
  write $\forall A. B$ as an abbreviation for $\Pi A:\Set. B$.
\end{itemize}

A \term{relation} $R$ over a set $X$ is a set of pairs $R \subseteq
X^2$.  We write $a \mathbin{R} b$ if $(a,b) \in R$.  An
\term{equivalence} is a reflexive, symmetric, and transitive
relation.  If $R$ is an equivalence over $X$, we write $X/R$ to denote
the set of equivalence classes of $R$ in $X$, that is, maximal subsets
of $X$ such that any two elements are related by $R$.

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
only regular species and no recursion. \todo{improve?}

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

We can interpret these expressions as species, that is, as functors
$\B \to \E$ as described in \pref{sec:building-species}.  We will
write $\spe{S}$ to denote the functor $\B \to \E$ corresponding to the
species expression $S$.  But we can also straightforwardly interpret
them as type constructors, as shown in \pref{fig:type-constructors}.
The principal difference between the two interpretations is that $\ty
S A$ does not take the size of $A$ into account, whereas $\spe{S}[U]$
is indexed by the size of $U$. \todo{phrase this more accurately}

\begin{figure}
  \centering
  \begin{align*}
  \ty{\Zero} A &= \bot \\
  \ty{\One} A &= \top \\
  \ty{\X} A &= A \\
  \ty{F+G} A &= \ty{F} A + \ty{G} A \\
  \ty{F \sprod G} A &= \ty F A \times \ty G A \\
  \ty{F \comp G} A &= \ty F {(\ty G A)}
  \end{align*}
  \caption{Interpreting species expressions as type constructors}
  \label{fig:type-constructors}
\end{figure}

What is the precise relationship between $\spe{S}$ and $\ty{S}{}$ for
a given expression $S$?  $\spe{S}[U]$ describes labeled shapes
containing no data, with labels drawn from $U$, whereas elements of
$\ty{S}{A}$ are data structures containing data elements of type $A$.
Thus, we must pair structures of $\spe{S}[U]$ with functions of type
$U \to A$ to describe the mapping of locations to data.  However,
such pairings include ``too much'' information; in particular,
the precise labels used should not matter, so we need to quotient out
by an equivalence relating structures which use different labels but
are otherwise identical.

\todo{include a picture explaining the idea informally}

Formally, for a given species expression $S$ and type $A$, we define a
relation
\[ \seqv S A \subseteq \pset{(\Sigma U : Set. \spe{S}[U] \times (U \to
  A))^2} \] as follows: $(U, (s, f)) \sim_{S,A} (V, (t, g))$ if and
only if there exists some $\sigma : U \bij V$ such that \[ t =
\spe{S}[\sigma](s) \] and \[ g = f \comp \sigma^{-1}. \]
\todo{explain, give examples} 

% We must show that $\seqv S A$ is an
% equivalence, using properties of bijections and the functoriality of
% $\spe S$:
% \begin{itemize}
% \item For reflexivity, we take $\sigma = id$, noting that $f = f \comp
%   id = f \comp id^{-1}$, and $s = \spe{S}[id](s)$
%   by functoriality of $\spe S$.
% \item For symmetry, suppose $t = \spe{S}[\sigma](s)$ and $g = f
%   \comp \sigma^{-1}$.  Then $s = \spe{S}[\sigma^{-1}](t) =
%   (\spe{S}[\sigma])^{-1}(t)$ by functoriality, and $f = g \comp
%   (\sigma^{-1})^{-1} = g \comp \sigma$.

% \item For transitivity, if $(s,f)$ is related to $(t,g)$ by $\sigma$
%   and $(t,g)$ to $(u,h)$ by $\tau$, then as expected $(s,f)$ is
%   related to $(u,h)$ by $\tau \comp \sigma$.  The relation of $f$ to
%   $h$ can be seen by simple substitution; the relation of $s$ to $u$
%   follows again from the functoriality of $\spe S$.
% \end{itemize}

Given this, we can finally state the main theorem expressing the
precise connection between types and species:
\begin{thm}
  For all species expressions $S$,
  \[ \ty{S} A \cong \left( \sum_U \spe{S}[U] \times (U \to A) \right)
  / \seqv S A. \]
\end{thm}

% \begin{proof}
% The proof is by induction on the structure of species expressions.
% \begin{itemize}
% \item When $S = \Zero$, both sides are trivially isomorphic to the empty
%   type $0$.
% \item When $S = \One$, the sum on the right-hand side collapses to
%   $\spe{\One}[\varnothing] \times (\varnothing \to A) \cong 1 \times 1
%   \cong 1$.
% \item When $S = \X$, \todo{finish}
% \item When $S = S_1 + S_2$, \todo{finish.  Need lemma about sums of
%     quotients?}
% \item When $S = S_1 \sprod S_2$, \todo{finish}
% \item When $S = S_1 \comp S_2$, \todo{finish}
% \end{itemize}

% \end{proof}

We also have the following lemma, connecting the use of arbitrary
label sets with the use of the canonical label set $[n]$:
\begin{lem}
  \[ \left( \sum_U \spe{S}[U] \times (U \to A) \right)
  / \seqv S A \mathrel{\cong} \left( \sum_{n \in \N} \spe{S}[n] \times A^n \right)
  / \seqv S A \]
\end{lem}
Intuitively, including many different label sets of size $n$ does not
add any information; considering only the canonical label set of each
size is enough.  This lemma can be proved formally by noting that $||U||
= n$ if and only if there exists a bijection $\sigma : U \bij [n]$, so
every equivalence class on the left-hand side is a superset of one on
the right.

As a corollary, by transitivity we conclude that 
\begin{equation}
\ty{S} A \cong
\left( \sum_{n \in \N} \spe{S}[n] \times A^n \right) /
\mathord{\sim_{S,A}}, \label{eq:species-types}
\end{equation}
which gives a much more intuitive sense of what is going on: each type
is built up as a sum of species structures of every possible size,
each paired with a list of data elements.

Note that the quotienting in \eqref{eq:species-types} is still
required. \todo{explain why, and draw picture.}

 \todo{cite work on shape + data, explain further.  It's
  exactly the census by size that gives the theory of species enough
  of a foothold to do interesting computation.}

\todo{who cares? Why is this relevant?}

The language of species expressions used above is intentionally
simplified.  A full treatment will include some extra features:
\begin{itemize}
\item Multi-argument type constructors are quite common in practice
  and can be modeled by multisort species.  Extending the above theory
  to deal with multisort species is expected to be straightforward.
\item As explained previously, one of the great promises of the theory
  is to be able to talk about ``non-regular'' species and the
  corresponding types.  This requires extending the interpretation of
  species expressions from simple type constructors to \emph{setoids}
  consisting of a type constructor together with an equivalence
  relation on the values of the type.  All the theorems are then
  extended to take this new equivalence relation into account as well.
\item Recursion must be handled as well.  Recursive species
  expressions can be interpreted as recursive types, and the theory
  must be extended to take into account the relationship between them.
  I do not yet have a good sense of the difficulty, but expect that it
  should all go through.
\end{itemize}

\subsection{Eliminators for species types}
\label{sec:eliminators}

Standard type theory derives a generic \term{eliminator} for each type
which describes the computation principle by which values of that type
may be ``discharged'', \ie\ used in the service of computing some
other value.  If species are to be used as a foundation for data types
then we must be able to explain how to eliminate values of the
resulting types.

Specifically, we can define a (non-dependent) eliminator for the
species expression $S$ as a function of type \[ \forall A B. (\elim S A B)
\to \ty S A
\to B, \] where $(\elim S A B)$, to be defined below, denotes the type
of the arguments which must be provided to the eliminator.
Intuitively, $(\elim S A B)$ should be isomorphic to $\ty S A \to B$:
the forward direction is given by the eliminator itself, and the
backwards direction corresponds to the idea that we want to be able to
express every function of type $\ty S A \to B$ as an application of
the eliminator for $S$.

So far, our universe only contains species expressions whose type
interpretations are usual algebraic data types; we already know how to
construct eliminators for such types in a type-directed way, using
``high school algebra'' laws for exponents
\cite{hinze-reason-isomorphically}. \pref{fig:ADT-eliminators} can be
regarded as a recursive \emph{definition} of the eliminator
corresponding to any algebraic species expression.
\begin{figure}
  \centering
  \begin{center}
    \begin{tabular}{ccc}
      $\elim \Zero A B$ & $=$ & $\top$ \\
      $\elim \One A B$ & $=$ & $B$ \\
      $\elim \X A B$ & $=$ & $A \to B$ \\
      $\elim{F+G} A B$ & $=$ & $(\elim F A B) \times (\elim G A B)$ \\
      $\elim{F \sprod G} A B$ & $=$ & $\elim F A {(\elim G A B)}$ \\
      $\elim{F \comp G} A B$ & $=$ & $\elim F {(\ty G A)} B$
    \end{tabular}
  \end{center}  
  \caption{Eliminators for algebraic types}
  \label{fig:ADT-eliminators}
\end{figure}

% Note that if we continue the construction for composition
% recursively we eventually reach X, where we get  [[G]] A -> B which
% is actually isomorphic to A -G->> B.

So far, we have seen nothing new.  However, the promise of this work
is to be able to base types on species which do \emph{not} correspond
to any algebraic data type. Consider adding the following new
production to the grammar of species expressions, representing
\emph{molecular species}:
  \begin{align*}
    S & ::= \dots \\
      & \mid \X^n/\H_n
  \end{align*}
  Here $n$ is a natural
  number and $\H_n$ is a finite group of order $n$.
  $\spe{\X^n/\H_n}[U]$ is the set of length-$n$ sequences $\X^n[U]$,
  quotiented by the \term{action} of $\H_n$.  That is, two sequences
  $y,z \in \X^n[U]$ are considered equivalent if there is some $\sigma
  \in \H_n$ (considered as a permutation on $[n]$) such that $z =
  \sigma y$, where $\sigma$ acts on $y$ by permuting its elements.
  Here are a few examples:

\begin{itemize}
\item Let $Z_n$ denote be the cyclic group of order $n$.  Then
$\X^n/Z_n$ denotes the species of size-$n$ cycles, $\Sp{C}_n$: any two lists are
equivalent if they are related by a rotation.

\item As another example, if $\S_n$ is the symmetric group containing
  all possible permutations on $n$, $\X^n/\S_n$ denotes the species of
  size-$n$ bags, $\Bag_n$.
\end{itemize}

There are still many interesting species we cannot express, but this
addition gets at the crux of the matter.  The difficulty is that
\todo{should not be able to observe stuff quotiented by symmetry}

We can translate our intiution directly into a type for eliminators
for $\X^n/\H_n$ as follows:
\[ \elim{X^n/\H_n} A B \quad = \quad \Sigma f : \elim{X^n} A B.\ \Pi
\sigma \in \H.\ f = f \circ \sigma \] That is, to use an eliminator
for $\X^n/\H_n$, one must provide a way to eliminate $\X^n$,
\emph{paired with a proof} that the provided function respects the
symmetries imposed by $\H_n$; that is, permuting the list by one of
the allowed symmetries does not change the result of the provided
function.

\todo{how to implement this: actual proof in dep. typed language;
  randomized testing; theorem prover; etc.}

% Every nonempty species is isomorphic to
% \begin{itemize}
% \item the unit species,
% \item a sum,
% \item a product,
% \item or an \emph{atomic} species $X^n/\mathcal{H}$ 
%   \begin{itemize}
%   \item (where $\mathcal{H}$ acts transitively on $\{0, \dots,
%     n-1\}$).
%   \end{itemize}
% \end{itemize}

\subsection{An alternative approach to eliminators}
\label{sec:elim-alternative}

In this section I outline a possible alternative approach to
eliminators for species with symmetries, which also lends itself to
some nice programming constructs beyond eliminators.

Consider the \term{pointing} operator \todo{finish}

Pointing \emph{breaks symmetry}.

  \begin{diagram}[width=250]
    import Species
    f   = drawSpT (nd (text "F") (map lf [Leaf, Leaf, Leaf, Leaf])) # pad 1.1
    fpt = drawSpT (nd (text "F") (map lf [Point, Leaf, Leaf, Leaf])) # pad 1.1

    dia = [f, elimArrow, fpt] # map centerY # foldr1 (||-||) 
  \end{diagram}

  \[ \pt{(-)} : F \to \pt{F} ? \]

  \emph{Only} for polynomials!

\newcommand{\down}{\chi}

  \dots but Peter Hancock's ``cursor down'' operator \cite{hancock} is fine: \[ \down
  : F \to F \pt{F} \]

  \begin{diagram}[width=300]
    import Species
    c = Cyc [lab 0, lab 2, lab 3]
    d1 = draw c
    d2 = draw (down c)
    dia = (d1 ||-|| elimArrow ||-|| d2) # pad 1.05
  \end{diagram}

  \begin{diagram}[width=300]
    import Species
    c = Cyc [lab 0, lab 2, lab 3]
    d1 = draw c
    d2 = draw (down c)
    d3 = draw (Cyc (replicate 3 d4))
    d4 :: Diagram Cairo R2
    d4 = square 1 # fc purple
    x ||/|| y = x |||||| strutX 0.5 |||||| y
    t s = (text s <> strutY 1.3) # scale 0.5
    dia = (d1 ||/||
               arrow 1 (t "χ") ||/|| 
           d2 ||/||
               arrow 1 (t "F e'") ||/||
           d3 ||/||
               arrow 1 (t "δ") ||/||
           d4
          ) 
          # pad 1.05    
  \end{diagram}

  \begin{diagram}[width=300]
    import Species
    c = Cyc (map lab' [blue, red, yellow])
    d1 = draw c
    d2 = draw (down c)
    d3 = draw (fmap firstTwo (down c))
    d4 = draw (Cyc (map lab' [purple, orange, green]))
    firstTwo = map unPoint . take 2 . dropWhile isPlain . cycle . getCyc
    isPlain (Plain x) = True
    isPlain _         = False
    unPoint (Plain x) = x
    unPoint (Pointed x) = x
    t s = (text s <> strutY 1.3) # scale 0.5
    x ||/|| y = x |||||| strutX 0.5 |||||| y
    infixl 6 ||/||
    dia = (
          ( d1 ||/||
              arrow 1 (t "χ") ||/||
            d2 ||/||
              arrow 3 (t "F (id × head)" # scale 0.8)
          )
          ===
          strutY 1
          ===
          ( square 1 # lw 0 ||/||
            d3 ||/||
              arrow 1 (t "F ⊕") ||/||
            d4
          )

          )
          # pad 1.05
  \end{diagram}

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

\todo{give examples of use}

However, there are many features that could yet be added. \todo{talk
  about what some of these features are.}

% \section{Enumerating Unlabeled Structures}
% \label{sec:enumerating}

% \section{Doing Other Stuff}
%
% \todo{Need to figure out what other stuff to propose!  Views? Sharing?
%   L-species? Virtual species? Species + infinity?  Enumerating
%   unlabeled structures?  See NSF proposal for ideas, of course.}

It is unknown (to me) whether fast methods exist for generating
unlabeled structures (that is, representatives of equivalence classes)
for species involving composition, Cartesian product, and/or functor
composition.  I plan to investigate the combinatorics literature to
see whether such methods already exist, and, if so, add them to the
implementation in the \pkg{species} library.  If they do not, it may
be worth spending a bit of time thinking about, though in that case it
is likely to be quite difficult and probably beyond the scope of my
proposed research.

\section{Related Work}
\label{sec:related}

\paragraph{Species and computer science}

Flajolet, Salvy, and Zimmermann were some of the first to point out
connections between species and computer science \cite{FlSa95,
  FlajoletSalvyZimmermann1989a}.  Their work is now packaged as part
of the \emph{combstruct} library for
Maple~\cite{combstruct}. This library can achieve some
impressive results, but since it is only available within a
proprietary system with a dynamically typed language, it is neither
widely available nor easily portable to other languages.

The most closely related work is that of Carette and
Uszkay~\cite{Carette_Uszkay_2008_species}, who also see the potential
of species as a framework to extend the usual notion of algebraic data
types.  They describe some preliminary work adding species types to
Haskell, but it seems their work has not yet progressed very far.  Our
project plans to encompass their work and extend it in many directions.

\paragraph{Extending algebraic data types}

The idea of decomposing container types into shapes combined with data
can be found in the work of Jay and Cockett~\cite{jay-shapely}. They
define \term{shapely types} as a categorical framework for
understanding and working with container types that can be decomposed
in this way.  However, their framework cannot account for data types
with symmetry. Abbott \etal\ also give a formal categorical account of
\term{containers}~\cite{abbott_categories_2003}, a generalization of
shapely types, and later extended their work to the notion of a
\term{quotient container} \cite{abbott_quotient}, consisting of an
algebraic data type ``quotiented'' by some symmetries.  A fold over a
quotient container is thus a normal fold paired with a \emph{proof}
that the fold respects the quotient symmetries. It seems there are
strong connections with the theory of species, especially given the
molecular decomposition theorem, but these connections have not been
explored.  We would like to formalize the connection between species
and quotient containers, to bring insights from the work on quotient
containers to bear on species and vice versa.

Declaratively specifying \emph{sharing} in data structures has been
explored by Aiken \etal~\cite{aiken-2010-fusion}. In that work,
mutable data structures are specified as relations between data values,
and a language of indices describes the mapping from the relational
specification of a data structure to its physical layout.  In the
specific context of Haskell, Gill shows how it is possible to observe
sharing using special facilities provided by the Glasgow Haskell
Compiler~\cite{Gill-2009-sharing}.  These two approaches liberates
programmers from the difficulties of programming with pointers, but
otherwise does not not help with the problem of writing algorithms
that work over such structures.

Abel has implemented \emph{sized types}~\cite{abel-2010-miniagda} for the
dependently typed programming language Agda.  Such types have a rather
different goal than our proposed work on ``sized data types'': they
are a tool for termination checking, rather than a way to statically
track the size of containers.  Still, there may be some interesting
connections.

Atanassow and Jeuring explore the idea of automatically deriving
isomorphisms between types by making use of the theory of
\term{canonical isomorphisms}~\cite{Atanassow-2007-iso-inference}.  In
particular, they derive isomorphisms between user-defined data types
and the internal \emph{representation types} used by a generic
programming framework.  This allows converting between any two types
by converting to a representation type and back.  However, their
framework does not give the user much freedom in determining how the
isomorphism work; we envision a somewhat more flexible framework.

\paragraph{Testing}

Some early work on random generation is by Flajolet and Cutsem, who
describe a general algorithmic framework for random generation of a
certain subclass of labeled species~\cite{Flajolet-1994-random}.
Later Duchon \etal\ introduced \term{Boltzmann
  sampling}~\cite{Duchon-2002-Boltzmann, duchon-2004-boltzmann},
giving a faster way to do \emph{approximate} random generation (which
is sufficient for many applications, such as testing).  Boltzmann
sampling has been implemented in OCaml by Canou and
Darasse~\cite{ocaml-random-gen}, although only for algebraic data
types rather than for species types in general.  Moreover, there is
very recent work by Pivoteau, Salvy, and
Soria~\cite{pivoteau-11-algorithms} extending these techniques, which
as far as we know has not yet been incorporated into any real-world
testing framework.

In his masters thesis~\cite{agata}, Dureg{\r a}rd gives a careful
analysis of the distribution of recursive data structures generated by
naive QuickCheck generators, and explains the design of Agata, a
compositional framework for constructing random generators with
various desirable properties. However, the methods provided by Agata
for controlling generator distributions are somewhat ad-hoc, and do
not come with any sort of mathematical guarantees.  They are better
than the naive methods but still require considerable case-by-case
hand tuning.

Duregard Haskell Symposium.  gencheck.


point out connections between the theory of
species and computer science~\cite{FlSa95,
  FlajoletSalvyZimmermann1989a}.

Keck work.

Sedgewick + Flajolet, AoA + AC

\section{Timeline and Conclusion}
\label{sec:timeline}

\end{document}
