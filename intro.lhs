%% -*- mode: LaTeX; compile-command: "mk" -*-

%include thesis.fmt

\chapter{Introduction}
\label{chap:intro}

\todo{Probably need to go through and add some subsection headings.}

\bay{Big themes yet to mention: Principle of equivalence. Set theory
  vs type theory, constructive foundations.  Note that this
  dissertation sits in a somewhat awkward place, with feet in both the
  worlds of set theory and type theory; hopefully it can serve as a
  bridge.}

The theory of \term{algebraic data types} has had a profound impact on
the practice of programming, especially in functional languages.  The
basic idea is that types can be built up \term{algebraically} from a
small set of primitive types and combinators: a unit type, base types,
sums (\ie\ tagged unions), products (\ie\ tupling), and recursion.
Most languages with support for algebraic data types also add various
bells and whistles for convenience (such as labeled products and sums,
convenient syntax for defining types as a ``sum of products'', and
pattern matching), but the basic idea is unchanged.

For example, in Haskell~\citep{haskell} we can define a type of binary
trees with integer values stored in the leaves as follows:
\begin{code}
data Tree  =  Leaf Int
           |  Branch Tree Tree
\end{code}

Algebraically, we can think of this as defining the type which is the
least solution to the equation $T = \Int + T \times T$.  This
description says that a |Tree| is either an |Int| (tagged with |Leaf|)
or a pair of two recursive occurrences of |Trees| (tagged with
|Branch|).

This algebraic view of data types has many benefits. From a
theoretical point of view, recursive algebraic data types can be
interpreted as \emph{initial algebras} (or \emph{final coalgebras}),
which gives rise to an entire theory---both semantically elegant and
practical---of programming with recursive data structures via
\term{folds} and \term{unfolds} \citep{bananas, gibbons-calcfp}. A
fold gives a principled way to compute a ``summary value'' from a data
structure; dually, an unfold builds up a data structure from an
initial ``seed value''.  For example, a fold for |Tree| can be
implemented as
\begin{code}
treeFold :: (Int -> a) -> (a -> a -> a) -> Tree -> a
treeFold f _ (Leaf i)      = f i
treeFold f g (Branch l r)  = g (treeFold f g l) (treeFold f g r)
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
type---in fact, it is not hard to automatically generate the fold for
a data type, given its algebraic description.  There are several
Haskell libraries which can do this generation, including
|derive|~\citep{derive} and |DrIFT|~\citep{DrIFT}. The Charity
programming language~\citep{charity} was also designed so that all
computation over inductive types was based on automatically-derived
folds.

% % Folds are ubiquitous---even languages without direct support for
% % algebraic data types often make use of them.  For example, \emph{How
% %   to Design Programs}~\cite[\S 9.4]{HTDP}, a popular introductory
% % programming text using the Scheme (now Racket~\citep{racket})
% % programming language, teaches students to write folds over recursive
% % data types (although it does not use that terminology).  The
% % \emph{visitor pattern}~\citep{GoF,palsberg:essence}, often used in
% % object-oriented languages, can also be seen as a type of fold.

Folds (and unfolds) satisfy many theorems which aid in transforming,
optimizing, and reasoning about programs defined in terms of them.  As
a simple example, a map (\ie\ applying the same function to every
element of a container) followed by a fold can always be rewritten as
a single fold. These laws, and others, allow Haskell compilers to
eliminate intermediate data structures through an optimization called
deforestation~\citep{Wadler:1988,Gill93ashort}.

An algebraic view of data types also enables \term{datatype-generic
  programming}---writing functions which operate generically over
\emph{any} algebraic data type by examining its algebraic structure.
For example, the following function (defined using Generic
Haskell-like
syntax~\citep{Hinze-2000-generic-Haskell,generic-haskell}) finds the
product of all the |Int| values contained in a value of \emph{any}
algebraic data type.  It gives the same result as |treeProd| on
|Trees| but also works on lists or any other type.
\begin{spec}
genProd {| Int         |} i        = i
genProd {| Sum t1 t2   |} (Inl x)  = genProd {| t1 |} x
genProd {| Sum t1 t2   |} (Inr x)  = genProd {| t2 |} x
genProd {| Prod t1 t2  |} (x,y)    = genProd {| t1 |} x * genProd {| t2 |} y
genProd {| _           |} _        = 1
\end{spec}
Datatype-generic programming is a powerful technique for reducing
boilerplate, made possible by the algebraic view of data types, and
supported by many Haskell libraries and
extensions~\citep{Jansson:PolyP,Lammel:SYB,Cheney:LIG,weirich:replib,weirich:erasure}.

The theory of \term{combinatorial species} has been similarly
successful in the area of combinatorics.  First introduced by
\citet{joyal}, it is a unified theory of \term{combinatorial
  structures} or \term{shapes}. Its immediate goal was to generalize
the existing theory of \term{generating functions}, a central tool in
\term{enumerative combinatorics} (the branch of mathematics concerned
with counting abstract structures). \todo{More details here? What has
  it accomplished?  Unifies generating function techniques.  Elegantly
  rederive classical results in combinatorics, e.g. Cayley on number
  of trees, combinatorial interpretation \& proof of Lagrange
  inversion, \& some new results (?)}

Both the theory of algebraic data types and the theory of
combinatorial species have a similar algebraic flavor.  For example,
the \emph{species} of binary parenthesizations (\ie binary trees with
data stored in the leaves) can be defined by the recursive species
equation \[ \Sp{P} = \X + \Sp{P} \cdot \X \cdot \Sp{P} \] which
closely parallels the Haskell definition given above.  This is
tantalizing, since the theory of functional programming languages has
a long history of fruitful borrowing from pure mathematics, as, for
example, in the case of category theory.  However, there has yet to be
a comprehensive treatment of the precise connections between the
theory of algebraic data types and the theory of combinatorial
species. \citet{bll} give a comprehensive treatment of the theory of
species, but their book is written primarily from a mathematical point
of view and is only tangentially concerned with issues of computation.
It is also written in a style that makes it relatively inaccessible to
researchers in the programming languages community---it assumes quite
a bit of mathematical background that many PL researchers do not have.

The connection between species and computation was first explored by
Flajolet, Salvy, and Zimmermann, with their work on
LUO~\citep{FlajoletSalvyZimmermann1989a,FlSa95}, allowing the use of
species in automated algorithm analysis.  However, their work was all
carried out in a dynamically typed setting.

The first to think about species specifically in the context of
strongly typed functional programming were Carette and Uszkay
\citep{Carette_Uszkay_2008_species}, who explored the potential of
species as a framework to extend the usual notion of algebraic data
types, and described some preliminary work adding species types to
Haskell.  More recently, Joachim Kock has done some theoretical work
generalizing species, ``container types'', and several other notions
of ``extended data type''~\citep{kock2012data}.  \todo{What to say
  about this?  Something about Homotopy Type Theory.  It used to say
  ``Via Kock's work, it looks like there may be some interesting
  connections between the theory of species and the recent work in
  Homotopy Type Theory---though it remains quite inaccessible to most
  in the programming languages community.''}

The investigations in this dissertation all arise from considering the
central question, \textbf{what is the connection between species and
  algebraic data types?}  A precise connection between the two could
have many exciting implications.  For example, it would allow taking
much of the mathematical theory developed on the basis of
species---for example, enumeration, uniform random generation of
structures via Boltzmann sampling \todo{cite}, \todo{what else?}---and
applying it directly to algebraic data types.  It is also possible
that exploring the theory of species in an explicitly computational
setting will yield additional insights that can be contributed back
into a combinatorial setting.

There is also the promise of using species not just as a tool to
understand and work with algebraic data types in better ways, but
directly as a foundation upon which to build (a richer notion) of
algebraic data types.  This is particularly interesting due to the
ability of the theory of species to talk about structures which do not
correspond to algebraic data types---particularly structures which
involve \term{symmetry} and \term{sharing}.

A data structure with \term{symmetry} is one whose elements can be
permuted in certain ways without affecting its identity.  For example,
permuting the elements of a bag always results in the same bag.
Likewise, the elements of an ordered cycle may be cyclically permuted
without affecting the cycle.  By contrast, a typical binary tree
structure has no symmetry: any permutation of the elements may result
in a different tree.  In fact, every algebraic data structure has no
symmetry, since every element in an algebraic structure can be
uniquely identified by a \emph{path} from the root of the structure to
the element, so permuting the elements always results in an observably
different value.

\todo{More about symmetry---example pictures or something?}

A data structure with \term{sharing} is one in which different parts
of the structure may refer to the same subpart.  For example, consider
the type of undirected, simple graphs, consisting of a set of vertices
together with a set of edges connecting pairs of vertices.  In
general, such graphs may involve sharing, since multiple edges may
refer to the same vertex, and vice versa.

In a language with first-class pointers, creating data structures with
sharing is relatively easy, although writing correct programs that
manipulate them may be another story. The same holds true for many
languages without first-class pointers as well. Creating data
structures with sharing in the heap is not difficult in Haskell, but
it may be difficult or even impossible to express the programs that
manipulate them.

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
tricks~\citep{Gill-2009-sharing}) in either of these examples. Even
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

The grand vision of this research program, then, is to create and
exploit a bridge between the theory of species and the theory and
practice of programming languages. This dissertation represents just a
first step in this research program, laying the theoretical groundwork
necessary for its continued pursuit.

\todo{subsection here?}

To even get started building a bridge between species and data types
requires a lot more than one might na\"ively expect.  The fundamental
problem is that the theory of species is traditionally couched in
untyped, classical set theory.  To talk about data types, however, we
want to work in \emph{typed} and \emph{constructive} foundations.
Attempting to port species to a typed, constructive setting reveals
many implicit assumptions that must be made explicit, as well as
implicit uses of reasoning principles, such as the axiom of choice,
which are incompatible with constructive foundations.  The bulk of
\pref{chap:equality} is dedicated to the required \todo{what} which
makes it possible to \todo{what}.