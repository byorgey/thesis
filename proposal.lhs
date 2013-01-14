% -*- mode: LaTeX; compile-command: "lhs2tex proposal.lhs > proposal.tex && pdflatex --enable-write18 proposal.tex" -*-

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

The overarching goal of the proposed research is to ``extract the
juice'' from the theory of species \todo{finish}

% In particular, we want to extend the theory of algebraic data types to
% a theory of \emph{species data types}. A programming language with
% support for species would raise the level of abstraction available to
% programmers, making it easier for them to express programs that are
% closer to what they really \emph{mean}, instead of being forced to
% ``encode'' their intended meaning using the constructs available to
% them.

\section{Combinatorial Species}
\label{sec:species}

\todo{Background on combinatorial species.}

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

One thing that's important to get straight from the beginning is that we
are talking about structures with \emph{labeled locations}. The
\textbf{numbers in the picture above are \emph{not} data} being stored
in the structures, but \emph{names} or \emph{labels} for the locations.
To talk about a \emph{data structure} (\emph{i.e.} a structure filled
with data), we would have to also specify a mapping from locations to
data, like
$\{ 0 \mapsto \texttt{'s'}, 1 \mapsto \texttt{'p'}, 2 \mapsto \texttt{'e'} \dots \}$.

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
when we get to talking about operations like Cartesian product and
functor composition, since it gives us a way to model sharing (albeit
only in limited ways).

Why have labels at all? In the tree shown above, we can uniquely
identify each location by a path from the root of the tree, without
referencing their labels at all. However, the other structure
illustrates one reason why labels are needed. The circle is supposed to
indicate that the structure has \emph{rotational symmetry}, so there
would be no way to uniquely refer to any location other than by giving
them labels.

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

\todo{explain about using $[n]$ as canonical set of labels, etc.; size
is all that matters.}

\subsection{Building Species Algebraically}
\label{sec:building-species}

The formal definition of species is wonderfully simple, but working
directly with the definition in practice does not get one very far.
Instead, we use an algebraic theory that lets us compositionally build
up certain species from a collection of primitive species and species
operations. (It's important to note that it does \emph{not} allow us
to build \emph{all} species, but it does allow us to build many of the
ones we care about.)

\subsubsection{Primitives}
\label{sec:primitives}

We begin with a few primitive species:

\begin{itemize}
\item
  The \emph{zero} or \emph{empty} species, denoted $\mathbf{0}$, is the
  unique species with no structures whatsoever; that is,

  $\mathbf{0}[U] = \emptyset$

  and

  $\mathbf{0}[\sigma : U \leftrightarrow V] = id_{\emptyset} : \mathbf{0}[U] \to \mathbf{0}[V]$.

  Of course, $\mathbf{0}$ will turn out to be the identity element for
  species sum (which I'll define in my next post, though it's not hard
  to figure out what it should mean).
\item
  The \emph{unit} species, denoted $\mathbf{1}$, is defined by

  $\begin{array}{lcl}\mathbf{1}[\emptyset] &=& \{\star\} \\ \mathbf{1}[U] &=& \emptyset \qquad (U \neq \emptyset)\end{array}$

  That is, there is a unique $\mathbf{1}$-structure indexed by the empty
  set of labels, and no $\mathbf{1}$-structures with any positive number
  of labels. $\mathbf{1}$ lifts bijections in the obvious way, sending
  every bijection to the appropriate identity function.

  Some people initially find this definition surprising, expecting
  something like $\mathbf{1}[U] = \{ \star \}$ for all $U$ instead. That
  is indeed a valid species, and we will meet it below; but as I hope
  you will come to see, it doesn't deserve the name $\mathbf{1}$.

  Of course we should also verify that this definition satisfies the
  requisite functoriality properties, which is not difficult.

  More abstractly, for those who know some category theory, it's worth
  mentioning that $\mathbf{1}$ can be defined as
  $\mathbb{B}(\emptyset, -) : \mathbb{B} \to \mathbb{E}$, that is, the
  covariant hom-functor sending each finite set $U \in \mathbb{B}$ to
  the (finite) set of bijections $\emptyset \leftrightarrow U$. (This
  is why I wanted to think of species as functors $\mathbb{B} \to
  \mathbb{E}$. I learned this fact from Yeh~\citet{yeh}.) There is, of
  course, a unique bijection $\emptyset \leftrightarrow \emptyset$ and
  no bijections $\emptyset \leftrightarrow U$ for nonempty $U$, thus
  giving rise to the definition above.

  As you might expect, $\mathbf{1}$ will be the identity element for
  species product. Like $\mathbf{1}$ itself, species product isn't
  defined quite as most people would initially guess. If you haven't
  seen it before, you might like to try working out how product can be
  defined in order to make $\mathbf{1}$ an identity element.
\item
  The \emph{singleton} species, denoted $\mathbf{X}$, is defined by

  $\mathbf{X}[U] = \begin{cases} U & |U| = 1 \\ \emptyset & \text{otherwise} \end{cases}$

  with lifting of bijections defined in the evident manner. That is,
  there is a single $\mathbf{X}$-structure on a label set of size $1$
  (which we identify with the label itself, though we could have also
  defined $\mathbf{X}[U] = \{\star\}$ when $|U| = 1$), and no
  $\mathbf{X}$-structures indexed by any other number of labels.

  As with $\mathbf{1}$, we may equivalently define $\mathbf{X}$ as a
  hom-functor, namely $\mathbf{X} = \mathbb{B}(\{\star\}, -)$.

  It's worth noting again that although $\mathbf{1}$ and $\mathbf{X}$ do
  ``case analysis'' on the label set $U$, they actually only depend on
  the \emph{size} of $U$; indeed, as we
  \href{http://byorgey.wordpress.com/2012/12/06/species-definition-clarification-and-exercises/}{noted
  previously}, by functoriality this is all they can do.
\item
  The species of \emph{bags}\footnote{The species literature calls this
    the species of \emph{sets}, but that's misleading to computer
    scientists, who expect the word ``set'' to imply that elements
    cannot be repeated.}, denoted $\mathbf{E}$, is defined by

  $\mathbf{E}[U] = \{U\}$,

  that is, there is a single $\mathbf{E}$-structure on any set of labels
  $U$, which we usually identify with the set of labels itself (although
  we could equivalently define $\mathbf{E}[U] = \{\star\}$). The idea is
  that an $\mathbf{E}$-structure consists solely of a collection of
  labels, with no imposed ordering whatsoever.

  If you want to abuse types slightly, one can define $\mathbf{E}$ as
  a hom-functor too, namely $\mathbb{E}(-,\{\star\})$. (\citet{yeh}
  actually has $\mathbb{B}(-, \{\star\})$, but that's wrong.)
\end{itemize}

As a summary, \pref{fig:prims} contains a graphic showing
$\mathbf{0}$-, $\mathbf{1}$-, $\mathbf{X}$-, and
$\mathbf{E}$-structures arranged by size (\emph{i.e.}, the size of the
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

Just as a teaser, it turns out that $\mathbf{X}$ and $\mathbf{E}$ are
identity elements for certain binary operations on species as well,
though you'll have to wait to find out which ones!

\subsubsection{Operations}
\label{sec:operations}

\subsection{Equipotence, Isomorphism, and Unlabeled Species}
\label{sec:unlabeled}

We say that two species are \term{equipotent} when there exists a
family of bijections $\phi_U : F[U] \bij G[U]$, that is, there are the
same number of $F$- and $G$-structures of each size.  Although this
notion is occasionally useful, it is rather weak.  More useful is the
notion of species \term{isomorphism}: two species are isomorphic
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
For example, the species $X + X$ and $2X$ are isomorphic,
\todo{explain why}.  As an example of species which are equipotent but
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
isomorphic $F$-structures).

\section{Species as Data Types}
\label{sec:species-types}

\section{The \pkg{species} library}
\label{sec:species-library}

\section{Enumerating Unlabeled Structures}
\label{sec:enumerating}

\section{Doing Other Stuff}

\todo{Need to figure out what other stuff to propose!  Views? Sharing?
  L-species? Virtual species? Species + infinity?  Enumerating
  unlabeled structures?  See NSF proposal for ideas, of course.}

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

\section{Timeline and Conclusion}
\label{sec:timeline}

\end{document}
