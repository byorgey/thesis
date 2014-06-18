%% -*- mode: LaTeX; compile-command: "mk" -*-

%include thesis.fmt

%format iota = "\iota"

\chapter{Labelled structures}
\label{chap:labelled}

Now that we have a foundation for describing labelled shapes, the next
step is to extend them into full-blown \emph{data structures} by
adjoining mappings from labels to data.  For example,
\pref{fig:shape-data} illustrates an example of a labelled shape
together with a mapping from the labels to data values.
\begin{figure}
\centering
\begin{diagram}[width=400]
import SpeciesDiagrams
dia = shapePlusData # centerXY # pad 1.1

shapePlusData = hcat
  [ octo' elt "species!"
  , strutX 2
  , text "=" # fontSizeL 3 <> phantom (square 1 :: D R2)
  , strutX 2
  , octo [0..7]
  , strutX 2
  , text "×" # fontSizeL 3 <> phantom (square 1 :: D R2)
  , strutX 2
  , mapping
  , strutX 2
  ]

mapping = centerXY . vcat' (with & sep .~ 0.2) . map mapsto $ zip [0..7] "species!"
mapsto (l,x) = hcat' (with & sep .~ 0.5) [mloc l, a, elt x]
  where
    a = (arrow' (with & headLength .~ Local 1) 2 <> hrule 2) |||||| strutX 0.4
\end{diagram}
%$
\caption{Data structure = shape + data} \label{fig:shape-data}
\end{figure}
However, this must be done in a principled way which allows deriving
properties of labelled structures from corresponding properties of
labelled shapes.  This chapter begins with an overview of \term{Kan
  extensions} (\pref{sec:kan-extensions}) and \term{analytic functors}
(\pref{sec:analytic-functors}), which provide the theoretical basis
for extending labelled shapes to labelled structures.  \todo{Continue
  this description/outline once the rest of the chapter shakes out.}

\section{Kan extensions}
\label{sec:kan-extensions}

The definition of analytic functors, given in
\pref{sec:analytic-functors}, makes central use of the notion of a
(left) \term{Kan extension}.  This section defines Kan extensions and
provides some useful intuition for understanding them in this
context. For more details, see \citet[Chapter X]{mac1998categories};
for some good intuition with a computational bent, see
\citet{hinze2012kan}.

\begin{defn} \label{defn:lan} Given functors $F : \C \to \D$ and $J :
  \C \to \E$, the \term{left Kan extension of $F$ along $J$}, written
  $\lan J F$\footnote{$\lan J F$ is traditionally notated $\Lan_J F$.
    Inspired by the corresponding notion in relational algebra, Roland
    Backhouse suggested the notation $\ran J F$ for the right Kan
    extension of $F$ along $J$, which was adopted by
    \citet{hinze2012kan}.  This notation is a bit more perspicuous
    than the traditional notation $\Ran_J F$, especially with respect
    to the accompanying computation ($\beta$) and reflection ($\eta$)
    laws.  Unfortunately, there is not quite a satisfactory parallel
    in the case of left Kan extensions.  In relational algebra, the
    notations $A / P$ and $P \backslash A$ are used for the right
    adjoints to pre- and post-composition, respectively; whereas we
    want notations for the left and right adjoints of precomposition.
    I nevertheless adopt the notation $\lan J F$ for left Kan
    extensions, and hope this does not cause confusion.}, is a functor
  $\E \to \D$ characterized by the isomorphism
  \begin{equation} \label{eq:lan}
    (\nt {\lan{J}{F}} G) \iso (\nt F {G \comp J}),
  \end{equation}
  natural in $G$. (Note that the left-hand side consists of natural
  transformations between functors $\E \to \D$, whereas the right-hand
  side are between functors $\C \to \D$.) If this isomorphism exists
  for all $F$, then we may say even more succinctly that the left Kan
  extension functor $\lan J -$ is left adjoint to the precomposition
  functor $- \comp J$.
\end{defn}

The situation can be pictured as shown below: \[ \xymatrix{\C
  \ar[dr]^{F} \ar[d]_J \\ \E \ar[r]_{\lan J F} & \D } \] Intuitively,
if $J : \C \to \E$ is thought of as an ``embedding'' of $\C$ into
$\E$, then $\lan J F$ can be thought of as a way of ``extending'' the
domain of $F$ from $\C$ to $\E$ in a way compatible with $J$. If we
substitute $\lan J F$ for $G$ in \pref{eq:lan} and take the image of
$\id_{\lan J F}$, we obtain $\eta : F \to (\lan J F) \comp J$, a
natural transformation sending $F$ to the embedding $J$ followed by
the extension $\lan J F$. Intuitively, the existence of $\eta$
guarantees that $\lan J F$ has to ``act like'' $F$ on the image of
$\C$ under $J$. \todo{2-cell picture illustrating $\eta$} Of course,
$\lan J F$ must also be defined and functorial on all of $\E$, not
just on the image of $C$.  These facts together justify thinking of
$\lan J F$ as an ``extension'' of $F$.  Note also that substituting $G
\comp J$ for $F$ in \pref{eq:lan} and taking the image of $\id_{G\comp
  J}$ under the inverse yields $\varepsilon : \lan J {(G \comp J)} \to
G$, which can be thought of as a computation or reduction rule.

\todo{simple example(s)?}

The above gives an abstract characterization of left Kan extensions;
under suitable conditions we can explicitly construct them.
\begin{prop} \label{prop:Lan-coend}
When $\D$ is cocomplete and \todo{what?}, $\lan J F$ can be
constructed explicitly as a coend:
\begin{equation} \label{eq:lan-coend}
  (\lan J F)\ E = \coend{C} (J\ C \to E) \cdot F\ C.
\end{equation}
\end{prop}
As a Haskell type, this construction corresponds to
\begin{spec}
data Lan j f a where
  Lan :: (f c, j c -> a) -> Lan j f a
\end{spec}
The @kan-extensions@ package~\citep{kmett-kan-extensions-hackage}
contains a similar definition. Of course, this type is quite a bit
less general than the abstract definition given above---in particular,
it instantiates $\C$, $\D$, and $\E$ all to \Hask.  However, it is
still quite useful for gaining intuition.  Note that |c| is
existentially quantified; recall that in Haskell this corresponds to a
coend.  Note also that the copower (which in general relates two
different categories) turns into simple pairing.

We now turn to a proof of \pref{prop:Lan-coend}. \todo{Need to mention
  Fubini somewhere.}
\begin{proof}
We must show $(\nt {\lan J F} G) \iso (\nt F {G \comp J})$.
\begin{sproof}
  \stmt{\nt {\lan J F} G}
  \reason{\jeq}{definition}
  \stmt{\nt {(\coend{C} (J\ C \to -) \cdot F\ C)} G}
  \reason{\iso}{natural transformations are ends}
  \stmt{\eend{E} \left( \coend{C} (J\ C \to E) \cdot F\ C \right) \to G\ E}
  \reason{\iso}{$(- \to X)$ turns colimits into limits}
  \stmt{\eend{E} \eend{C} \left( (J\ C \to E) \cdot F\ C \to G\ E
    \right)}
  \reason{\iso}{currying}
  \stmt{\eend{E} \eend{C} (J\ C \to E) \to (F\ C \to G\ E)}
  \reason{\iso}{Fubini}
  \stmt{\eend{C} \eend{E} (J\ C \to E) \to (F\ C \to G\ E)}
  \reason{\iso}{Yoneda}
  \stmt{\eend{C} F\ C \to G\ (J\ C)}
  \reason{\iso}{natural transformations are ends}
  \stmt{\nt F {G \comp J}}
\end{sproof}
\end{proof}

Instead of merely showing the \emph{existence} of an isomorphism, the
above proof can in fact be interpreted as constructing a specific one:
each step has some constructive justification, and the final
isomorphism is the composition of all the steps.  However, instead of
formally expounding this isomorphism, it is useful to carry out the
construction in Haskell, using the type |Lan| defined above. This
brings out the essential components of the proof without getting too
bogged down in abstraction.  The code corresponding to the backwards
direction of the proof is shown in \pref{fig:lan-coend-Hask} (note
that it requires the |GADTs| and |RankNTypes| extensions~\citep{GADTs,
  RankNTypes}).\footnote{As evidenced by the @kan-extensions@
  package~\citep{kmett-kan-extensions-hackage}, the implementation of
  this constructive proof in Haskell can be considerably simplified,
  but at the expense of obscuring the connection to the original
  abstract proof given above.} The code for the forward direction is
similar, and it is the backwards direction which will be of particular
use later.
\begin{figure}
  \centering
\begin{spec}
lanAdjoint :: Functor g => (forall c. f c -> g (j c)) -> (forall a. Lan j f a -> g a)
lanAdjoint h = homL (uncurry (yoneda' h))
  where
    -- Turn a forall outside an arrow into an existential to the left
    -- of the arrow
    homL :: (forall a c. (f c, j c -> a) -> g a) -> (forall a. Lan j f a -> g a)
    homL h (Lan (fc, jc_a)) = h (fc, jc_a)

    -- One direction of the Yoneda lemma.
    yoneda :: Functor f => f c -> (forall a. (c -> a) -> f a)
    yoneda fc h = fmap h fc

    -- A particular instantiation of |yoneda|. This needs to be
    -- declared and given a type signature, since there are higher-
    -- rank types involved which GHC is not able to infer.
    yoneda'  ::  Functor g
             =>  (forall c. f c ->  g (j c)                        )
             ->  (forall c. f c ->  (forall a. (j c -> a) -> g a)  )
    yoneda' h fc = yoneda (h fc)
\end{spec}
  \caption{Proof of \pref{prop:Lan-coend} in Haskell}
  \label{fig:lan-coend-Hask}
\end{figure}

\section{Analytic functors}
\label{sec:analytic-functors}

\todo{Apparently the terminology ``analytic'' is not due to Joyal? See
  \url{http://en.wikipedia.org/wiki/Calculus_of_functors}.}

We are now ready to consider Joyal's definition of \term{analytic
  functors}~\citep{Joyal86}.
\begin{defn}[Joyal]
  Given a species $F \in [\B,\Set]$, the \term{analytic functor}
  $\analytic F$ corresponding to $F$ is given by $\lan \iota F$, the
  left Kan extension of $F$ along the inclusion functor $\iota : \B
  \inj \Set$. A functor $\Set \to \Set$ is \term{analytic} when it
  arises in this way from some species.
\end{defn}
\[ \xymatrix{\B
  \ar[dr]^{F} \ar@@{_{(}->}[d]_\iota \\ \Set \ar[r]_{\analytic F} & \Set } \]
We can think of $\analytic F$ as the polymorphic ``data type'' arising from
the species $F$. The construction in \pref{prop:Lan-coend} tells us
exactly what such a data type looks like: \[ \analytic F\ A = \coend L (\iota
L \to A) \times F\ L. \]  That is, given a set $A$, a value in $\analytic F\
A$ consists of an $L$-labelled $F$-shape together with a function (\ie
a morphism in $\Set$) from $\iota L$ to $A$.  The coend means that the
choice of a particular label set $L$ does not matter: any two values
$f : (\iota L \to A) \times F\ L$ and $g : (\iota L' \to A) \times F\
L' $ are considered equal if there is some bijection $\sigma : L \bij
L'$ which sends $f$ to $g$.

Moreover, the natural isomorphism \eqref{eq:lan} in this case
becomes \[ (\nt {\analytic F} G) \iso (\nt F {G \iota}), \] that is,
the natural maps (\ie parametrically polymorphic functions) out of
$\analytic F$ are in one-to-one correspondence with species morphisms
out of $F$.  The isomorphism constructed in \pref{fig:lan-coend-Hask}
can give us some insight into the computational content of this
correspondence.  We identify both $\B$ and $\Set$ with
\Hask---formally dubious but close enough for intuition---and thus the
inclusion functor $\iota : \B \to \Set$ becomes the identity.  Let |h
:: forall c. f c -> g c| be an arbitrary natural transformation from
|f| to |g = g . iota|, which should be thought of as a morphism
between species, that is, between functors $\B \to \Set$.
|lanAdjoint| turns such species morphisms into polymorphic functions
(that is, natural transformations between $\Set \to \Set$ functors)
from |Lan iota f a| to |g a|.  In particular, let |Lan (sp,m)| be a
value of type |Lan iota f a|, containing, for some label type |c|, a
shape |sp : f c| and a mapping |m : iota c -> a|.  Then |lanAdjoint h
(Lan (sp,m))| has type |g a|, and we can carry out the following
simplication just by unfolding definitions:
\begin{sproof}
  \stmt{|lanAdjoint h (Lan (sp,m))|}
  \reason{=}{definition of |lanAdjoint|}
  \stmt{|homL (uncurry (yoneda' h)) (Lan (sp,m))|}
  \reason{=}{definition of |homL|}
  \stmt{|uncurry (yoneda' h) (sp,m)|}
  \reason{=}{definition of |uncurry|}
  \stmt{|yoneda' h sp m|}
  \reason{=}{definition of |yoneda'|}
  \stmt{|yoneda (h sp) m|}
  \reason{=}{definition of |yoneda|}
  \stmt{|fmap m (h sp)|.}
\end{sproof}
This can be interpreted as follows: given the species morphism |h| out
of the species $F$, it is turned into a function out of the
corresponding analytic functor $\analytic F$ by applying it to the
underlying shape, and then functorially applying the associated data
mapping.  Note in particular that |lanAdjoint| is an
\emph{isomorphism}, which means that \emph{every} polymorphic function
out of an analytic functor arises in this way.  That is, every
polymorphic function out of $\analytic F\ A$ is ``just a reshaping'': it is
equivalent to a process consisting of splitting $\analytic F\ A$ into a
labelled shape and a mapping from labels to data, followed by a
``reshaping''---an application some species morphism to the
shape---and concluding with re-combining the new shape with the data
mapping.

Such a reshaping only has access to the labelled shape, and not to the
values of type $A$, so it obviously cannot depend on them. However,
this is not surprising, since this property is already implied by
naturality.  More interesting is the fact that the set of labels must
be finite. This means, intuitively, that functors corresponding to
infinite data structures are not analytic.  It is not possible to
represent all possible natural maps out of an infinite data structure
by natural maps out of structures containing only a finite number of
labels.  This is proved more formally in \pref{sec:analytic-finite}.

\todo{What is the relationship with ``shapely types''?}

Analytic functors have many nice properties: for example, they are
closed under sums, products, composition, and least fixed
points. \todo{cite. Joyal?} \todo{Expand.  Give a bit more
  context/justification.}

\subsection{Analytic functors and generating functions}
\label{sec:analytic-generating}

Another nice property of analytic functors is that they have
corresponding \term{generating functions} (indeed, a big part of the
motivation of Joyal's work seems to have been to categorify the
existing theory of generating functions).  In fact, passing from $\B$
to $\P$, suppose we have a species $F : \P \to \Set$; then the
analytic functor $\analytic F$ is given by \[ \analytic F\ A =
\coend{(n:\N)} (\iota n \to A) \times F\ n, \] where $\iota : \P \to
\Set$ in this case sends the natural number $n$ to the set $\fin n$.
Note that functions $\fin n \to A$ are in bijection with the $n$-fold
product $A^n$, so $\analytic F\ A$ may equivalently be expressed as \[
\analytic F\ A = \coend{(n:\N)} F\ n \times A^n. \] The coend, in this
case, is a quotient by permutations on $\fin n$, which act on $F\ n
\times A^n$ by permuting the elements of the $n$-fold product.  So
each value of the coend is an equivalence class of $n!$ pairs, one for
each possible permutation of $A^n$. We may therefore suggestively (if
informally) write
\[ \analytic F\ A = \sum_{n : \N} F\ n \times \frac{A^n}{n!} \] which
very strongly resembles the \term{exponential generating function}
associated to the species $F$, \[ F(x) = \sum_{n \geq 0} ||F\ n||
\times \frac{x^n}{n!}. \] Of course, the resemblance is no accident;
this gives a glimpse of the sense in which analytic functors are said
to be a categorification of such generating functions. \todo{Explain
  formally?}

\subsection{Analytic functors and finiteness}
\label{sec:analytic-finite}

\citet{Joyal86} characterized analytic functors as those which
preserve \term{filtered colimits}, \term{cofiltered limits}, and
\term{weak pullbacks}.  It is instructive to use this characterization
as a lens to consider some examples of functors which are \emph{not}
analytic.

\begin{defn}
  A \term{filtered} category $\C$ \citep{adamek2002classification} is
  one which ``has all finite cocones'', that is, for any finite
  collection of objects and morphisms in $\C$, there is some object $C
  \in \C$ with morphisms from all the objects in the collection to
  $C$, such that all the relevant triangles commute.

  Equivalently, and more simply, a filtered category is one for which
  \begin{itemize}
  \item there exists at least one object;
  \item any two objects $C_1, C_2 \in \C$ have an ``upper bound'',
    that is, an object $C_3$ with morphisms \[ \Cospan {C_1} {} {C_3}
    {} {C_2}; \]
  \item and finally, any two parallel morphisms $\Parallel {C_1} f g
    {C_2}$ also have an ``upper bound'', that is, another morphism \[
    \xymatrix{C_1 \ar@@<.5ex>[r]^{f} \ar@@<-.5ex>[r]_{g} & C_2
      \ar[r]^h & C_3} \] such that $f \then h = g \then h$.
  \end{itemize}
  These binary upper bound operations on objects and morphisms may be
  used to inductively ``build up'' cocones for arbitrary diagrams in
  $\C$.
\end{defn}

This can be seen as a ``categorification'' of the notion of a
\term{directed set} (also known as a \term{filtered set}), a preorder
in which any two elements have an upper bound.  Categories can be seen
as generalizations of preorders in which multiple morphisms are
allowed between each pair of objects, so the above definition has to
extend the idea of pairwise upper bounds to apply to parallel
morphisms as well as objects; in a preorder there are no parallel
morphisms so this does not come up.

\begin{ex}
  Any category with a terminal object is filtered: the terminal object
  may be taken as the upper bound of any two objects, and the unique
  morphism to the terminal object as the upper bound of any two
  parallel morphisms.
\end{ex}

\begin{ex}
  The poset $(\N,\leq)$, considered as a category whose objects are
  natural numbers, with morphisms $m \leq n$, is a filtered
  category. The upper bound of any two objects is their maximum, and
  there are no parallel morphisms to consider.

  \[ \xymatrix{0 \ar[r] & 1 \ar[r] & 2 \ar[r] & 3 \ar[r] & \dots} \]

  Note that filteredness only requires that every \emph{finite}
  collection of objects have an upper bound; in particular, in this example it is
  not true of \emph{infinite} collections of objects.  For example,
  the set of all even numbers has no natural number upper bound.

  \todo{Historically, this was one of the main examples from which the
    idea of filtered categories was generalized.  Iterated limits,
    etc.}
\end{ex}

 \todo{Some example of a filtered category with nontrivial
    parallel morphisms, which is not cocomplete?}

\begin{ex}
  Consider the category $\FinNSub$ whose objects are finite subsets of
  $\N$ and whose morphisms are inclusion maps.  That is, whenever $S
  \subseteq T$ there is a single morphism $\iota_{ST} : S \to T$
  defined by $\iota_{ST}(s) = s$.  Since this is a nonempty preorder,
  it suffices to note that any two finite sets $S$ and $T$ have $S
  \union T$ as an upper bound.
\end{ex}

\begin{ex}
  Filtered categories are also a generalization of finitely cocomplete
  categories, \ie categories having all finite colimits.  In
  particular, categories having all finite colimits can be
  characterized as those having an initial object, all binary
  coproducts, and all coequalizers: these are exactly parallel to the
  three criteria given above for filtered categories, with an extra
  ``universal property'' corresponding to each (for example, the
  binary coproduct of two objects is an upper bound along with a
  universal property).

  Therefore, any (finitely) cocomplete category is automatically
  filtered: for example, $\Set$, $\Grp$, and $\Vect$.
\end{ex}

Recall that a \term{diagram} in $\C$ is a functor $\I \to \C$ from
some ``index category'' $\I$, which determines the ``shape'' of
diagrams in $\C$.

\begin{defn}
  A \term{filtered diagram} in $\C$ is a functor $\I \to \C$ from a
  filtered index category $\I$.  A \term{filtered colimit} is a
  colimit of a filtered diagram.
\end{defn}

That is, a filtered diagram in $\C$ is a diagram that ``looks like'' a
filtered category ``sitting inside'' $\C$.  A filtered colimit is
then just a normal colimit which happens to be taken over a filtered
diagram.

\begin{ex}
  Let $F : \C \to \C$ be an endofunctor on the category $\C$. Suppose
  $\C$ contains an initial object $0$, and let $!$ denote the unique
  morphism $0 \to C$.  Then consider the diagram \[ \xymatrix{ 0
    \ar[r]^{!} & F 0 \ar[r]^{F !} & F^2 0 \ar[r]^{F^2 !} & F^3 0
    \ar[r] & \dots} \] The colimit of this diagram is the fixed point
  $\mu F$, and is a filtered colimit since the diagram has the
  filtered poset $(\N, \leq)$ as its index category.
\end{ex}

\begin{ex}
  Pushouts are an example of colimits which are \emph{not} filtered,
  since pushouts are colimits over a span $\Span X {} Z {} Y$, which
  is not filtered ($X$ and $Y$ have no upper bound).
\end{ex}

\begin{ex}
  Recall the filtered poset $\FinNSub$ introduced earlier, consisting
  of finite subsets of $\N$ and inclusion maps.  The inclusion functor
  $\FinNSub \inj \Set$ allows viewing $\FinNSub$ as a diagram in
  $\Set$, and we consider the (filtered) colimit of this diagram,
  which must consist of some set $S$ along with maps from all the
  finite subsets of $\N$ into $S$, which commute with the inclusion
  maps among the finite subsets of $\N$.  In fact, it suffices to take
  $\N$ itself, together with the inclusion maps from each finite
  subset of $\N$ into $\N$.  Intuitively, $\N$ arises here as the
  disjoint union of all finite subsets of $\N$, quotiented by the
  relationships induced by all the inclusion maps---which collapses
  the disjointness, resulting in a simple union of all finite subsets.

  To show that this is universal, suppose \todo{finish.}
\end{ex}

Now consider the functor $F \defeq (-)^\N : \Set \to \Set$, which
sends the set $A$ to the set $A^\N$ of functions from $\N$ to
$A$.\footnote{This example is due to \citet{trimble-not-analytic}.}
The claim is that $F$ is not analytic, and in particular that it does
not preserve the filtered colimit of $\FinNSub$, discussed above.  As
we will see, the ``problem'' is that $F$ corresponds to an
\emph{infinite} data type, \ie one which can contain infinitely many
$A$ values.  In particular, $F$ corresponds to the data type of \emph{infinite
  streams}: a function $\N \to A$ can be thought of as an infinite
stream of $A$ values, where the value of the function at $n$ gives the
value of $A$ located at position $n$ in the stream.

We also consider how $F$ acts on inclusion maps.  The action of $F$ on
morphisms is given by postcomposition, so $F$ sends the inclusion
$\iota : S \inj T$ to $\iota \comp - : S^\N \to T^\N$, which is also
an inclusion map: it sends the stream $s : \N \to S$ to the stream
$\iota \comp s : \N \to T$, consisting of the application of $\iota$
to every element in $s$.  That is, $\iota \comp -$ does not actually
modify any values of a stream, but simply codifies the observation
that whenever $S \subseteq T$, a stream containing only values from
$S$ may also be thought of as a stream containing only values from $T$
(which simply happens not to include any values from $T - S$).

We saw above that the colimit of $\FinNSub$, considered as a diagram
in $\Set$, is $\N$ (together with the obvious inclusion maps to $\N$
from each finite subset).  $F$ sends $\N$ to $\N^\N$, the type of
infinite streams of natural numbers.  $F$ also sends each inclusion
map $S \inj \N$ to the inclusion $S^\N \inj \N^\N$, which allows a
stream of $S$ values to be ``upgraded'' to a stream of natural
numbers.

Now consider where $F$ sends the diagram $\FinNSub$.  $F$ sends each
finite set $S \subset \N$ to the set of infinite streams of $S$
values, $S^\N$, and it sends each inclusion $S \inj T$ to the
inclusion $S^\N \inj T^\N$.  However, the colimit of this new diagram
$F( \FinNSub)$ is not $\N^\N$, the set of streams of natural numbers,
but instead the set of \emph{finitely supported} streams of natural
numbers, that is, the set of all streams which contain only finitely
many distinct elements.  Thus $F\ (\colim \FinNSub) \ncong \colim (F\
\FinNSub)$, and we conclude that $F$ is not analytic since it does not
preserve filtered colimits.

\later{Give a bit more intuition about this example.}

Another example\footnote{Also due to \citet{trimble-not-analytic}.} is
given by the covariant power set functor $P : \Set \to \Set$, which
sends each set $A$ to its power set $P(A)$, the set of all subsets of
$A$, and sends each function $f : A \to B$ to the function $P(f) :
P(A) \to P(B)$ which gives the image of a subset of $A$ under $f$.
$P(\N)$ is the set of all (finite and infinite) subsets of $\N$, but
$\colim P(\FinNSub)$ is the set of all \emph{finite} subsets of $\N$.
Note, however, that the covariant finite powerset functor $FP : \Set
\to \Set$, which sends each set $A$ to the set of all its
\emph{finite} subsets, is analytic; it corresponds to the species
$\Bag^2$ (or, more accurately, to $\Bag \cdot \Rubbish$).

\subsection{Analytic functors in HoTT}
\label{sec:analytic-functors-hott}

The definition of analytic functors ports almost unchanged into
homotopy type theory: we merely replace the set-theoretic categories
$\B$ and $\Set$ with the homotopy-theoretic $\BT$ and $\ST$,
respectively.  Then we have
\begin{defn}
Given an \hott{functor} $F : \BT \to \ST$, the analytic \hott{functor}
$\analytic F : \ST \to \ST$ is defined as $\analytic F \hdefeq \lan
\iota F$, where $\iota : \BT \inj \ST$ is the evident injection.
\end{defn}
Note that the definition of a Kan extension needs no modification; we
simply use the appropriate notions of natural isomorphism and
adjunction as defined in HoTT.

Again, Kan extensions can be explicitly constructed via coends, and we
have \[ \analytic F\ A = \coend L (\hom[\ST] {\iota\ L} A) \times F\
L. \]  Recalling that coends in HoTT are just $\Sigma$-types, and that
morphisms in $\ST$ are functions, we have \[ \analytic F\ A = \sum_{L
  : \BT} (\iota\ L \to A) \times F\ L. \]

\section{Labelled structures}
\label{sec:labelled-structures}

$\analytic F$ thus represents the ``data type'' corresponding to the
species $F$, whose values consist of a labelled $F$-shape paired with
a map assigning a data value to each label.  It will be convenient,
however, to be able to explicitly work with label types.

\newcommand{\lab}[1]{\langle #1 \rangle}
\newcommand{\LStr}[3]{{\lab #1}_{#2}\ {#3}}

\begin{defn}
  Given a species $F$, the type of \term{labelled structures} over $F$
  is a bifunctor $\lab F : \B \times \Set \to \Set$,
  defined by \[ \LStr F L A = (\iota L \to A) \times F\ L. \]
\end{defn}

We evidently have $\analytic F\ A = \coend L \LStr F L A$, that is,
labelled structures are obtained from analytic functors by ``taking
the coend off'', exposing the set of labels as a parameter.

Note that the same definition applies equally well in HoTT, replacing
$\B$ and $\Set$ with $\BT$ and $\ST$.  Note, however, that
functoriality of $\lab F$ in the labels depends crucially on $\B$ (and
$\BT$) being groupoids, since $L$ appears both co- and contravariantly
in the definition of $\LStr F L A$.

To generalize labelled structures to $[\Lab,\Str]$-species where
$\Lab$ is not a groupoid, \todo{Generalize.  Need two label type
  parameters for positive and negative occurrences?  \emph{e.g.} can
  we use category of partial bijections, \ie prisms?} \bay{Wait and
  see whether/how we actually end up needing this.}

\section{Operations on labelled structures}
\label{sec:labelled-operations}

\todo{Edit. Dumped here from description of product from paper.}

%%% XXX remove me
\newcommand{\under}[1]{\floor{#1}}
\newcommand{\lift}[1]{\ceil{#1}}

One introduces a labelled $(F \sprod G)$-shape by pairing a labelled
$F$-shape and a labelled $G$-shape, using a label set isomorphic to
the coproduct of the two label types:
\begin{align*}
  - \sprod_- - &: (\under{L_1} + \under{L_2} \equiv \under{L}) \to F\ L_1
  \to G\ L_2 \to (F \sprod G)\ L \\
  - \lab{\sprod}_- - &: (\under{L_1} + \under{L_2} \equiv \under{L}) \to \LStr F {L_1} A \to \LStr G {L_2} A \to
  \LStr {F \sprod G} L A
\end{align*}
We use here (and for the rest of the paper) the notational convention that
the isomorphism arguments are given first, but are written as subscripts
in mathematical notation.



%% XXX remove me
\newcommand{\StoreNP}{\mapsto}

\todo{Edit. Dumped here from paper.}

As an example, we may now encode the standard algebraic data type of
lists, represented by the inductively-defined species satisfying
$\List \equiv \One + (\X \sprod \List)$ (for convenience, in what
follows we leave implicit the constructor witnessing this
equivalence).  We can then define the usual constructors $\cons{nil}$
and $\cons{cons}$ as follows:
\begin{align*}
  &\cons{nil} : \LStr{\List}{\Fin 0} A \\
  &\cons{nil} \defeq \lab{\inl} \lab{\One} \\
  &\cons{cons} : A \to \LStr \List L A \to (\Fin 1 + \under L \equiv
  \under{L'}) \to \LStr \List {L'} A \\
  &\cons{cons}\ a\ (|shape|,|elts|)\ e \defeq (\inr\ (\cons{x} \sprod_e
  |shape|), |append|\ e\ (|allocate|\ (\lambda x. a))\ |elts|)
\end{align*}
The interesting thing to note here is the extra equivalence passed as
an argument to $\cons{cons}$, specifying the precise way in which the
old label type augmented with an extra distinguished label is
isomorphic to the new label type.  Again, one might intuitively expect
something like \[ \cons{cons} : A \to \LStr \List L A \to \LStr \List
{\lift{\Fin 1} + L} A, \] but this is nonsensical: we cannot take the
coproduct of two elements of $\FinType$, as it is underspecified.  For
implementations of $\StoreNP - -$ which make use of the equivalence to
$\Fin n$ stored in $\FinType$ values (we give an example of one such
implementation in \pref{sec:vecmap}), the extra equivalence given as
an argument to \cons{cons} allows us to influence the particular way
in which the list elements are stored in memory.  For lists, this is
not very interesting, and we would typically use a variant $\cons{cons'}
: A \to \LStr \List L A \to \LStr \List {\cons{inc}(L)} A$ making use of a
canonical construction $\cons{inc}(-) : \FinType \to \FinType$ with
$\Fin 1 + \under L \equiv \under{\cons{inc}(L)}$.

\section{Sharing}
\label{sec:sharing}

That is, multiple parts of the same shape can all ``point to'' the
same data.  In pure functional languages such as Haskell or Agda,
sharing is a (mostly) unobservable operational detail; with a labelled
structure we can directly model and observe
it. \pref{fig:tree-list-cp} illustrates the Cartesian product of a
binary tree and a list.
\begin{figure}
  \centering
  \begin{diagram}[width=200]
import           Data.List.Split
import           Diagrams.TwoD.Layout.Tree
import           Diagrams.TwoD.Path.Metafont

import           SpeciesDiagrams

leaf1 = circle 1 # fc white # named "l1"
leaf2 = circle 1 # fc white # named "l2"

tree = maybe mempty (renderTree (const leaf1) (~~))
     . symmLayoutBin' (with & slVSep .~ 4 & slHSep .~ 6)
     $ (BNode () (BNode () (BNode () Empty (BNode () Empty Empty)) Empty) (BNode () (BNode () Empty Empty) (BNode () Empty Empty)))

listL shp l = hcat . replicate 7 $ (shp # fc white # named l)

connectAll l1 l2 perm =
  withNameAll l1 $ \l1s ->
  withNameAll l2 $ \l2s ->
  applyAll (zipWith conn l1s (perm l2s))

conn l1 l2 = beneath (lc grey . metafont $ location l1 .- leaving unit_Y <> arriving unit_Y -. endpt (location l2))

dia = vcat' (with & sep .~ 5)
  [ hcat' (with & sep .~ 5)
    [ tree # centerY
    , listL (circle 1) "l2" # centerY
    ] # centerXY
  , listL (square 2) "s" # centerXY
  ]
  # connectAll "l1" "s" id
  # connectAll "l2" "s" (concat . map reverse . chunksOf 2)
  # centerXY # sized (Width 4) # pad 1.1
  \end{diagram}%$
  \caption{Superimposing a tree and a list on shared data}
  \label{fig:tree-list-cp}
\end{figure}

\section{Recursion and the implicit species theorem}
\label{sec:recursion}

\todo{Write me}

\section{Other stuff}

\todo{Discuss variant of $\Bag$ which stores no data.}

\todo{Discuss decomposition of structures using category of partial
  isomorphisms for labels?}

\todo{Examples. Bounded tree width.  Generic programming.}

\todo{Apply combinatorics?  e.g. generating trees.  Random generation,
  Boltzmann sampling...}

\todo{Stick in a bit of the generating functions story?  Just enough
  to show where it's going?  With some applications to enumeration or
  counting etc.  Maybe put it in a future work section---can be very
  concrete.}
