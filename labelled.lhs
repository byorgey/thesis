%% -*- mode: LaTeX; compile-command: "mk" -*-

%include thesis.fmt

%format iota = "\iota"
%format <=<  = "<\!\!=\!\!<"

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
  package~\citep{kmett-kan-extensions}, the implementation of
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

\todo{Introduce definition as functors having a Taylor series first
  (like Joyal)?}

We are now ready to consider Joyal's definition of \term{analytic
  functors}~\citep{Joyal86}.
\begin{defn}[Joyal]
  Given a species $F : \fc \B \Set$, the \term{analytic functor}
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

\subsection{Simple labelled structures}
\label{sec:simple-labelled}

\begin{defn}
  Given a species $F$, the type of \term{labelled structures} over $F$
  is a bifunctor $\lab F : \B \times \Set \to \Set$,
  defined by \[ \LStr F L A = (\iota L \to A) \times F\ L. \]
\end{defn}

We evidently have $\analytic F\ A = \coend L \LStr F L A$, that is,
labelled structures are obtained from analytic functors by ``taking
the coend off'', exposing the set of labels as a parameter.
$\LStr F L -$ is clearly functorial.  Note, however, that $L$ appears
both co- and contravariantly, so $\LStr F - A$ is functorial only if
$\Lab$ is a groupoid, in which case $\LStr F \sigma A = (\iota
(\sigma^{-1}) \to A) \times F \sigma$.

Note that the same definition applies equally well in HoTT, replacing
$\B$ and $\Set$ with $\BT$ and $\ST$.

\subsection{Generalized labelled structures}
\label{sec:generalized-labelled}

To generalize labelled structures to $(\fc \Lab \Str)$-species where
$\Lab$ is not a groupoid, we must split the parameter $L$ into two,
one each for the contravariant and covariant occurrences: \[ \GLStr F
K L A \defeq (\iota K \to A) \times F\ L. \]

\subsection{Partial bijections}
\label{sec:partial-bijections}

\todo{This needs to be moved! Where?  To Equality chapter?  Or to end
  of species chapter?}

As a larger running example, we develop the theory of finite sets and
\term{partial bijections}, bijection-like functions which are allowed
to be partial in one direction.  Such partial bijections form a
category, $\BTSub$, which we put to work as the category of labels for
generalized notion of species (\todo{forward reference}).  The
development will be carried out in HoTT, though it works equally well
in set theory.

\begin{rem}
  A \term{bijection} in HoTT is taken to be a pair of inverse
  functions. Recall that in general, this may not be the same as an
  \emph{equivalence}, although in the specific case of sets
  ($0$-types) the notions of bijection and equivalence do coincide.
  The following discussion sticks mostly to the terminology of
  ``bijections'' but may occasionally mention ``equivalences'' as well.
\end{rem}

The basic idea is to introduce a type of evidence witnessing the fact
that one set ($0$-type) is a ``subset'' of another, written $A
\pbij B$.\footnote{There should be no problem in generalizing
  partial bijections to partial equivalences which work over any
  types, using an appropriate notion of partial adjoint equivalences.
  However, there is no need for such generalization in the present
  work, so we stick to the simpler case of $0$-types.} Of course there
is no subtyping in HoTT, so there is no literal sense in which one
type can be a subset of another. However, the situation can be
modelled using constructive evidence for the embedding of one type
into another.  In order to focus the discussion, we begin with partial
bijections between arbitrary sets, and only later restrict to finite
ones.

\begin{defn} \label{defn:pbij}
  A \term{partial bijection} $f : A \pbij B$ between two sets $A$
  and $B$ is given by:
\begin{itemize}
\item an embedding function $\embed f : A \to B$ (in a slight abuse of
  notation, we will often simply use $f$, rather than $\embed f$, to
  refer to the embedding function),
\item a projection function $\project f : B \to \TyOne + A$,
\end{itemize}
together with two round-trip laws:
\begin{itemize}
\item $\project f \comp \embed f = \inr$, and
\item for all $a: A$ and $b : B$, if $\project f\ b = \inr\ a$
  then $\embed f\ a = b$.
\end{itemize}
\end{defn}

That is, $A \pbij B$ witnesses that there is a $1$-$1$
correspondence between all the elements of $A$ and \emph{some}
(possibly all) of the elements of $B$, as pictured in
\pref{fig:partial-bijection}. This concept is also known as a
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
  \embed f\ a$. Conversely,
  \begin{sproof}
    \stmt{\embed f\ a = b}
    \reason{\implies}{apply $\project f$ to both sides}
    \stmt{\project f\ (\embed f\ a) = \project f\ b}
    \reason{\iff}{first round-trip law}
    \stmt{\inr\ a = \project f\ b.}
  \end{sproof}
\end{proof}

\begin{rem}
  Equation \eqref{eq:rt-adj} is strongly reminiscent of an adjunction.  However,
  I do not know whether there is a suitable sense in which it can
  actually be seen as one.
\end{rem}


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
  \caption{A typical partial bijection}
  \label{fig:partial-bijection}
\end{figure}

As an aid in discussing partial bijections we define $\pInv(f)$ which
together with $f : A \to B$ constitutes a partial bijection $A
\pbij B$.

\begin{defn}
  A \term{partial inverse} $\pInv(f)$ to $f : A \to B$ is defined so
  that \[ (A \pbij B) \jeq (f : A \to B) \times \pInv(f), \] that
  is, \[ \pInv(f) \hdefeq (g : B \to \TyOne + A) \times (\all {a b}
  (f\ a = b) \lequiv (\inr\ a = g\ b)). \]
\end{defn}

We also define some notation to make working with partial bijections
more convenient.

\begin{defn}
  First, for any types $A$ and $B$, there is a canonical partial
  bijection $A \pbij A + B$, which we denote simply by $\inl$;
  similarly, $\inr : B \pbij A + B$.

  For the remainder, assume there is a partial bijection $p : K \pbij
  L$.
  \begin{itemize}
  \item $\embed p\ K$ denotes the image of $K$ under $p$, that is, the
    set of values in $L$ in the range of $\embed p$; we often simply
    write $p\ K$ instead of $\embed p\ K$.
  \item $\restr K p : K \bij p\ K$ denotes the bijection
    between $K$ and the image of $K$ in $L$.
  \item When some $q : K' \pbij K$ is understood from the context, we
    also write $\restr {K'} p$ as an abbreviation for $\restr {K'} {(p
      \comp q)}$, the bijection between $K'$ and the image of $K'$ in
    $L$ under the composite $(p \comp q)$.
  \item $\extra p = \{ l : L \mid \project l = \inl\ \unit \}$ denotes
    the ``extra'' values in $L$ which are not in the image of $K$.
  \item $\extrabij p$ denotes the canonical bijection $K + \extra p
    \bij L$. \todo{better notation for this?}
  \end{itemize}
\end{defn}

We now turn to the category structure on partial bijections.

\begin{prop}
  Partial bijections compose, that is, there is an associative
  operation \[ - \comp - : (B \pbij C) \to (A \pbij B) \to (A
  \pbij C). \]
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
  \caption{Composition of partial bijections}
  \label{fig:partial-bij-compose}
\end{figure}

\begin{proof}
  This can be intuitively grasped by studying a diagram such as the
  one shown in \pref{fig:partial-bij-compose}.

  More formally, we set $\embed{(g \comp f)} = \embed g \comp \embed f$ and
  $\project{(g \comp f)} = \project f \kcomp \project g$, where $-
  \kcomp -$ denotes Kleisli composition for the $\TyOne + -$ monad
  (\ie |(<=<) :: (b -> Maybe c) -> (a -> Maybe b) -> (a -> Maybe c)|
  in Haskell). Associativity thus follows from the associativity of
  function composition and Kleisli composition.

  \todo{Need to explain |=<<| somewhere.}

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
    \reason{\iff}{definition of |=<<|; case analysis}
    \stmt{\inr\ a = \project f |=<<| \project g\ c}
    \reason{\iff}{Kleisli composition}
    \stmt{\inr\ a = (\project f \kcomp \project g)\ c}
    \reason{\iff}{definition}
    \stmt{\inr\ a = \project {(g \comp f)}\ c}
  \end{sproof}
\end{proof}

\begin{prop}
  Partial bijections form an \hott{category}, $\STSub$, with sets as
  objects.
\end{prop}

\begin{proof}
  The identity morphism $\id : A \pbij A$ is given by $\embed \id
  = \id$ and $\project \id = \inr$.  The identity laws follow from the
  fact that $\id$ is the identity for function composition, and $\inr$
  is the identity for Kleisli composition.

  $\BTSub$ is thus a precategory.  It remains only to show that
  isomorphism is equivalent to equality.  An isomorphism $A \iso B$ is
  given by $f : A \pbij B$ and $g : B \pbij A$ such that $f
  \comp g = \id = g \comp f$.  Note that we have $\embed f : A \to B$
  and $\embed g : B \to A$ with $\embed f \comp \embed g = \embed{(f
    \comp g)} = \embed \id = \id$, and likewise for $\embed g \comp
  \embed f$.  Thus, $\embed f$ and $\embed g$ constitute a bijection
  $A \bij B$; since $A$ and $B$ are sets, this is the same as an
  equivalence $A \equiv B$, and hence by univalence an equality $A =
  B$.
\end{proof}

\begin{rem}
  Note that a bijection $f : A \bij B$ can be made into a partial
  bijection $h : A \pbij B$ trivially by setting $\embed h = f$ and
  $\project h = \inr \comp f^{-1}$, and moreover that this is a
  homomorphism with respect to composition; that is, the category of
  bijections embeds into the category of partial bijections as a
  subcategory.  We will usually not bother to note the conversion,
  simply using bijections as if they were partial bijections when
  convenient.\footnote{In fact, using the \pkg{lens} library---and
    more generally, using a van Laarhoven formulation of
    lenses~\cite{XXX}---this all works out automatically: the
    representations of bijections (isomorphisms) and partial
    bijections (prisms) are such that the former simply \emph{are} the
    latter, and they compose as one would expect (albeit
    ``backwards''), using the standard function composition operator.}
\end{rem}

\subsection{Finite partial bijections}
\label{sec:fin-partial-bijections}

Finally, we turn to the theory of partial bijections on \emph{finite}
sets. In the case of finite sets, it turns out that partial bijections
$A \pbij B$ can be more simply characterized as injective
functions $A \inj B$.  This might seem ``obvious'', and indeed, it is
straightforward in a classical setting.  One direction, namely,
converting a partial bijection into an injection, is straightforward
in HoTT as well (\pref{lem:pbij-is-inj}). However, to produce a
partial bijection from an injection, we must be able to recover the
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
  Note that $\isInjective(f)$ is a mere proposition when $A$ is a set.
  Given $i, j : \isInjective(f)$, for all $a_1, a_2 : A$ and $e : f\ a_1
  = f\ a_2$, we have $i\ a_1\ a_2\ e = j\ a_1\ a_2\ e$ (since they are
  parallel paths between elements of a set) and hence $i = j$ by
  function extensionality.
\end{rem}

\begin{lem} \label{lem:pbij-is-inj}
  Every partial bijection is an injection, that is, $(A \pbij B)
  \to (A \inj B)$.
\end{lem}

\begin{proof}
  Let $f : A \pbij B$.  Then $\embed f : A \to B$ is
  injective:
  \begin{sproof}
    \stmt{\embed f\ a_1 = \embed f\ a_2}
    \reason{\implies}{apply $\project f$ to both sides}
    \stmt{\project f\ (\embed f\ a_1) = \project f\ (\embed f\ a_2)}
    \reason{\iff}{$f$ is a partial bijection}
    \stmt{\inr\ a_1 = \inr\ a_2}
    \reason{\iff}{$\inr$ is injective}
    \stmt{a_1 = a_2}
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
  \item Next, suppose $g\ b = \inr\ a$ and $g'\ b = \inr\ a'$.  Then
    by $p$ and $p'$ we have $f\ a = b = f\ a'$, whence $a = a'$
    since by \pref{lem:pbij-is-inj} we know $f$ is injective.
  \item Finally, suppose $g\ b = \inr\ a$ and $g'\ b = \inl\ \unit$
    (the other case is symmetric).  In that case $f\ a = b$ by $p$,
    and hence, substituting, $g'\ (f\ a) = \inl\ \unit$.  However,
    recall that $p'$ implies $g'\ (f\ a) = \inr\ a$, a contradiction.
  \end{itemize}

  Letting $r : g = g'$ denote the equality just constructed, we
  complete the argument by noting that $r_*(p)$ and $p'$ are parallel
  paths between elements of a set, and hence equal.
\end{proof}

\begin{lem} \label{lem:inj-is-pbij}
  If $A$ is a finite set and $B$ a set with decidable equality,
  then \[ (A \inj B) \to (A \pbij B). \]
\end{lem}

\begin{proof}
  Let $f : A \to B$ be an injective function; we must construct $h : A
  \pbij B$.  First, we set $\embed h = f$.  It remains to
  construct $\pInv(\embed h)$, which is a mere proposition by
  \pref{lem:pinv-mere-prop}.  Thus, by the recursion principle for
  propositional truncation, we are justified in using the constructive
  evidence of $A$'s finiteness, that is, its cardinality $n : \N$ and
  equivalence $\sigma : A \equiv \Fin n$.  We define $\project h : B \to
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

\todo{Remark about finiteness and decidable equality.  Add it to
  equality chapter.}

\begin{prop} \label{prop:inj-equiv-pbij}
  For $A$ a finite set and $B$ a set with decidable equality,
  \[ (A \inj B) \equiv (A \pbij B). \]
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
  Denote by $\BTSub$ the \hott{category} of finite sets and partial
  bijections (\ie injections).  That is, objects in $\BTSub$ are
  values of type $\FinSetT \jeq (A : \Type) \times \isSet(A) \times
  \isFinite(A)$, and morphisms $\hom[\BTSub] {(A,s_a,f_a)}
  {(B,s_b,f_b)}$ are partial bijections $A \pbij B$.  Showing that
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
  (\pref{cor:BT-iso-PT}).  We define a functor $\fin{-}_{\pbij} :
  \PTSub \to \BTSub$ which sends $n$ to $(\Fin n, s,
  \ptruncI{(n,\id)})$ (just like the functor $\fin - : \PT \to \BT$
  defined in \pref{defn:functor-fin}), and which sends $\iota :
  \hom[\PT] m n \jeq \Fin m \inj \Fin n$ to the corresponding partial
  bijection (\pref{prop:inj-equiv-pbij}).  It is not hard to show that
  this functor is full, faithful, and essentially surjective, which by
  \pref{prop:splitEssSurj-equiv} and \pref{cor:essSurj-splitEssSurj}
  implies that $\fin{-}_{\pbij} : \PTSub \to \BTSub$ is one half of an
  equivalence. \later{actually flesh this out?}
\end{proof}

\subsection{The Gordon complementary bijection principle}

Suppose $A_0, A_1, B_0, B_1$ are types with bijections $f_0 : A_0 \bij
B_0$ and $f_1 : A_1 \bij B_1$.  Then it's clear how to construct a
bijection $f : A_0 + A_1 \bij B_0 + B_1$: one just takes $f
= f_0 + f_1$, as illustrated in \pref{fig:adding-bijections}.

\begin{figure}
  \centering
  \begin{diagram}[width=200]
import Bijections

dia =
  (vcat' (with & sep .~ 1) . map centerX)
  [ hcat' (with & sep .~ 2)
    [ drawBComplex $ bc0 # labelBC "f₀"  -- $
    , plus
    , drawBComplex $ bc1 # labelBC "f₁"  -- $
    ]
  , equals
  , drawBComplex $ parC bc0 bc1 # labelBC "f = f₀ + f₁"  -- $
  ]
  # centerXY
  # frame 0.5
  # lwO 0.7
  \end{diagram}
  \caption{Adding bijections}
  \label{fig:adding-bijections}
\end{figure}

So computing the ``sum'' of two bijections is not hard. What about the
\emph{difference}?  That is, given $f : A_0 + A_1 \bij B_0 + B_1$ and
$f_1 : A_1 \bij B_1$, can we compute some $f_0 : A_0 \bij B_0$
(\pref{fig:subtracting-bijections})?

\begin{figure}
  \centering
  \begin{diagram}[width=200]
import           Bijections

dia =
  (vcat' (with & sep .~ 1) . map centerX)
  [ hcat' (with & sep .~ 2)
    [ drawBComplex $   -- $
      [a0,a1] .- bij01 # labelBij "f" -.. [b0,b1]
    , minus
    , drawBComplex $ bc1 # labelBC "f₁"  -- $
    ]
  , equals
  , mconcat
    [ text' 3 "?"
    , drawBComplex $ [a0] .- emptyBij # labelBij "f₀" -.. [b0]  -- $
    ]
  ]
  # centerXY
  # frame 0.5
  # lwO 0.7
  \end{diagram}
  \caption{Subtracting bijections?}
  \label{fig:subtracting-bijections}
\end{figure}

Though it is obvious that $\size A_0 = \size B_0$, it is not \latin{a
  priori} obvious whether it is possible to actually construct a
bijection between them.  The problem, as can be seen in
\pref{fig:subtracting-bijections}, is that $f$ may mix up elements
among the $A_i$ and $B_i$---that is, one cannot simply, say, take the
restriction of $f$ to $A_0$, since the image of $A_0$ under $f$ may
intersect both $B_0$ and $B_1$.

However, it turns out that this is possible, via the \term{Gordon
  complementary bijection principle} \todo{cite}.  You might want to
stop and think about it for a while at this point.  If you know some
Haskell, try filling in the definition of `subtractIso`:

> {-# LANGUAGE TypeOperators #-}
>
> import Prelude hiding ((.), id)
> import Control.Category
>
> data a :<->: b = (a -> b) :<->: (b -> a)
>   -- Invariant: the two functions are inverse.
>
> applyIso :: (a :<->: b) -> (a -> b)
> applyIso (f :<->: _) = f
>
> invert :: (a :<->: b) -> (b :<->: a)
> invert (f :<->: g) = (g :<->: f)
>
> instance Category (:<->:) where
>   id = id :<->: id
>   (f1 :<->: g1) . (f2 :<->: g2) = (f1 . f2) :<->: (g2 . g1)
>
> subtractIso :: (Either a0 a1 :<->: Either b0 b1) -> (a1 :<->: b1) -> (a0 :<->: b0)
> subtractIso = undefined

% Instead of defining the GCBP via a bunch of symbols, or even by exhibiting
% some code, I will begin by *drawing* it for you:

% ```{.dia width='450'}
% import           Bijections
% import           Control.Lens ((&), (.~))

% gcbp = drawBComplex . flattenA $
%     bc01' .- ebij1 -. bc01' .- ebij1 -.. bc01'
%   where
%     ebij1 = colorBij colorMap $
%             emptyBij `parBij` (bij1 & labelBij "f₁⁻¹")
%     bc01' = map2 (colorBij colorMap . labelBij "f") bc01
%     colorMap = orbitsToColorMap
%                  [red, green, blue, orange, purple]
%                  (orbits
%                    (bijToRel bij01)
%                    (bijToRel ebij1)
%                  )

% gcbpEqn =
%   (vcat' (with & sep .~ 1) . map centerX)
%   [ hcat' (with & sep .~ 2)
%     [ drawBComplex $
%       [a0,a1] .- bij01 # labelBij "f" -.. [b0,b1]
%     , minus
%     , drawBComplex $ bc1 # labelBC "f₁"
%     ]
%   , equals
%   , gcbp
%   ]

% -- XXX draw resulting bijection

% dia = gcbpEqn
%   # centerXY # pad 1.1
%   # sized (Width 2)
% ```

% Here's the idea in words: start with an element in $A_0$ (that's the
% yellow set in the illustration above), and apply $f$.  If we get something in $B_0$ (blue),
% great---we're done!  Otherwise, we have something in $B_1$ (red), so
% we apply $f_1^{-1}$ to send us back over to $B_0$ (green), and from
% there we apply $f$ again and repeat.  In the above example, you can
% see that the first two elements of $A_0$ land in $B_0$ immediately;
% for the third, we have to iterate three times (or perhaps we should
% say "two and a half times").

% Here's a more complicated example:

% ```{.dia width='450'}
% import Bijections
% import Control.Lens ((&), (.~))
% import Data.Bits (xor)
% import Data.Typeable (cast)
% import Diagrams.Core.Names

% a2 = nset 4 yellow
% b2 = nset 4 blue
% a3 = nset 5 green
% b3 = nset 5 red

% bc3 = [a3] .- bij3 -.. [b3]

% bij3 = [bijFun [0..4] (Just . (\n -> if n == 4 then 4 else xor 1 n))]

% bij23 = [with & bijData .~ tableToFun tab23]
% tab23 = zip (('a' ||> toNamesI [0..3]) ++ ('b' ||> toNamesI [0..4]))
%             [ 'b' ||@@ 0, 'a' ||@@ 0, 'b' ||@@ 1, 'a' ||@@ 1
%             , 'b' ||@@ 2, 'a' ||@@ 2, 'b' ||@@ 3, 'b' ||@@ 4, 'a' ||@@ 3
%             ]

% bc23 = [a2,a3] .- bij23 -.. [b2,b3]

% gcbp = drawBComplex . flattenA $
%   bc23' .- ebij3 -. bc23' .- ebij3 -. bc23' .- ebij3 -.. bc23'
%   where
%     ebij3 = emptyBij `parBij` (bij3 & labelBij "f₁⁻¹")
%     bc23' = map2 (labelBij "f") bc23

% gcbpEqn =
%   (vcat' (with & sep .~ 1) . map centerX)
%   [ hcat' (with & sep .~ 2)
%     [ drawBComplex $
%       [a2,a3] .- bij23 # labelBij "f" -.. [b2,b3]
%     , minus
%     , drawBComplex $ bc3 # labelBC "f₁"
%     ]
%   , equals
%   , gcbp
%   ]

% dia = gcbpEqn
%   # centerXY # pad 1.1
%   # sized (Width 2)

% ```

% We need to show that this gives a well-defined bijection---that it
% terminates, first of all, and that it gives us a mapping which really
% is a bijection.

% The "usual" proof goes something like this: XXX

% However, we can apprehend the validity of the GCBP more directly and
% intuitively.  Consider "extending to infinity" the iteration in both
% directions.

% XXX picture.

% Since we have created this picture by simply copying the same
% bijections over and over, it obviously has translational
% symmetry---moving it one unit to the left or right doesn't change
% anything.  Let's consider the different types of paths that show up in
% this kind of picture.

% First, can there be bi-infinite paths?  Sure, there can be, but any
% such path must necessarily stay entirely within the bottom half of the
% picture, since the top half of the picture only contains *ends* of
% paths.  Since our goal is to construct a bijection between the top
% sets we can therefore ignore bi-infinite paths.

% Can there be *half*-infinite paths, *i.e.* paths which have a starting
% point in the top half of the picture but then wander around in the
% bottom half forever?  No, because XXX it will intersect its copies
% (explain this better).  Therefore, every path that is not bi-infinite
% must have two endpoints in the top half of the picture.

% Finally, it's easy to see that every point belongs to a unique
% path. (XXX why?)

% The GCBP in Haskell
% -------------------

% Here's my implementation of `subtractIso`:

% > subtractIso' :: (Either a0 a1 :<->: Either b0 b1) -> (a1 :<->: b1) -> (a0 :<->: b0)
% > subtractIso' a0a1__b0b1 a1__b1 =
% >     (iter (applyIso a0a1__b0b1) (applyIso $ invert a1__b1) . Left)
% >     :<->:
% >     (iter (applyIso $ invert a0a1__b0b1) (applyIso $ a1__b1) . Left)
% >   where
% >     iter a0a1_b0b1 b1_a1 a0a1 =
% >       case a0a1_b0b1 a0a1 of
% >         Left  b0 -> b0
% >         Right b1 -> iter a0a1_b0b1 b1_a1 (Right (b1_a1 b1))

% It feels sort of ugly---in fact, it is the exact computational
% analogue of the usual proof of the GCBP (though it's missing quite a
% bit, in particular a proof of termination and a proof that the output
% really is a bijection).  Given that I don't like the usual proof, it's
% no surprise that I find this code ugly.  I don't like the fact that it
% projects functions out of the input bijections and uses them to
% construct the two directions of the output bijection separately.  I'd
% rather work entirely in terms of operations on bijections.  I don't
% know whether that is possible.  I'd be very interested to see what
% others come up with.

% The Garsia-Milne involution principle
% -------------------------------------

% Further reading
% ---------------

% XXX Cite Garsia-Milne paper(s).  Don't recommend actually reading
% it/them.

% Came out of trying to prove partition identities. XXX cite Wilf paper
% tying a bunch of this together.


\begin{prop}[Gordon complementary bijection principle]
  For finite sets $A_1$, $A_2$, $B_1$, and $B_2$, if $A_1 + B_1
  \equiv A_2 + B_2$ and $B_1 \equiv B_2$, then $A_1 \equiv A_2$.
\end{prop}

\todo{Explain intuition.  Can use some text from half-written blog
  post.}

\begin{proof}
  \todo{Figure out a good constructive proof!}
\end{proof}

\subsection{Partial species}
\label{sec:partial-species}

In a combinatorial setting, one is primarily interested in
\emph{counting} \todo{finish.  Computationally we want to model
  partiality.  Give some motivating examples.}

\begin{defn}
  A \term{partial species} is a functor $F : \BTSub \to \ST$.  We
  denote by $\PSpe = \fc \BTSub \ST$ the functor category of partial
  species.
\end{defn}

\begin{rem}
  Since $\BTSub \iso \PTSub$ (\pref{prop:btsub-iso-ptsub}) partial
  species are also equivalent to functors $\PTSub \to \ST$.
\end{rem}

Since the objects of \BTSub\ are the same as the objects of \BT, the
object mapping of a partial species is similar to that of a normal
species.  That is, one can still think of a partial species as mapping
a finite set of labels to a set of structures ``built from'' those
labels.

\todo{use term ``transport'' instead of ``lift''?}
A partial species $F$ also has an action on morphisms: it must lift
any partial bijection $K \pbij L$ to a function $F\ K \to F\ L$.  Of
course, bijections are partial bijections, so this includes the
familiar case of ``relabelling''; bijections are isomorphisms in
$\BTSub$, and functors necessarily preserve isomorphisms, so
bijections on labels are still sent to bijections between structures.

The case of strictly partial bijections, that is, $K \pbij L$ where
$\size K < \size L$, is more interesting.  Each structure in the set
$F\ K$, with labels in $K$, must map to a structure in $F\ L$, given
an embedding of $K$ into $L$.  Intuitively, this can be thought of as
introducing ``extra'' labels which must be incorporated into the
structure in a suitably canonical way.  However, the partial bijection
$p : K \pbij L$ affords no structure whatsoever on the ``extra''
labels (that is, those $l \in L$ for which $\project p\ l = \inl
\unit$).  So it is not acceptable, for example, to prepend the extra
labels to the front of a list structure, since there is no canonical
way to choose an ordering on the extra labels.  The only feasible
approach is to simply attach the extra labels in a \emph{set}, as
illustrated in \pref{fig:lift-strict-pbij}.

\begin{figure}
  \centering
  \todo{make a diagram.  Tree maps to tree + set.}
  \caption{Lifting a strictly partial bijection}
  \label{fig:lift-strict-pbij}
\end{figure}

Moreover, note that one cannot adjoin a \emph{new} set of labels with
every lift.  Performing multiple lifts would then result in multiple
sets of extra labels (\eg a list of such sets), but this fails to be
functorial, since \todo{explain.  Reference diagram.}

\begin{figure}
  \centering
  \todo{make a diagram.  Non-commuting diagram of adjoining multiple
    extra sets vs all at once.}
  \caption{TODO write me}
  \label{fig:XXX}
\end{figure}

So the only option is to have \emph{every} partial species structure
accompanied by a set of ``extra'' labels (which may be
empty). Transporting along a strictly partial bijection results in
some labels being added to the set.

Intuitively, every normal species $F$ gives rise to a partial species
$\prt F$ which ``acts like'' the species $F \cdot \Bag$.  In fact,
along these lines we can formally define a fully faithful embedding of
\Spe into \PSpe.

\todo{Combinatorics of partial species, \eg generating functions.
  Partial species are like having things ``up to'' the given size.
  Explain why there is not an equivalence.  Problem is that partial
  species do not necessarily preserve injectivity.  Talk about
  intuition from generating functions and partial sums.  Can't undo
  operation of taking ``partial sums'' in this case because it might
  not preserve information---ie can't subtract $G\ (n-1)$ from $G\
  n$.}

\begin{defn}
  The functor $\prt - : \Spe \to \PSpe$ is defined as follows.

  First consider the action of $\prt -$ on objects, that is, species
  $F : \BT \to \ST$.  We define $\prt F : \BTSub \to \ST$ as the
  partial species which
  \begin{itemize}
  \item sends the finite set of labels $K$ to the set of structures
    $(F \cdot \Bag)\ K$, and
  \item lifts the partial bijection $p : K \pbij L$ to a function
    $\prt p : \prt F\ K \to \prt F\ L$.  \todo{insert picture here?} This function takes as input
    a structure of type $(F \cdot \Bag)\ K$, that is, a tuple \[ (K_1,
    K_2, f, \unit, \sigma) \] where $f : F\ K_1$ is a $K_1$-labelled
    $F$-structure, the unit value $\unit$ represents a $K_2$-labeled
    set, and $\sigma : K \bij K_1 + K_2$ witnesses that $K_1$ and
    $K_2$ form a partition of the label set $K$.  As output, $\prt p$
    yields \[ (L_1, L_2 + \extra p, F\ (\restr{K_1}{p_1})\ f, \unit,
    \psi), \] where
    \begin{itemize}
    \item $p_1$ is the ``restriction of $p$ to $K_1$'', that is, the
      composite partial bijection
      \[ p_1 : \xymatrix{K_1 \ar[r]^-{\pbij}_-{\inl} & K_1 + K_2
        \ar[r]^-{\sim}_-{\sigma^{-1}} & K \ar[r]^{\pbij}_{p} & L}. \]
      Similarly, $p_2 : K_2 \pbij L$.
    \item $L_1 = p_1\ K_1$ is the image of $K_1$ under the restricted
      partial bijection $p_1$.  Similarly, $L_2 = p_2\ K_2$. Note that
      we ``throw in the extra labels'' by using the coproduct $L_2 +
      \extra p$ as the second set of labels.
    \item Recall that $\restr {K_1} {p_1} : K_1 \bij p_1\ K_1$; thus
      $F\ (\restr {K_1} {p_1})\ f$ denotes the relabelling of the
      $F$-structure $f$ from $K_1$ to $p\ K_1 = L_1$.
    \item $\psi : L \bij L_1 + (L_2 + \extra p)$ is given by the composite
    \[ \xymatrixcolsep{4pc} \xymatrix{L \ar[r]^-{\sim}_-{\extrabij p} & p\ K +
      \extra p} \] \todo{finish.}
    \end{itemize}
  \end{itemize}
  We must verify that this defines a valid functor $\BTSub \to
  \ST$. \todo{finish}

  Next, consider the action of $\prt -$ on morphisms, that is, natural
  transformations $\varphi : \all L F\ L \to G\ L$ where $F$ and $G$
  are species.  Define $(\prt \varphi)_L : \prt F\ L \to \prt G\ L$
  by \[ (L_1, L_2, f, \unit, \sigma) \mapsto (L_1, L_2, \varphi_{L_1}\
  f, \unit, \sigma). \] For this to be natural the following square
  must commute for all $F, G : \BT \to \ST$, all $\varphi : \all L F\
  L \to G\ L$, and all $p : K \pbij L$:
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

\begin{prop}
  $\prt - : \Spe \to \PSpe$ is full.
\end{prop}

\begin{proof}
  \todo{prove me}
\end{proof}

\begin{prop}
  $\prt - : \Spe \to \PSpe$ is faithful.
\end{prop}

\begin{proof}
  \todo{prove me}
\end{proof}

\todo{Is the functor $\prt -$ monoidal? Intuitively, yes for $+$, no
  for $\cdot$.  Probably not for $\comp$.}

\todo{Labelled structures with partial species; memory layout.}

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

\todo{Examples. Bounded tree width.  Generic programming.}

\todo{Apply combinatorics?  e.g. generating trees.  Random generation,
  Boltzmann sampling...}

\todo{Stick in a bit of the generating functions story?  Just enough
  to show where it's going?  With some applications to enumeration or
  counting etc.  Maybe put it in a future work section---can be very
  concrete.}
