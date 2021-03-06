%% -*- mode: LaTeX; compile-command: "mk" -*-

%include thesis.fmt

\chapter{Generalized species and species operations}
\label{chap:generalized-species}

The definition of species, in either set theory or type theory, is
straightforward: species are objects in a certain functor category.
However, it is not the functors themselves which are fundamentally
interesting, but the structure of the functor category.  As we will
see in this chapter, the functor category $\fc \B \Set$ has at least
six different monoidal structures, corresponding to combinatorially
sensible operations on species.

This also opens up the possibility of considering other functor
categories with similar monoidal structures, instead of remaining tied
to $\fc \B \Set$, which is too specific and restrictive.  In
particular, we will consider arbitrary functor categories in place of
traditional species, determining the properties necessary to support
each species operation.  First of all, this allows us to justify $\fc
\BT \ST$ as an analogue of species in HoTT.  Even within the realm of
pure mathematics, however, there are extensions to the basic theory of
species (\eg multisort species, weighted species, $\L$-species, vector
species, \dots) which require generalizing from $\fc \B \Set$ to other
functor categories.

Sections \pref{sec:lifted}--\pref{sec:differentiation} examine species
operations---in particular, the six monoidal structures referred to
above, along with differentiation---in the context of general functor
categories $\fc \Lab \Str$ (where $\Lab$ and $\Str$ are arbitrary
categories), in order to identify precisely what properties of $\Lab$
and $\Str$ are necessary to define each operation. That is, starting
``from scratch'', we will build up a generic notion of species that
supports the operations we are interested in. In the process, we get a
much clearer picture of where the operations ``come from''.  In
particular, $\B$ and \Set enjoy special properties as categories (for
example, \Set is cartesian closed, has all limits and colimits, and so
on), and it is enlightening to see precisely which of these properties
are required in which situations.  Although more general versions of
specific operations have been defined previously
\citep{kelly2005operads, Fiore08, lack2014combinatorial}, I am not
aware of any previous systematic generalization similar to this work.
In particular, the general categorical treatments of arithmetic
product (\pref{sec:arithmetic-product}) and multisort species
(\pref{sec:multisort}) are new.

Along the way, we will explore particular instantiations of the
general framework. Each instantiation arises from considering
particular categories in place of $\B$ and $\Set$.  To keep these
functor categories straight, we will use the word ``species'' for
$\fc \B \Set$, and ``generalized species'' (or, more specifically,
``$(\fc \Lab \Str)$-species'')\footnote{Not to be confused with the
  generalized species of~\citet{Fiore08}, who define
  ``$(A,B)$-species'' as functors from $\B A$ (a generalization of
  $\B$) to $\hat B$, the category of presheaves $B^\op \to \Set$ over
  $B$.} for some abstract $\fc \Lab \Str$.  Each section begins by
defining a particular species operation in $\fc \B \Set$, then
generalizes it to arbitrary functor categories $\fc \Lab \Str$, and
exhibits examples in other functor categories.

The chapter concludes with some comments on the relationship between
symmetry and species operations (\pref{sec:molecular-atomic}) and on
\emph{eliminators} for species (\pref{sec:elim-species}, which become
important when considering species as a basis for data structures, as
in \pref{chap:labelled}.

\section{Lifted monoids: sum and Cartesian product}
\label{sec:lifted}

Two of the simplest operations on species are \emph{sum} and
\emph{Cartesian product}.  These operations are structurally
analogous: the only difference is that species sum arises from
coproducts in $\Set$ (disjoint union), whereas the Cartesian product
of species arises from products in $\Set$.  We first define and give
examples of these operations in the context of $\fc \B \Set$ and then
generalize to other functor categories.

\subsection{Species sum}

The \emph{sum} of two species is given by their disjoint union: an $(F
+ G)$-shape is either an $F$-shape \emph{or} a $G$-shape, together
with a tag to distinguish them.

%   \begin{figure}
%     \centering
%     \begin{diagram}[width=250]
% import SpeciesDiagrams

% theDia
%   = hcat' (with & sep .~ 1)
%     [ struct 5 "F+G"
%     , text' 1 "="
%     , vcat
%       [ struct 5 "F"
%       , text' 0.5 "OR"
%       , struct 5 "G"
%       ]
%       # centerY
%     ]

% dia = theDia # centerXY # pad 1.1
%     \end{diagram}
%     \caption{Species sum}
%     \label{fig:sum}
%   \end{figure}

\begin{defn}
  Given $F, G : \B \to \Set$, their sum $F + G : \B \to \Set$ is
  defined on objects by \[ (F + G)\ L \defeq F\ L \uplus G\ L, \]
  where $\uplus$ denotes disjoint union (coproduct) of sets, and on
  morphisms by \[ (F + G)\ \sigma \defeq F\ \sigma \uplus G\
  \sigma, \] where $\uplus$ is considered as a bifunctor in the
  evident way: $(f \uplus g)\ (\inl\ x) \defeq \inl\ (f\ x)$ and $(f \uplus
  g)\ (\inr\ y) \defeq \inr\ (g\ y)$.
\end{defn}

It remains to prove that the $F + G$ defined above is actually
functorial.
\begin{proof}
  The functoriality of $F + G$ follows from that of $F$, $G$, and
  $\uplus$:
  \[ (F + G)\ id = F\ id \uplus G\ id = id \uplus id = id, \]
  and
  \begin{sproof}
  \stmt{(F + G) (f \comp g)}
  \reason{=}{$+$ definition}
  \stmt{F\ (f \comp g) \uplus G\ (f \comp g)}
  \reason{=}{$F$, $G$ functors}
  \stmt{(F\ f \comp F\ g) \uplus (G\ f \comp G\ g)}
  \reason{=}{$\uplus$ bifunctor}
  \stmt{(F\ f \uplus G\ f) \comp (F\ g \uplus G\ g)}
  \reason{=}{$+$ definition}
  \stmt{(F + G)\ f \comp (F + G)\ g.}
  \end{sproof}
\end{proof}

\begin{rem}
  More abstractly, when defining a functor with a groupoid as its
  domain (such as $F + G$ above), it suffices to specify only its
  action on objects, using an arbitrary expression composed of (co-
  and contravariant) functors.  For example, $(F + G)\ L = F\ L \uplus
  G\ L$ is defined in terms of the functors $F$, $G$, and $\uplus$.
  In that case the action of the functor on morphisms can be derived
  automatically by induction on the structure of the expression,
  simply substituting the morphism in place of covariant occurrences
  of the object, and the morphism's inverse in place of contravariant
  occurrences.  In fact, in HoTT, this is simply transport; that is,
  given an \hott{groupoid} $B$ and a (pre)category $C$, any function
  $B_0 \to C_0$ extends to a functor $B \to C$.

  By the same token, to define a functor with an arbitrary category
  (not necessarily a groupoid) as its domain, it suffices to define
  its action on an object using an expression containing only
  covariant occurrences of the object.

  \later{Flesh this out some more\dots ?  This could all be made formal
  and precise but the idea should be clear, and it's not necessarily
  worth it.  Could also probably find something to cite.}
\end{rem}

\begin{ex}
  $\Bin + \List$ is the species of shapes which are \emph{either}
  binary trees or lists (\pref{fig:bin-plus-list}).
\end{ex}

\begin{figure}
  \centering
  \begin{diagram}[width=250]
import SpeciesDiagrams
import Data.List (permutations)

dia = (hcat' (with & sep .~ 0.5)) (map (tag 1) trees ++ map (tag 2) lists)
    # frame 0.5

trees
  = map (drawBinTreeWide . fmap labT)
  $ enumTrees [0,1 :: Int]

lists
  = map (drawList' labT)
  . permutations
  $ [0,1 :: Int]
  \end{diagram}
  \caption{$(\Bin + \List)\ 2$}
  \label{fig:bin-plus-list}
\end{figure}

\begin{ex}
  As another example, consider $\Bin + \Bin$.  It is important to bear
  in mind that $+$ yields a \emph{disjoint} or ``tagged'' union; so
  $\Bin + \Bin$ consists of \emph{two} copies of every binary tree
  (\pref{fig:bin-plus-bin}), and in particular it is distinct from
  $\Bin$.
\end{ex}

Species sum corresponds to the sum of generating functions: we have \[
(F + G)(x) = F(x) + G(x) \quad \text{and} \quad \unl{(F + G)}(x) =
\unl F(x) + \unl G(x). \] This is because the sum of two generating
functions is computed by summing corresponding coefficients, \[
\left(\sum_{n \geq 0} a_n x^n \right) + \left(\sum_{n \geq 0} b_n
  x^n\right) = \sum_{n \geq 0} (a_n + b_n) x^n \] (and likewise for
egfs), and since species sum is given by disjoint union, the number of
$(F+G)$-shapes and -forms of a given size is the sum of the number of
$F$- and $G$-shapes (respectively -forms) of that size.

\begin{figure}
  \centering
  \begin{diagram}[width=250]
import SpeciesDiagrams

dia = (hcat' (with & sep .~ 0.5)) (map (tag 1) trees ++ map (tag 2) trees)
    # frame 0.5

trees
  = map (drawBinTreeWide . fmap labT)
  $ enumTrees [0,1 :: Int]  -- $
  \end{diagram}
  \caption{$(\Bin + \Bin)\ 2$}
  \label{fig:bin-plus-bin}
\end{figure}

There is also a primitive species which is an identity element for
species sum.

\begin{defn}
  The \term{zero} or \term{empty} species,
  $\Zero$, is the unique species with no shapes whatsoever.  That is,
  on objects,
    $\Zero\ L \defeq \varnothing$,
  and on morphisms $\Zero$ sends every $\sigma$ to the unique function
  $\varnothing \to \varnothing$.
\end{defn}

We evidently have \[ \Zero(x) = \unl \Zero(x) = 0 + 0x + 0x^2 + \dots
= 0. \]

\begin{prop}
  $(+,\Zero)$ is a symmetric monoid on $\fc \B \Set$.
\end{prop}

\begin{proof}
  First, we must show that $+$ is a bifunctor. By definition it sends
  two functors to a functor, but this is only its action on the
  objects of $\Spe$.  We must also specify its action on morphisms,
  that is, natural transformations between species, and we must show
  that it preserves identity natural transformations and (vertical)
  composition of natural transformations.

  In this case it's enough simply to unfold definitions and follow the
  types.  Given species $F$, $F'$, $G$, and $G'$ and natural
  transformations $\phi : \nt F {F'}$ and $\psi : \nt G {G'}$, we
  should have $\phi + \psi : \nt {F+G} {F'+G'}$.  The component of
  $\phi + \psi$ at some $L \in \B$ should thus be a morphism in $\Set$
  of type $F\ L \uplus G\ L \to F'\ L \uplus G'\ L$; the only thing
  that fits the bill is $\phi_L \uplus \psi_L$.

  This nicely fits with the ``elementwise'' definition of $+$ on
  species: $(F + G)\ L = F\ L \uplus G\ L$, and likewise $(\phi +
  \psi)_L = \phi_L \uplus \psi_L$.  The action of $+$ on natural
  transformations thus reduces to the elementwise action of $\uplus$
  on their components.  From this it follows that
  \begin{itemize}
  \item $\phi + \psi$ is natural (because $\phi$ and $\psi$ are), and
  \item $+$ preserves identity and composition (because $\uplus$
    does).
  \end{itemize}
  Finally, we note that $+$ inherits the symmetry of $\uplus$.
\end{proof}

Stepping back a bit, we can see that this monoidal structure on
species arises straightforwardly from the corresponding monoidal
structure on sets: the sum of two functors is defined as the pointwise
coproduct of their outputs, and likewise \Zero, the identity for the
sum of species, is defined as the functor which pointwise returns
$\varnothing$, the identity for the coproduct of sets.  More
generally, any monoidal structure on a category $\Str$ lifts to a
corresponding monoidal structure on a functor category $\fc \Lab \Str$
(this construction is spelled out in \pref{sec:lifting-monoids}).
This leads us naturally to consider another species operation which
arises in the same way, but based on a different monoid.

\subsection{Cartesian/Hadamard product}
\label{sec:cartesian}

The definition of species sum involves \emph{coproducts} in $\Set$.
Of course, $\Set$ also has \emph{products}, given by $S \times T = \{
(s,t) \mid s \in S, t \in T \}$, with any one-element set as the
identity. We may suppose there is some canonical choice of one-element
set, $\singleton$; since there is exactly one bijection between any
two singleton sets, we do not even need the axiom of choice to
implicitly make use of them.  (In type theory, there is by definition
a canonical singleton type $\TyOne$.)
\begin{defn}
  The \term{Cartesian} or \term{Hadamard product} of species is
  defined on objects by $ (F \times G)\ L = F\ L \times G\ L.$
\end{defn}
This is the ``obvious'' definition of product for species, though as
we will see it is not the most natural one from a combinatorial point
of view.  Nonetheless, it is the simplest to define and is thus worth
studying first.  The action of $(F \times G)$ on morphisms,
functoriality, \etc are omitted; the details are exactly parallel to
the definition of species sum, and are presented much more generally
in \pref{sec:lifting-monoids} and \pref{chap:lifting-monoids}.

An $(F \times G)$-shape is both an $F$-shape \emph{and} a $G$-shape,
on \emph{the same set of labels}.  There are several ways to think
about this situation, as illustrated in \pref{fig:Cartesian-product}.
\begin{figure}
  \centering
  \begin{diagram}[width=380]
import           Data.List.Split
import           Diagrams.TwoD.Layout.Tree
import           Diagrams.TwoD.Path.Metafont

import           SpeciesDiagrams

connectAll l1 l2 n perm =
  withNames (map (l1 .>) [0 :: Int .. n-1]) $ \l1s ->
  withNames (map (l2 .>) [0 :: Int .. n-1]) $ \l2s ->
  applyAll (zipWith conn l1s (perm l2s))

conn l1 l2 = beneath (lc grey . metafont $ location l1 .- leaving unit_Y <> arriving unit_Y -. endpt (location l2))
-- $

sharedMem = vcat' (with & sep .~ 5)
  [ hcat' (with & sep .~ 3)
    [ wideTree (mkLeaf (circle 1) . ("l1" .>)) sampleBTree7 # centerY
    , drawList (mkLeaf (circle 1) . ("l2" .>)) 7 # centerY
    ] # centerXY
  , drawList (mkLeaf (square 2) . ("s" .>)) 7 # centerXY
  ]
  # connectAll "l1" "s" 7 perm1
  # connectAll "l2" "s" 7 perm2
  # centerXY # pad 1.1

perm1 = id
perm2 = concat . map reverse . chunksOf 2

asFun :: ([Int] -> [Int]) -> Int -> Int
asFun perm i = perm [0..6] !! i

numbering = hcat' (with & sep .~ 3) . map centerXY $  -- $
  [ wideTree numbered sampleBTree7 # centerX
  , drawList (numbered . asFun perm2) 7 # centerX
  ]
  where
    numbered n = mkLeaf (text (show n) # fc black <> circle 1) ()

listOnTree = wideTree (mkLeaf (circle 1)) sampleBTree7
  # cCurve 1 0 (1/4 @@@@ turn)
  # cStr   0 3
  # cCurve 3 2 (1/2 @@@@ turn)
  # cStr   2 5
  # cCurve 5 4 (1/4 @@@@ turn)
  # cCurve 4 6 (0 @@@@ turn)
  where
    cCurve :: Int -> Int -> Angle -> Diagram B R2 -> Diagram B R2
    cCurve n1 n2 a =
      connectPerim'
        (superASty & arrowShaft .~ arc (0 @@@@ turn) (1/5 @@@@ turn) # reverseTrail)
        n1 n2
        a (a ^+^ (1/4 @@@@ turn))
    cStr :: Int -> Int -> Diagram B R2 -> Diagram B R2
    cStr   = connectOutside' superASty

superASty   = with & shaftStyle %~ dashingG [0.3,0.3] 0 . lw medium
                   & arrowHead .~ spike
                   & headLength .~ Local 1

treeOnList = drawList (mkLeaf (circle 1)) 7
  # top 1 0
  # top 1 5
  # top 3 2
  # bot 0 3
  # bot 5 4
  # bot 5 6
  where
    top = conn True
    bot = conn False
    conn :: Bool -> Int -> Int -> Diagram B R2 -> Diagram B R2
    conn isTop x y = connectPerim'
        (superASty & arrowShaft .~ (arc (zeroV) (3/8  @@@@ turn) # adjShaft))
        x y pAng pAng
      where
        adjShaft || (x < y) /= isTop = id
                 || otherwise        = reverseTrail
        pAng || isTop     = 1/4 @@@@ turn
             || otherwise = 3/4 @@@@ turn

super = (hcat' (with & sep .~ 5) . map centerXY) [listOnTree, treeOnList]

dia
  = frame 0.5 . centerXY . lwO 0.7
  . vcat' (with & sep .~ 4) . map centerXY
  $
  [ numbering
  , sharedMem
  , super
  ]
  \end{diagram}
  %$
  \caption{Four views on the Cartesian product $\Bin \times \List$}
  \label{fig:Cartesian-product}
\end{figure}
One can think of two distinct shapes, with labels duplicated between
them; this is the most literal interpretation of the definition.  One
can also think of the labels as \emph{pointers} for locations in a
shared memory. Finally, one can think of the shapes themselves as
being superimposed.  This last view highlights the fact that $\times$
is symmetric, but only up to isomorphism, since at root it still
consists of an \emph{ordered} pair of shapes.

In parallel with sum, we can see that \[ (F \times G)(x) = F(x) \times
G(x) \quad \text{and} \quad \unl{(F \times G)}(x) = \unl F(x) \times
\unl G(x), \] where \[ \left( \sum_{n \geq 0} a_n x^n\right) \times
\left( \sum_{n \geq 0} b_n x^n \right) = \sum_{n \geq 0} (a_n b_n) x^n
\] and \[ \left( \sum_{n \geq 0} a_n \frac{x^n}{n!} \right) \times
\left( \sum_{n \geq 0} b_n \frac{x^n}{n!} \right) = \sum_{n \geq 0}
(a_n b_n) \frac{x^n}{n!}
\] denote the elementwise or \term{Hadamard} product of two
generating functions.  This is not a particularly natural operation on
generating functions (although it is easy to compute); in particular
it is not what one usually thinks of as \emph{the} product of
generating functions.  As we will see in \pref{sec:day}, there is a
different combinatorial operation that corresponds to the usual
product of generating functions.

There is also a species, usually called $\Bag$, which is an identity
element for Cartesian product.  Considering that we should have $(\Bag
\times G)\ L = \Bag\ L \times G\ L \equiv G\ L$, the proper definition
of $\Bag$ becomes clear:

\begin{defn}
  The species of \emph{sets}, $\Bag$, is defined as the constant functor
  yielding $\singleton$, that is, $\Bag\ L = \singleton$.
\end{defn}

The ogf for $\Bag$ is given by \[ \unl \Bag(x) = 1 + x + x^2 + \dots =
\frac{1}{1-x}, \] and the egf by \[ \Bag(x) = 1 + x + \frac{x^2}{2!} +
\frac{x^3}{3!} + \dots = e^x. \] The notation $\Bag$ was probably
chosen as an abbreviation of the French \foreign{ensemble} (set), but
it is also a clever pun on the fact that $\Bag(x) = e^x$.

\begin{figure}
  \centering
  \begin{diagram}[width=100]
import SpeciesDiagrams

dia = tag 0 (decoratePath (pentagon 1) (map labT [0..4]))
    # frame 0.5
  \end{diagram}
  \caption{The unique $\Bag\ 5$ shape}
  \label{fig:bag}
\end{figure}

\begin{rem}
  $\Bag$ is called the \term{species of sets} since there is exactly
  one shape on any set of labels, which can be thought of as the set
  of labels itself, with no additional structure.  In
  fact, since all one-element sets are isomorphic, we may define
  $\Bag\ L = \{L\}$ (\pref{fig:bag}).
\end{rem}

\begin{prop}
  $(\times, \Bag)$ is a symmetric monoid on $\Spe$.
\end{prop}

\begin{proof}
  The proof is omitted, since it is almost exactly the same as the
  proof for $(+, \Zero)$; the only difference is the substitution of
  Cartesian product of sets for disjoint union.
\end{proof}

\subsection{Lifting monoids}
\label{sec:lifting-monoids}

% comment from Derek Elkins:
% I'm pretty sure most of the stuff from Lemma 3.6.9 is simply a consequence of (C => -) being a (2-)functor on Cat, and, furthermore, as a right adjoint it preserves limits.  So, for example, Lemma 3.6.9 is: let d \in D be represented as d : 1 -> D.  The d^C : (1^C -> D^C) ~ (1 -> D^C) ~ (C -> D).  A bifunctor F : DxD -> D leads to F^C : ((DxD)^C -> D^C) ~ (D^C x D^C) -> D^C.}

Both these constructions generalize readily. In fact, any monoidal
structure on a category $\Str$ can be lifted to one on $\fc \Lab \Str$
where everything is done elementwise.  The basic idea is exactly
the same as the standard Haskell type class instance
\begin{spec}
instance Monoid a => Monoid (e -> a) where
  mempty         = \ _ -> mempty
  f `mappend` g  = \a -> f a `mappend` g a
\end{spec}
but quite a bit more general.

\begin{prop} \label{prop:lift-monoid-simple} Any (strict) monoid
  $(\otimes, I)$ on $\Str$ lifts to a monoid, denoted $(\otimes^\Lab,
  I^\Lab)$, on the functor category $\fc \Lab \Str$.  In particular, $(F
  \otimes^\Lab G)\ L = F\ L \otimes G\ L$, and $I^\Lab$ is $\Delta_I$,
  the functor which is constantly $I$.  Moreover, this lifting
  preserves products, coproducts, symmetry, and distributivity.
\end{prop}

In fact, non-strict monoids lift as well; a yet more general version
of this proposition, along with a detailed proof, will be given
later. First, however, we consider some examples.

\begin{ex}
  Lifting coproducts in $\Set$ to $\fc \B \Set$ yields the $(+, \Zero)$
  structure on species, and likewise lifting products yields $(\times,
  \Bag)$. According to \pref{prop:lift-monoid-simple}, since
  $(\uplus,\varnothing)$ is a categorical coproduct on $\Set$, $(+,
  \Zero)$ is likewise a categorical coproduct on the category $\fc \B \Set$
  of species, and similarly $(\times, \Bag)$ is a categorical product.
\end{ex}

\begin{ex}
  Take $\Lab = \cat{1}$ (the trivial category with one object and one
  morphism). In this case, functors in $\fc {\cat{1}} \Str$ are just
  objects of $\Str$, and a lifted monoidal operation is isomorphic
  to the unlifted one.
\end{ex}

\begin{ex}
  Take $\Lab = \disc{\cat{2}}$, the discrete category with two
  objects.  Then a functor $F : \disc{\cat{2}} \to \Str$ is just a
  pair of objects in $\Str$.  For example, if $\Str = \Set$, a functor
  $\disc{\cat{2}} \to \Set$ is a pair of sets.  In this case, taking
  the lifted sum $F + G$ of two functors $F,G : \disc{\cat{2}} \to
  \Set$ corresponds to summing the pairs elementwise, that is, $(S_1,
  T_1) + (S_2, T_2) = (S_1 \uplus S_2, T_1 \uplus T_2)$.

  Recall that when $X$ is a discrete category, the functor category
  $\fc X \Set$ is equivalent to the slice category $\Set / X$.  This
  gives another way to think of a functor $\disc{\cat{2}} \to \Set$,
  namely, as a single set of elements $S$ together with a function $S
  \to \disc{\cat{2}}$ which ``tags'' each element with one of two tags
  (``left'' or ``right'', $0$ or $1$, \etc).  From this point of view,
  a lifted sum can be thought of as a tag-preserving disjoint union.
\end{ex}

\begin{ex}
  As an example in a similar vein, consider $\Lab = \N$, the discrete
  category with natural numbers as objects.  Functors $\N \to \Str$
  are countably infinite sequences of objects $[S_0, S_1, S_2,
  \dots]$.  One way to think of this is as a collection of
  $\Str$-objects, one for each natural number \emph{size}.  For
  example, when $\Str = \Set$, a functor $\N \to \Set$ is a sequence
  of sets $[S_0, S_1, S_2, \dots]$, where $S_i$ can be thought of as
  some collection of objects of size $i$. (This ``size'' intuition is
  actually fairly arbitrary at this point---the objects of $\N$ are in
  some sense just an arbitrary countably infinite set of labels, and
  there is no particular reason they should represent ``sizes''.
  However, the ``size'' intuition carries over well to species.)

  Again, $(\fc \N \Set) \iso \Set/\N$, so functors $\N \to \Set$ can
  also be thought of as a single set $S$ along with a function $S \to
  \N$ which gives the size of each element.

  Lifting a monoidal operation to countable sequences of objects
  performs a ``zip'', applying the monoidal operation between matching
  positions in the two lists: \[ [S_1, S_2, S_3, \dots] \oplus [T_1,
  T_2, T_3, \dots] = [S_1 \oplus T_1, S_2 \oplus T_2, S_3 \oplus T_3,
  \dots] \]
\end{ex}

\begin{ex}
  All the previous examples have used a discrete category in place of
  $\Lab$; it is instructive to see an example with nontrivial
  morphisms involved. As the simplest nontrivial example, consider
  $\Lab = \cat{2}$, the category with two objects $0$ and $1$ and a
  single non-identity morphism $\mor 0 1$.  A functor $\cat{2} \to
  \Str$ is not just a pair of objects (as with $\Lab = \disc{\cat 2}$)
  but a pair of objects with a morphism between them: \[ S_0
  \stackrel{f}{\longrightarrow} S_1. \] Combining two such functors
  with a lifted monoidal operation combines not just the objects but
  also the morphisms: \[ (S_0 \stackrel{f}{\longrightarrow} S_1)
  \oplus (T_0 \stackrel{g}{\longrightarrow} T_1) = (S_0 \oplus T_0)
  \stackrel{f \oplus g}{\longrightarrow} (S_1 \oplus T_1) \] This is
  possible since the monoidal operation $\oplus$ is, by definition,
  required to be a bifunctor.
\end{ex}

\begin{ex}
  In $\ST$, the coproduct of two types $A$ and $B$ is given by their
  sum, $A + B$, with the void type $\TyZero$ serving as the identity.
  We may thus lift this coproduct structure to the functor category
  $\fc \BT \ST$---or indeed to any $\fc \Lab \ST$, since no
  requirements are imposed on the domain category.
\end{ex}

\begin{ex}
  Similarly, categorical products in $\ST$ are given by product
  types $A \times B$, with the unit type $\TyOne$ as the identity.
  This then lifts to products on $\fc \BT \ST$ (or, again, any
  $\fc \Lab \ST$) which serve as an analogue of Cartesian product of
  species.
\end{ex}

\later{give some examples with other categories. $1/\Set$,
  \ie\ pointed sets with smash product? $\cat{Vect}$?}

A more detailed proof of the fact that any monoid on a category $\Str$
lifts to a corresponding monoid on $\fc \Lab \Str$ can be found in
\pref{chap:lifting-monoids}.

\subsection{Internal Hom for Cartesian product}
\label{sec:internal-Hom-cprod}

Recall that a \term{Cartesian closed} category is one which is closed
with respect to Cartesian product, that is, there exists some
bifunctor $\expn B C$ such that \[ \all{ABC}{(\Hom {A \times B} C)
  \iso (\Hom A {(\expn B C)})}. \]  Such categories allow morphisms to be
``internalized'', that is, represented as objects.

\begin{prop}
  $\Spe$ is Cartesian closed.
\end{prop}

If $\Lab$ is locally small and $\Str$ is complete and Cartesian
closed, then $\fc \Lab \Str$ is also complete and Cartesian closed
\citep{cart-closed-functor-cat}.  In particular, the exponential of
$F,G : \Lab \to \Str$ is given by \[ G^F\ L = \eend{K \in \Lab}
\prod_{\Lab(L,K)} G(K)^{F(K)}. \] For example, $\B$, $\P$, $\BT$, and
$\PT$ are all locally small, and $\Set$ and $\ST$ are complete and
Cartesian closed, so $\fc \B \Set$, $\fc \P \Set$, $\fc \BT \ST$, and
$\fc \PT \ST$ are all complete and Cartesian closed as well.

Let's unpack this result a bit in the specific case of $\fc \PT \ST$.
By a dual argument to the one given in \pref{sec:coends-hott}, ends in
$\ST$ over the groupoid $\PT$ are given by $\Pi$-types, \ie universal
quantification; hence, we have
\begin{align*}
(H^G)\ n &= \eend{m \in \PT} \prod_{\PT(m,n)} (H\ n)^{G\ n} \\
       &= (m : \N) \to (\Fin m \equiv \Fin n) \to G\ n \to H\ n \\
       &\equiv (\Fin n \equiv \Fin n) \to G\ n \to H\ n
\end{align*}
where the final isomorphism follows since $(\Fin m \equiv \Fin n)$ is
only inhabited when $m = n$.

Being Cartesian closed means there is an adjunction $- \times G \adj
-^G$ between products and exponentials, which yields a natural
isomorphism \[ (\Hom[\ST^\PT]{F \times G}{H}) \equiv (\Hom[
\ST^\PT]{F}{H^G}). \] Expanding morphisms of the functor category $\fc
\PT \ST$ as natural transformations, and expanding the definition of
$H^G$ derived above, this yields \[ \left( (n : \N) \to (F \times G)\
  n \to H\ n \right) \equiv \left( (n : \N) \to F\ n \to (\Fin n
  \equiv \Fin n) \to G\ n \to H\ n \right). \] Intuitively, this says
that a size-polymorphic function taking a Cartesian product shape $F
\times G$ and yielding an $H$-shape of the same size is isomorphic to
a size-polymorphic function taking a triple of an $F$-shape, a
$G$-shape, \emph{and a permutation on $\Fin n$}, and yielding an
$H$-shape.  The point is that an $(F \times G)$-shape consists not
just of separate $F$- and $G$-shapes, but those shapes get to
``interact'': in particular we need a permutation to tell us how the
labels on the separate $F$- and $G$-shapes line up.  An $(F \times
G)$-shape encodes this information implicitly, by the fact that the
two shapes share the exact same set of labels.

Practically speaking, this result tells us how to express an
eliminator for $(F \times G)$-shapes.  That is, to be able to
eliminate $(F \times G)$-shapes, it suffices to be able to eliminate
$F$- and $G$-shapes individually, with an extra permutation supplied
as an argument. Eliminators for species shapes are treated more
generally and systematically in \pref{sec:elim-species}.

On the surface, the fact that $\Spe$ is Cartesian closed only allows
us to internalize \emph{species morphisms} as species, but not to
interpret functions between data types.  $\Spe$ being Cartesian closed
does mean that the simply typed lambda calculus can be interpreted
internally to $\Spe$; but it is not yet clear to me what this would
mean on an intuitive level.

\section{Partitional product and Day convolution}
\label{sec:day}

There is another notion of product for species, the \term{partitional}
or \term{Cauchy} product.  It it is the partitional product, rather
than Cartesian product, which corresponds to the product of generating
functions and which gives rise to the usual notion of product on
algebraic data types.  For these reasons, partitional product is often
(both in this thesis and in species literature generally) simply
referred to as ``product'', without any modifier.

There is also another lesser-known product, \term{arithmetic
  product} \citep{maia2008arithmetic}, which can be thought of as a
symmetric form of composition.  These two \mbox{products} arise in an
analogous way, via a categorical construction known as \emph{Day
  convolution}.

In this section, we explore each operation in turn, and then give a
general account of their common abstraction.

\subsection{Partitional/Cauchy product}
\label{sec:partitional-product}


The partitional product $F \sprod G$ of two species $F$ and $G$
consists of paired $F$- and $G$-shapes, as with the Cartesian product,
but with the labels \emph{partitioned} between the two shapes instead
of replicated (\pref{fig:product}).  The divided box with rounded
corners used in \pref{fig:product} will often be used to schematically
indicate a partitional product.

  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import           Data.List.Split
import           Diagrams.TwoD.Layout.Tree
import           Diagrams.TwoD.Path.Metafont

import           SpeciesDiagrams
import           Structures (pair)

connectAll l1 l2 n =
  withNames (map (l1 .>) [0 :: Int .. n-1]) $ \l1s ->
  withNames (map (l2 .>) [0 :: Int .. n-1]) $ \l2s ->
  applyAll (zipWith conn l1s l2s)

conn l1 l2 = beneath (lc grey . metafont $ location l1 .- leaving unit_Y <> arriving unit_Y -. endpt (location l2))
-- $

sharedMem = vcat' (with & sep .~ 5)
  [ pair
      (wideTree (mkLeaf (circle 1) . ("l" .>) . (part1!!)) sampleBTree5 # centerY)
      (drawList (mkLeaf (circle 1) . ("l" .>) . (part2!!)) 3 # centerY)
    # centerX
  , drawList (mkLeaf (square 2) . ("s" .>)) 8 # centerXY
  ]
  # connectAll "l" "s" 8
  # centerXY # pad 1.1

perm1 = id
perm2 = id

part1, part2 :: [Int]
part1 = [3,0,1,2,6]
part2 = [5,4,7]

numbering =
  pair
    (wideTree (numbered . (part1!!)) sampleBTree5 # centerXY)
    (drawList (numbered . (part2!!)) 3 # centerXY)
  where
    numbered n = mkLeaf (text (show n) # fc black <> circle 1) ()

dia
  = frame 0.5 . lwO 0.7 . centerXY
  . vcat' (with & sep .~ 4) . map centerXY
  $
  [ numbering
  , sharedMem
  ]
    \end{diagram}
    %$

%     \begin{diagram}[width=250]
% import SpeciesDiagrams

% theDia
%   = hcat' (with & sep .~ 1)
%     [ struct 5 "F•G"
%     , text' 1 "="
%     , vcat' (with & sep .~ 0.2)
%       [ struct 2 "F"
%       , struct 3 "G"
%       ]
%       # centerY
%     ]

% dia = theDia # centerXY # pad 1.1
%     \end{diagram}
    \caption{Two views on the partitional species product $\Bin
      \cdot \List$}
    \label{fig:product}
  \end{figure}

\begin{defn}
  The \term{partitional} or \term{Cauchy product} of two species $F$
  and $G$ is the functor defined on objects by \[ (F \sprod G)\ L =
  \biguplus_{L_F,L_G \partition L} F\ L_F \times G\ L_G \] where
  $\biguplus$ denotes an indexed coproduct (\ie disjoint union) of
  sets, and $L_F,L_G
  \partition L$ indicates that $L_F$ and $L_G$ constitute a partition
  of $L$, (\ie $L_F \union L_G = L$ and $L_F \intersect L_G =
  \varnothing$); note that $L_F$ and $L_G$ may be empty.  In words, an
  $(F \cdot G)$-shape with labels taken from $L$ consists of some
  partition of $L$ into two disjoint subsets, with an $F$-shape on one
  subset and a $G$-shape on the other.

  On morphisms, $(F \cdot G)\ \sigma$ is the function \[
  (L_F,L_G, x, y) \mapsto (\sigma\ L_F, \sigma\ L_G, F\ (\sigma
  \vert_{L_F})\ x, G\ (\sigma \vert_{L_G})\ y), \] where $L_F,L_G
  \partition L$ and $x \in F\ L_F$ and $y \in G\ L_G$.  That is,
  $\sigma$ acts independently on the two subsets of $L$.
\end{defn}

To compute the ogf of a product species $F \cdot G$, consider the
product of ogfs \[ \unl F(x) \unl G(x) = \left( \sum_{n \geq 0} f_n x^n \right) \left(
  \sum_{n \geq 0} g_n x^n \right) = \sum_{n \geq 0} \left( \sum_{0
    \leq k \leq n} f_k g_{n-k} \right) x^n. \] Note that the inner sum
$\sum_{0 \leq k \leq n} f_k g_{n-k}$ is indeed the number of $(F \cdot
G)$-forms of size $n$: such forms necessarily consist of an $F$-form
of size $k$ paired with a $G$-form of size $n-k$. Hence \[ \unl{(F
  \cdot G)}(x) = \unl F(x) \unl G(x). \]

The computation of the egf of a product species is similar.
\begin{align*}
  F(x)G(x) &= \left(\sum_{n \geq 0} f_n \frac{x^n}{n!} \right) \left(
    \sum_{n \geq 0} g_n \frac{x^n}{n!} \right) \\
  &= \sum_{n \geq 0} \left( \sum_{0 \leq k \leq n} \frac{f_k}{k!}
    \frac{g_{n-k}}{(n-k)!} \right) x^n \\
  &= \sum_{n \geq 0} \left( \sum_{0 \leq k \leq n} \binom{n}{k} f_k
    g_{n-k} \right) \frac{x^n}{n!}.
\end{align*}
Again, we verify that the inner sum $\sum_{0 \leq k \leq n}
\binom{n}{k} f_k g_{n-k}$ is the number of labelled $(F \cdot
G)$-shapes of size $n$: for each $0 \leq k \leq n$, there are $\binom
n k$ ways to partition the $n$ labels into two subsets of size $k$ and
$n-k$, and then there are $f_k$ ways to make an $F$-shape on the first
subset, and $g_{n-k}$ ways to make a $G$-shape on the second.  We
therefore have \[ (F \cdot G)(x) = F(x) G(x) \] as well.

The identity for partitional product should evidently be some species
$\One$ such that \[ (\One \cdot G)\ L = \left(\biguplus_{L_F,L_G
    \partition L} \One\ L_F \times G\ L_G \right) \equiv G\ L. \] The only
way for this isomorphism to hold naturally in $L$ is if $\One\
\varnothing = \singleton$ (yielding a summand of $G\ L$ when
$\varnothing,L \partition L$) and $\One\ L_F = \varnothing$ for all other $L_F$
(cancelling all the other summands).

\begin{defn}
  The \term{unit species}, $\One$, is defined by
  \[ \One\ L =
  \begin{cases}
    \singleton & L = \varnothing \\
    \varnothing & \text{otherwise}.
  \end{cases}
  \]
\end{defn}

\begin{rem}
  Recall that one should not think of $\One$ as doing case analysis.
  Rather, a more intuitive way to think of it is ``there is a single
  $\One$-shape, and it has no labels''; that is, the unit species
  denotes a sort of ``trivial'' or ``leaf'' structure containing no
  labels.  Intuitively, it corresponds to a Haskell type like
  {\setlength{\belowdisplayskip}{0pt}
  \begin{spec}
    data Unit a = Unit
  \end{spec}
  }
\end{rem}

The generating functions for $\One$ are given by \[ \One(x) = \unl
\One(x) = 1. \]

\begin{ex}
  The following example is due to \citet{joyal}. Recall that
  $\Perm$ denotes the species of permutations.  Consider the species
  $\Der$ of \term{derangements}, that is, permutations which have no
  fixed points.  It is not possible, in general, to directly express
  species using a ``filter'' operation, as in, ``all $F$-shapes
  satisfying predicate $P$''.  However, it is possible to get a handle
  on $\Der$ in a more constructive manner by noting that every
  permutation can be canonically decomposed as a set of fixed points
  paired with a derangement on the rest of the elements
  (\pref{fig:perm-der}). \later{Improve this diagram.}
  \begin{figure}
    \centering
    \begin{diagram}[width=300]
import           SpeciesDiagrams
import           Structures       (pair)

dot = circle 0.2 # fc black

selfLoop d =
    strutY (height d / 2)
    ===
    d # named () # connectPerim' opts () () (3/8 @@@@ turn) (1/8 @@@@ turn)
  where
    opts = with & arrowShaft .~ arc (7/8 @@@@ turn) (5/8 @@@@ turn) # reverseTrail

fps = hcat' (with & sep .~ 0.5) (replicate 3 (dot # selfLoop))

cycs :: Diagram B R2
cycs =
  hcat' (with & sep .~ 0.5)
  [ cyc' (replicate 3 dot) 0.8
  , cyc' (replicate 2 dot) 0.8
  ]

dia = pair fps cycs # frame 0.5
    \end{diagram}
    \caption{Permutation = fixpoints $\cdot$ derangement}
    \label{fig:perm-der}
  \end{figure}
  That is, algebraically, \begin{equation} \label{eq:perm-eq} \Perm =
    \Bag \cdot \Der. \end{equation} This does not directly give us an
  expression for $\Der$, since there is no notion of multiplicative
  inverse for species\footnote{Multiplicative inverses can in fact be
    defined for suitable \emph{virtual} species~\citep[Chapter
    3]{bll}.  However, virtual species are beyond the scope of this
    dissertation.}.  However, this is still a useful characterization
  of derangements.  For example, since the mapping from species to
  egfs is a homomorphism with respect to product, \eqref{eq:perm-eq}
  becomes \[ \frac{1}{1-x} = e^x \cdot \Der(x). \] We can solve to
  obtain the egf $\Der(x) = e^{-x}/(1-x)$, even though we cannot make
  direct combinatorial sense out of $\Der = \Perm / \Bag$.
\end{ex}

\later{Another example?}

\begin{prop}
  $(\Spe, \cdot, \One)$ is symmetric monoidal.
\end{prop}

\begin{proof}
  We constructed $\One$ so as to be an identity for partitional
  product.  Associativity and symmetry of partitional product are not
  hard to prove and are left as an exercise for the reader.
\end{proof}

In fact, $(\Spe, \cdot, \One)$ is closed as well, but a discussion of
the internal Hom functor corresponding to partitional product must be
postponed to \pref{sec:internal-Hom-pprod-aprod}, after discussing
species differentiation.

\subsection{Arithmetic/rectangular product}
\label{sec:arithmetic-product}

\newcommand{\aprod}{\boxtimes}

There is another, more recently discovered monoidal structure on
species known as \emph{arithmetic product} \citep{maia2008arithmetic}.
The arithmetic product of the species $F$ and $G$, written $F \aprod
G$, can intuitively be thought of as an ``$F$-assembly of cloned
$G$-shapes'', that is, an $F$-shape containing multiple copies of a
\emph{single} $G$-shape.  Unlike the usual notion of composition
(\pref{sec:composition}), where the $F$-shape is allowed to contain
many different $G$-shapes, this notion is symmetric: an $F$-assembly
of cloned $G$-shapes is isomorphic to a $G$-assembly of cloned
$F$-shapes.  Another intuitive way to think of the arithmetic product,
which points out the symmetry more clearly, is to think of a
rectangular grid of labels, together with an $F$-shape labelled by
the rows of the grid, and a $G$-shape labelled by the
columns. \pref{fig:arithmetic-product} illustrates these intuitions
with the arithmetic product $\Bin \aprod \List$.

\begin{figure}
  \centering
  \begin{diagram}[width=250]
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

grays  = map (\k -> blend k black white) [0, 0.2, 0.8, 1, 0.5]
shapes = [circle 0.2, triangle 0.4, square 0.4]

grid = vcat' (with & sep .~ 0.5)
  [ tree3 (\n -> mkLeaf (circle 0.4 # fc (grays !! n)) n) # translateX 3.4
  , hcat' (with & sep .~ 0.5)
    [ list2 (\n -> (mkLeaf ((shapes !! n) # rotateBy (1/4) <> circle 0.4) n)) # rotateBy (3/4)
    , theGrid
    ]
  ]
  where
    theGrid :: Diagram B R2
    theGrid = vcat . map hcat $
      [ [ (shapes !! i) # fc (grays !! j) <> square 1
        || j <- [1,0,3,2,4]
        ]
      || i <- [0..2]
      ]

assembly1 =
  tree3 (mkLeaf $ enrect (list2 (mkLeaf (circle 0.4)) # centerX # scale 0.5))

assembly2 = hcat' (with & sep .~ 0.4)
  (map (fc white . enrect . (mkLeaf (tree3 (mkLeaf (circle 0.4)) # centerXY # scale 0.5))) [0 .. 2 :: Int])
  <>
  hrule 7 # alignL

enrect d = d <> roundedRect (width d + 0.2) (height d + 0.2) 0.2

tree3 nd
  = maybe mempty (renderTree nd (~~))
  . uniqueXLayout 1 1
  $ sampleBTree5

list2 nd = hcat' (with & sep .~ 1 & catMethod .~ Distrib)
  (map nd [0 :: Int .. 2])
  <>
  hrule 2 # alignL
  where
    aSty = with & arrowHead .~ noHead

dia = frame 0.2 . lwO 0.7 . centerXY . vcat' (with & sep .~ 2) . map centerXY $
  [ assembly1 # scale 1.3
  , assembly2
  , grid
  ]
  \end{diagram}
  \caption{Three views on the arithmetic product $\Bin \aprod \List$}
  \label{fig:arithmetic-product}
\end{figure}

A more formal definition requires the notion of a \term{rectangle} on
a set~\citep{maia2008arithmetic, baddeley2004transitive}, which plays
a role similar to that of set partition in the definition of
partitional product. (So arithmetic product can also be called
\emph{rectangular product}.)  In particular, whereas a binary
partition of a set $L$ is a decomposition of $L$ into a sum, a
rectangle on $L$ can be thought of as a decomposition into a product.
The basic idea is to partition $L$ in two different ways, and require
the partitions to act like the ``rows'' and ``columns'' of a
rectangular matrix, which have the defining characteristic that every
pair of a row and a column have a single point of intersection.

\begin{defn}[\citet{maia2008arithmetic}]
  \label{defn:rectangle}
  A \term{rectangle} on a set $L$ is a pair $(\pi, \tau)$ of families
  of subsets of $L$, such that
  \begin{itemize}
  \item $\pi \partition L$ and $\tau \partition L$, and
  \item $||X \intersect Y|| = 1$, for all $X \in \pi$, $Y \in \tau$.
  \end{itemize}
  Here, $\pi \partition L$ denotes that $\pi$ is a partition of $L$
  into any number of nonempty parts, that is, the elements of $\pi$
  are nonempty, pairwise disjoint, and have $L$ as their union.  We
  write $\pi,\tau \rectangle L$ to denote that $(\pi,\tau)$ constitute
  a rectangle on $L$, and call $\pi$ and $\tau$ the \term{sides} of
  the rectangle.
\end{defn}

We can now formally define arithmetic product as follows:

\begin{defn}
  The \term{arithmetic product} $F \aprod G$ of two species $F$ and
  $G$ is the species defined on objects by \[ (F \aprod G)\ L =
  \biguplus_{L_F, L_G \rectangle L} F\ L_F \times G\ L_G. \]

  $(F \aprod G)$ lifts bijections $\sigma : L \bij L'$ to functions
  $(F \aprod G)\ L \to (F \aprod G)\ L'$ as follows: \[ (F \aprod G)\
  \sigma\ (L_F, L_G, f, g) = (\powerset(\sigma)\ L_F,
  \powerset(\sigma)\ L_G, F\ \powerset(\sigma)\ f, G\
  \powerset(\sigma)\ g), \] where $\powerset(\sigma) : \powerset(L)
  \bij \powerset(L')$ denotes the functorial lifting of $\sigma$ to a
  bijection between subsets of $L$ and $L'$.
\end{defn}

\begin{rem}
  The similarity of this definition to the definition of partitional
  product should be apparent: the only real difference is that
  rectangles ($L_F,L_G \rectangle L$) have been substituted for
  partitions ($L_F,L_G \partition L$).
\end{rem}

\begin{ex}
  $\Sp{Mat} = \List \aprod \List$ is the species of (two-dimensional)
  \term{matrices}. $\Sp{Mat}$-shapes consist simply of labels arranged
  in a rectangular grid (\pref{fig:mat-shape}).
\end{ex}
\begin{figure}
  \centering
  \begin{diagram}[width=150]
import           SpeciesDiagrams

mkGrid = vcat . map hcat . (map . map) mkElt
  where
    mkElt i = square 1 <> labT i

dia = mkGrid [[0,2,5],[3,1,4]]
  # lwO 0.7
  # frame 0.5
  \end{diagram}
  \caption{A $\Sp{Mat}$-shape of size $6$}
  \label{fig:mat-shape}
\end{figure}

\begin{ex}
  $\Sp{Rect} = \Bag \aprod \Bag$ is the species of
  \term{rectangles}. One way to think of rectangles is as equivalence
  classes of matrices up to reordering of the rows and columns.  Each
  label has no fixed ``position''; the only invariants on any given
  label are the sets of other labels which are in the same row or
  column.  \pref{fig:rect-shape} shows an illustration; each rounded
  outline represents a \emph{set} of labels. One can also
  take the species of rectangles as primitive and define arithmetic
  product in terms of it.
\end{ex}

\begin{figure}
  \centering
  \begin{diagram}[width=200]
import           Data.List                      (transpose)
import           Diagrams.TwoD.Offset
import           SpeciesDiagrams

mkRect :: [[Int]] -> Diagram B R2
mkRect g = (vcat . map hcat . (map . map) mkElt $ g) # applyAll (map neighborSet g) # applyAll (map neighborSet (transpose g))
  where
    mkElt i = square 1.5 # lw none <> labT i # named i
    neighborSet xs = withNames [head xs, last xs] $ \[s,e] ->
      let v = (location e .-. location s) # normalized # scale 0.6
      in  beneath (stroke $ expandPath' (with & expandCap .~ LineCapRound) 0.4 ((location s .-^ v) ~~ (location e .+^ v))) -- $

dia = mkRect [[0,2,5],[3,1,4]]
  # lwO 0.7
  # frame 0.5
  \end{diagram}
  \caption{A $\Sp{Rect}$-shape of size $6$}
  \label{fig:rect-shape}
\end{figure}

\begin{ex}
  Just as topological cylinders and tori may be obtained by gluing the
  edges of a square, species corresponding to cylinders or tori may be
  obtained by starting with the species of 2D matrices and ``gluing''
  along one or both edges by turning lists $\List$ into cycles $\Cyc$.
  In particular, $\Sp{Cyl} = \List \aprod \Cyc$ is the species of
  (oriented) \term{cylinders}, and $\Sp{Tor} = \Cyc \aprod \Cyc$ is
  the species of (oriented) \term{tori}.

  Although species corresponding to Klein bottles and real projective
  planes (which arise from gluing the edges of a square with one or
  both pairs of edges given a half-twist before gluing, respectively)
  certainly exist, it does not seem they can be constructed using
  $\aprod$, since in those cases the actions of the symmetric group
  along the two axes are not independent.
\end{ex}

\later{More examples?}

The ogf for $F \aprod G$ is given by \[ \unl F(x) \aprod \unl G(x) = \left(
  \sum_{n \geq 0} f_n x^n \right) \aprod \left( \sum_{n
    \geq 0} g_n x^n \right) = \sum_{n \geq
  0} \left( \sum_{d \mid n} f_d g_{n/d} \right) x^n, \] since an $(F
\aprod G)$-form of size $n$ consists of a pair of an $F$-form and a
$G$-form, whose sizes have a product of $n$.

Likewise, the egf is \[ \sum_{n \geq 0} \left( \sum_{d \mid n}
  \numrect{n}{d} f_d g_{n/d} \right) \frac{x^n}{n!}, \] where \[
\numrect{n}{d} = \frac{n!}{d!(n/d)!} \] denotes the number of $d
\times (n/d)$ rectangles on a set of size $n$.

An identity element for arithmetic product should be some species $\X$
such that \[ (\X \aprod G)\ L = \left(\biguplus_{L_\X, L_G \rectangle L} \X\
L_\X \times G\ L_G\right) \iso G\ L. \] Thus we want $\X\ L_\X = \singleton$
when $L_G = L$, and $\X\ L_\X = \varnothing$ otherwise.
Consider $L_\X, L \rectangle L$.  Of course, $L$ does not have the
right type to be one side of a rectangle on itself, but it is
isomorphic to the set of all singleton subsets of itself, which does.
The definition of a rectangle now requires every element of $L_\X$ to
have a nontrivial intersection with every singleton subset of $L$
(such intersections will automatically have size $1$).  Therefore
$L_\X$ has only one element, namely, $L$ itself, and is isomorphic to
$\singleton$.  Intuitively, $\singleton, L \rectangle L$ corresponds
to the fact that we can always make a $1 \times n$ rectangle on any
set of size $n$, that is, any number $n$ can be ``factored'' as $1
\times n$.

This leads to the following definition:
\begin{defn}
  The \term{singleton species}, $\X$, is defined by \[ \X\ L =
  \begin{cases}
    \singleton & ||L|| = 1 \\
    \varnothing & \text{otherwise}.
  \end{cases}
  \]
\end{defn}

\begin{rem}
  Like the unit species $\One$, the singleton species $\X$ denotes a
  sort of ``leaf'' structure; however, instead of being a trivial leaf
  structure with no labels, it contains a single label, that is, it
  marks the spot where a single piece of data can go.  Intuitively, it corresponds
  to the Haskell data type
  {\setlength{\belowdisplayskip}{0pt}
  \begin{spec}
    data X a = X a
  \end{spec}
  }
\end{rem}

One can see that the egf and ogf for $\X$ are \[ \X(x) = \unl \X(x) =
x. \]

Species corresponding to a wide variety of standard data structures
can be defined using $\X$.

\begin{ex}
  The species of \term{ordered pairs} is given by $\X \cdot \X$.
  Since there is only an $\X$-shape on a single label, and product
  partitions the labels, there are only $(\X \cdot \X)$-shapes on
  label sets of cardinality $2$, and there are two such shapes, one
  for each ordering of the two labels (\pref{fig:XdX-shapes}).
  \begin{figure}
    \centering
    \begin{diagram}[width=200]
import           Data.List                      (permutations)
import           SpeciesDiagrams

pair x y = hcat
  [ roundedRect' 1 1 (with & radiusTL .~ 0.2 & radiusBL .~ 0.2) <> x
  , roundedRect' 1 1 (with & radiusTR .~ 0.2 & radiusBR .~ 0.2) <> y
  ]

pairs = hcat' (with & sep .~ 1) $ map mkPair (permutations [0,1])  -- $
  where
    mkPair [x,y] = pair (labT x) (labT y)

dia = pairs
  # lwO 0.7
  # frame 0.5
    \end{diagram}
    \caption{$(\X \cdot \X)$-shapes}
    \label{fig:XdX-shapes}
  \end{figure}

  More generally, $\X^n = \underbrace{\X \cdot \dots \cdot \X}_n$ is the
  species of \term{ordered $n$-tuples}; there are exactly $n!$ many
  $(\X^n)$-structures on $n$ labels and none on label sets of any
  other size.
\end{ex}

\begin{ex}
  Recall that $\List$ denotes the species of lists, \ie linear
  orderings.  Besides the interpretation of recursion, to be explored
  in \pref{sec:recursive}, we have now seen all the necessary pieces
  to understand the algebraic definition of $\List$: \[ \List = \One +
  \X \cdot \List. \] That is, a list structure is either the trivial
  structure on zero labels, or a single label paired with a list
  structure on the remainder of the labels.  We also have $\List =
  \One + \X + \X^2 + \X^3 + \dots$.
\end{ex}

\begin{ex}
  Similarly, recall that the species $\Bin$ of \term{binary trees} is
  given by \[ \Bin = \One + \Bin \cdot \X \cdot \Bin. \]
\end{ex}

\begin{ex}
  The species $\X \cdot \Bag$ is variously known as the species of
  \term{pointed sets} (which may be denoted $\pointed{\Bag}$) or the
  species of \term{elements} (denoted $\elts$).  $(\X \cdot
  \Bag)$-structures consist of a single distinguished label paired
  with an unstructured collection of any number of remaining
  labels. There are thus $n$ such structures on each label set of
  cardinality $n$, one for each label.

  The two different names result from the fact that we may ``care
  about'' the labels in an $\Bag$-structure or not---that is, when
  considering data structures built on top of species, $\Bag$ may
  correspond either to a bag data structure, or instead to a ``sink''
  where we throw labels to which we do not wish to associate any
  data. This makes no difference from a purely combinatorial point of
  view, but makes a difference when considering labelled structures
  (\pref{chap:labelled}).
\end{ex}

% \begin{ex}
%   Likewise, $\Bag \cdot \Bag$ is the species of \term{binary
%     partitions}, whereas $\Bag \cdot \Rubbish$ is the species of
%   \term{subsets}; they are combinatorially equivalent but differ in
%   their realization as data structures.
% \end{ex}

\subsection{Day convolution}
\label{sec:day-convolution}

Just as sum and Cartesian product were seen to arise from the same
construction applied to different monoids, both partitional and
arithmetic product arise from \emph{Day convolution}, applied to
different monoidal structures on $\B$.

It is worth first briefly mentioning the definition of an
\term{enriched category}, which is needed here and also in
\pref{sec:composition}.  Enriched categories are a generalization of
categories where the \emph{set} of morphisms between two objects is
replaced by an \emph{object} of some other category.
\begin{defn}
  Given some monoidal category $(\D, \otimes, I)$, a \term{category
    enriched over $\D$} consists of
  \begin{itemize}
  \item a collection of objects $O$;
  \item for every pair of objects $A,B \in O$, a corresponding object
    of $\D$, which we notate $\hom A B$;
  \item for each object $A \in O$, a morphism $I \to (\hom A A)$ in
    $\D$, which ``picks out'' the identity morphism for each object;
  \item for every three objects $A,B,C \in O$, a morphism
    $\comp_{A,B,C} : (\hom B C) \otimes (\hom A B) \to (\hom A C)$
    representing composition.
  \end{itemize}
  Of course, identity and composition have to satisfy the usual laws,
  expressed via commutative diagrams.  Note we are technically
  overloading the $\hom{}{}$ notation, but it is natural to extend it
  from denoting hom sets to denoting hom objects in general.
\end{defn}
Enriched categories and categories are notionally distinct, but we
often conflate them.  In particular, any category can be seen as an
enriched category over $\Set$, and we also often say that a category
$\C$ \term{is enriched over} $\D$ if there exists some functor $\hom -
- : \C^\op \times \C \to \D$ satisfying the above criteria.

We can now give the definition of Day convolution.  The essential
idea, first described by \citet{day1970closed}, is to
construct a monoidal structure on a functor category $[\Lab^\op,
\Str]$ based primarily on a monoidal structure on the \emph{domain}
category $\Lab$.  In particular, Day convolution requires
\begin{itemize}
\item a monoidal structure $\oplus$ on the domain $\Lab$;
\item that $\Lab$ be enriched over $\Str$, so hom sets of $\Lab$ can
  be seen as objects in $\Str$;
\item a symmetric monoidal structure $\otimes$ on the codomain $\Str$
  (satisfying an additional technical requirement, to be explained
  below); and
\item that $\Str$ be cocomplete, and in particular
  have coends over $\Lab$.
\end{itemize}

\later{Note that any small category can be seen as $V$-enriched, for
  symmetric monoidal (closed?) $V$, by composing $hom$ with functor
  $\Set \to V$ that sends $U$ to $U$-indexed product of $I$.  Does
  this assume AC or anything?  Actually I am no longer sure I even
  understand this statement.  Need to look it up in ``geometry of
  tensor calculus'' or ``introduction to enriched categories'',
  perhaps.  But if I can understand it again it would probably be a
  good thing to include.}

In addition, $\otimes$ must preserve colimits in each of its
arguments.  That is, $- \otimes B$ and $A \otimes -$ must both
preserve colimits for any $A$ and $B$.  It is sufficient (though not
necessary) that $\otimes$ is a left adjoint.  For example, the product
bifunctor in $\Set$ is left adjoint (via currying), and thus preserves
colimits---the distributive law $(X \times (Y + Z) \iso X \times Y + X
\times Z$ is a well-known example.  On the other hand, the coproduct
bifunctor in $\Set$ does not preserve colimits; it is not the case,
for example, that $X + (Y + Z) \iso (X + Y) + (X + Z)$.  The important
point to note is that Day convolution can be instantiated using
\emph{any} monoidal structure on the source category $\Lab$, but
requires a very particular sort of monoidal structure on the target
category $\Str$.

\begin{defn}
  Given the above conditions, the Day convolution product of $F, G :
  \fc {\Lab^\op} \Str$ is given by the coend \[ (F \oast G)\ L = \coend{L_F, L_G}
  F\ L_F \otimes G\ L_G \otimes (\Hom[\Lab]{L}{L_F \oplus L_G}). \]
\end{defn}

\begin{rem}
  Since groupoids are self-dual, we may ignore the $-^\op$ in the
  common case that $\Lab$ is a groupoid.  Note that $F\ L_F$ and $G\
  L_G$ are objects in $\Str$, and $(\Hom[\Lab]{L}{L_F \oplus L_G})$ is
  a hom set in $\Lab$, viewed as an object in $\Str$ as well.
\end{rem}

This operation is associative, and has as a unit $j(I)$, where $I$ is
the unit for $\oplus$ and $j : \Lab \to (\fc {\Lab^{\text{op}}} \Str)$
is the co-Yoneda embedding, that is, $j(L) = (\hom[\Lab] - L)$. See
\citet{kelly2005operads} for proof.

\begin{ex}
  Let's begin by looking at the traditional setting of $\Lab = \B$ and
  $\Str = \Set$.  As noted in~\pref{sec:groupoids}, $\B$ has a
  monoidal structure given by disjoint union of finite sets. $\B$ is
  indeed enriched over $\Set$, which is also cocomplete and has an
  appropriate symmetric monoidal structure given by Cartesian product.

  Specializing the definition to this case, we obtain
  \begin{align*}
    (F \cdot G)\ L &= \coend{L_F, L_G} F\ L_F \times G\ L_G \times
    (L \bij L_F \uplus L_G).
  \end{align*}
  We can simplify this further by characterizing the coend more
  explicitly.  Let \[ R \defeq \biguplus_{L_F, L_G} F\ L_F \times G\ L_G
  \times (L \bij L_F \uplus L_G). \] Elements of $R$ look like
  quintuples $(L_F, L_G, f, g, i)$, where $f \in F\ L_F$, $g \in G\
  L_G$, and $i : L \bij L_F \uplus L_G$ witnesses a partition of $L$
  into two subsets.  Then, as we have seen, the coend can be expressed
  as a quotient $\quotient{R}{\eqrel}$, where every pair of bijections
  $(\sigma_F : L_F \bij L_F', \sigma_G : L_G \bij L_G')$ induces an
  equivalence of the form \[ (L_F, L_G, f, g, i) \eqrel (L_F',\; L_G',\;
  F\ \sigma_F\ f,\; G\ \sigma_G\ g,\; i \then (\sigma_F \uplus
  \sigma_G)). \] That is, $f \in F\ L_F$ is sent to $F\ \sigma_F\ f$
  (the relabelling of $f$ by $\sigma_F$); $g \in G\ L_G$ is sent to
  $G\ \sigma_G\ g$; and $i : L \bij L_F \uplus L_G$ is sent to \[
  \xymatrixcolsep{4pc} \xymatrix{L \ar[r]^-{\sim}_-i & L_F \uplus L_G
    \ar[r]^-{\sim}_-{\sigma_F \uplus \sigma_G} & L_F' \uplus L_G'}. \]

  When are two elements of $R$ \emph{inequivalent}, that is, when can we be
  certain two elements of $R$ are not related by a pair of
  relabellings?  Two elements $(L_{F1}, L_{G2}, f_1, g_1, i_1)$ and
  $(L_{F2},L_{G2},f_2,g_2,i_2)$ of $R$ are unrelated if and only if
  \begin{itemize}
  \item $f_1$ and $f_2$ have different forms, that is, they are
    unrelated by any relabelling, or
  \item $g_1$ and $g_2$ have different forms, or
  \item $L_{F1}$ and $L_{G1}$ ``sit inside'' $L$ differently than $L_{F2}$ and
    $L_{G2}$ in $L_2$, that is, $i_1^{-1}(L_{F1}) \neq i_2^{-1}(L_{F2})$.
  \end{itemize}
  (Note they are also unrelated if there is no bijection $L_{F1} \bij
  L_{F2}$ or no bijection $L_{G1} \bij L_{G2}$, but in those cases one
  of the first two bullets above would hold as well.)  The first two
  bullets are immediate; the third follows since a pair of
  relabellings can permute the elements of $L_F$ and $L_G$
  arbitrarily, or replace $L_F$ and $L_G$ with any other sets of the
  same size, but relabelling alone can never change which elements of
  $L$ correspond to $L_F$ and which to $L_G$, since that is preserved
  by composition with a coproduct bijection $\sigma_F \uplus
  \sigma_G$.

  Therefore, all the equivalence classes of $\quotient{R}{\eqrel}$ can
  be represented canonically by a partition of $L$ into two disjoint
  subsets, along with a choice of $F$ and $G$ structures, giving rise
  to the earlier definition:
  \begin{equation} \label{eq:product-partition}
    (F \sprod G)\ L = \biguplus_{L_F,L_G \partition L} F\ L_F \times
    G\ L_G.
  \end{equation}

  Also, in this case, the identity element is $j(I) = j(\varnothing) =
  \B(-,\varnothing)$, that is, the species which takes as input a
  label set $L$ and constructs the set of bijections between $L$ and
  the empty set.  Clearly there is exactly one such bijection when $L
  = \varnothing$, and none otherwise: as expected, this is the species
  $\One$ defined in the previous section.
\end{ex}

\begin{ex}
  Although $\B$ and $\P$ are equivalent, it is still instructive to
  work out the general definition in the case of $\P$, particularly
  because, as we have seen, proving $\B \iso \P$ requires the axiom
  of choice.

  We find that $\P$ has not just one but \emph{many} monoidal
  structures corresponding to disjoint union.  The action of such a
  monoid on objects of $\P$ is clear: the natural numbers $m$ and $n$
  are sent to their sum $m + n$.  For the action on morphisms, we are
  given $\sigma : \perm{(\Fin m)}$ and $\tau : \perm{(\Fin n)}$ and
  have to produce some $\perm{(\Fin (m+n))}$.  However, there are many
  valid ways to do this.  One class of examples arises from
  considering bijections \[ \varphi : \Fin m \uplus \Fin n \bij \Fin
  (m + n), \] which specify how to embed $\{0, \dots, m-1\}$ and $\{0,
  \dots, n-1\}$ into $\{0, \dots, m+n-1\}$.  Given such a $\varphi$,
  we may construct \[ \Omega(\varphi)(\sigma, \tau) \defeq \Fin (m+n)
  \stackrel{\varphi^{-1}}{\bij} \Fin m \uplus \Fin n \stackrel{\sigma
    \uplus \tau}{\bij} \Fin m \uplus \Fin n \stackrel{\varphi}{\bij}
  \Fin (m+n), \] as illustrated in \pref{fig:sumiso}. (Note that
  conjugating by $\varphi$ is essential for the functoriality of the
  result; picking some other bijection in place of, say,
  $\varphi^{-1}$, would result in a permutation that sent $\sigma =
  \tau = \id$ to something other than the identity.)
  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import           Control.Lens                   (partsOf, traverse, (%~))
import           Diagrams.Prelude               hiding (tau)

import           Data.Bits (xor)
import           SumPermDiagrams

phi :: Either Index Index -> Index
phi (Left 0) = 1
phi (Left 1) = 3
phi (Left 2) = 4
phi (Left 3) = 6
phi (Right 0) = 0
phi (Right 1) = 2
phi (Right 2) = 5

q :: Index -> Either Index Index
q n || n <= 3    = Left n
    || otherwise = Right (n-4)

sigma :: Index -> Index
sigma = (`xor` 1)

tau :: Index -> Index
tau = (`mod` 3) . succ

blues = iterateN 4 (blend 0.3 white) blue # reverse
reds = iterateN 3 (blend 0.3 white) red # reverse

dia =
  (hcat' (with & sep .~ 2) . map centerY $ -- $
     [ 'A' ||> column (permL (phi . q) (blues ++ reds)) [7]
     , 'B' ||> column (blues ++ reds) [4,3]
     , 'C' ||> column (permL sigma blues ++ permL tau reds)  [4,3]
     , 'D' ||> column (permL (phi . q) (permL sigma blues ++ permL tau reds))  [7]
     ]
   )
   # applyAll [connect' aOpts ('A' .> 'a' .> i) ('B' .> n) || i <- [0..6], let n = either2Name (inverse phi i) ]
   # applyAll [connect' aOpts ('B' .> 'a' .> i) ('C' .> 'a' .> sigma i) || i <- [0..3] ]
   # applyAll [connect' aOpts ('B' .> 'b' .> i) ('C' .> 'b' .> tau i) || i <- [0..3] ]
   # applyAll [connect' aOpts ('C' .> n) ('D' .> 'a' .> i) || i <- [0..6], let n = either2Name (inverse phi i) ]
   # frame 0.5
   # lwO 0.7

aOpts = with & gaps .~ (Local 0.2) & headLength .~ (Local 0.25)
    \end{diagram}
    \caption{$\Fin (m+n) \bij \Fin m \uplus \Fin n \bij \Fin m \uplus
      \Fin n \bij \Fin (m+n)$}
    \label{fig:sumiso}
  \end{figure}

  \begin{rem}
    Although it is not essential to what follows, we note that the
    $\Omega$ defined above, which sends bijections $\varphi : \Fin m
    \uplus \Fin n \bij \Fin (m + n)$ to functorial maps $\perm{(\Fin
      m)} \to \perm{(\Fin n)} \to \perm{(\Fin{(m+n)})}$, is neither
    injective nor surjective.  It is not injective since, for example,
    with $m = n = 1$, there are two distinct inhabitants of $\Fin 2
    \bij \Fin 1 + \Fin 1$, but both give rise to the same function
    $\perm{(\Fin 1)} \to \perm{(\Fin 1)} \to \perm{(\Fin 2)}$
    (\pref{fig:conjugations}), namely, the one which constantly
    returns the identity permutation (which, indeed, is the only such
    function which is functorial).

    \begin{figure}
      \centering
      \begin{diagram}[width=300]
import           SpeciesDiagrams
import           SumPermDiagrams

idDia = (hcat' (with & sep .~ 1.5) . map centerY $ -- $
      [ 'A' ||> column (repeat white) [2]
      , 'B' ||> column (repeat white) [1,1]
      , 'C' ||> column (repeat white) [1,1]
      , 'D' ||> column (repeat white) [2]
      ]
  )
  # connect' aOpts ('A' .> 'a' .> (0 :: Index)) ('B' .> 'a' .> (0 :: Index))
  # connect' aOpts ('A' .> 'a' .> (1 :: Index)) ('B' .> 'b' .> (0 :: Index))
  # connect' aOpts ('B' .> 'a' .> (0 :: Index)) ('C' .> 'a' .> (0 :: Index))
  # connect' aOpts ('B' .> 'b' .> (0 :: Index)) ('C' .> 'b' .> (0 :: Index))
  # connect' aOpts ('C' .> 'a' .> (0 :: Index)) ('D' .> 'a' .> (0 :: Index))
  # connect' aOpts ('C' .> 'b' .> (0 :: Index)) ('D' .> 'a' .> (1 :: Index))

swapDia =
  (hcat' (with & sep .~ 1.5) . map centerY $ -- $
    [ 'A' ||> column (repeat white) [2]
    , 'B' ||> column (repeat white) [1,1]
    , 'C' ||> column (repeat white) [1,1]
    , 'D' ||> column (repeat white) [2]
    ]
  )
  # connect' aOpts ('A' .> 'a' .> (0 :: Index)) ('B' .> 'b' .> (0 :: Index))
  # connect' aOpts ('A' .> 'a' .> (1 :: Index)) ('B' .> 'a' .> (0 :: Index))
  # connect' aOpts ('B' .> 'a' .> (0 :: Index)) ('C' .> 'a' .> (0 :: Index))
  # connect' aOpts ('B' .> 'b' .> (0 :: Index)) ('C' .> 'b' .> (0 :: Index))
  # connect' aOpts ('C' .> 'b' .> (0 :: Index)) ('D' .> 'a' .> (0 :: Index))
  # connect' aOpts ('C' .> 'a' .> (0 :: Index)) ('D' .> 'a' .> (1 :: Index))

dia = hcat' (with & sep .~ 2) [idDia, swapDia]
  # frame 0.5
  # lwO 0.7

aOpts = with & gaps .~ (Local 0.2) & headLength .~ (Local 0.25)
      \end{diagram}
      \caption{Distinct choices of $\varphi$ that result in identical
        permutations $f$}
      \label{fig:conjugations}
    \end{figure}

    Neither is $\Omega$ surjective.  Consider the case where $m = n =
    2$, and the function $f : \perm{(\Fin 2)} \to \perm{(\Fin
      2)} \to \perm{(\Fin 4)}$ given by the table:
    \begin{center}
    \begin{tabular}{c||cc}
             & $\id$  & $(12)$ \\
             \hline
      $\id$  & $\id$  & $(12)(34)$ \\
      $(12)$ & $(12)$ & $(34)$
    \end{tabular}
    \end{center}
    It is not hard to verify that $f$ is functorial; for example,
    $f\ \id\ (12) \then f\ (12)\ \id = (12)(34) \then (12) = (34) = f\
    (12)\ (12)$.  However, we will show that $f$ cannot be of the form
    $f\ \sigma\ \tau = \varphi \comp (\sigma \uplus \tau) \comp
    \varphi^{-1}$ for any $\varphi$.

    For a permutation $\psi$, denote by $\Fix(\psi) = \{ x \mid
    \psi(x) = x \}$ the set of fixed points of $\psi$, and by
    $\fix(\psi) = \size \Fix(\psi)$ the number of fixed points.  Note
    that $\fix(\sigma \uplus \tau) = \fix(\sigma) + \fix(\tau)$, since
    if some value $\inl\ s$ is fixed by $\sigma \uplus \tau$, then $s$
    must be fixed by $\sigma$, and conversely (and similarly for
    $\inr$ and $\tau$).  We also note the following lemma:
    \begin{lem}
      $\fix$ is invariant under conjugation; that is, for any
      permutations $\psi$ and $\varphi$ we have $\fix(\psi) =
      \fix(\varphi \comp \psi \comp \varphi^{-1})$.
    \end{lem}
    \begin{proof}
      Calculate as follows:
      \begin{sproof}
        \stmt{\psi(x) = x}
        \reason{\iff}{apply $\psi^{-1}$ to both sides}
        \stmt{x = \psi^{-1}(x)}
        \reason{\iff}{apply $\varphi \comp \psi \comp \varphi^{-1}
          \comp \varphi$ to both sides}
        \stmt{\varphi(\psi(\varphi^{-1}(\varphi(s)))) =
          \varphi(\psi(\varphi^{-1}(\varphi(\psi^{-1}(s)))))}
        \reason{\iff}{simplify}
        \stmt{(\varphi \comp \psi \comp
          \varphi^{-1})(\varphi(s)) = \varphi(s).}
      \end{sproof}
      Thus $\varphi$ is a bijection between the fixed points of $\psi$
      and those of $\varphi \comp \psi \comp \varphi^{-1}$.
    \end{proof}

    If $f\ \sigma\ \tau$ is of the form $\varphi \comp (\sigma \uplus
    \tau) \comp \varphi^{-1}$, we therefore have \[ \fix(f\ \sigma\
    \tau) = \fix(\varphi \comp (\sigma \uplus \tau) \comp
    \varphi^{-1}) = \fix(\sigma \uplus \tau) = \fix(\sigma) +
    \fix(\tau). \] However, the $f$ exhibited in the table above does
    not satisfy this equality: in particular, \[ \fix(f\ \id\ (12)) =
    \fix((12)(34)) = 0 \neq 2 = \fix(\id) + \fix((12)). \]
  \end{rem}

  We may now instantiate the definition of Day convolution (for some
  particular choice of monoid in $\P$), obtaining \[ (F \sprod G)\ n =
  \coend{n_F, n_G} F\ n_F \times G\ n_G \times (\Fin n \bij \Fin (n_F
  + n_G)). \]

  Again, letting $R \defeq \biguplus_{n_F, n_G} F_{n_F} \times G_{n_G}
  \times (\Fin n \bij \Fin {(n_F + n_G)})$, the coend is equivalent to
  $\quotient{R}{\eqrel}$, where \[ (n_F, n_G, f, g, i) \eqrel (n_F,
  n_G,\;F\ \sigma_F\ f,\;G\ \sigma_G\ g,\;i \then (\sigma_F +_\varphi
  \sigma_G)) \] for any $\sigma_F : \perm{(\Fin n_F)}$ and $\sigma_G :
  \perm{(\Fin n_G)}$.  Note that the meaning of $\sigma_F + \sigma_G$
  depends on the particular monoid we have chosen, which fixes an
  interpretation of $\Fin{(m+n)}$ as representing a disjoint union.

  Unlike in the case of $\fc \B \Set$, we cannot really simplify this
  any further.  In particular, it is \emph{not} equivalent to \[
  \biguplus_{n_F + n_G = n} F\ n_F \times G\ n_G, \] since that does
  not take into account the different ways the overall set of
  labels could be distributed between $F$ and $G$---that is, it
  throws away the information contained in the bijection $\Fin n \bij
  \Fin {(n_F + n_G)}$.  The reason we could ``get rid of'' the
  bijection in \eqref{eq:product-partition} is that the bijection is
  secretly encoded in the partition $L_F, L_G \partition L$.  In
  contrast, $n_F + n_G = n$ says nothing about the relationship of the
  actual labels, but only about the sizes of the label sets.
\end{ex}

\begin{ex}
  There is another monoidal structure on $\B$ corresponding to the
  Cartesian product of sets. If we instantiate the framework of Day
  convolution with this product-like monoidal structure---but
  keep everything else the same, in particular continuing to use
  products on $\Set$---we obtain the arithmetic product.

  That is, \[ (F \aprod G)\ L = \coend {L_F, L_G} F\ L_F \times G\ L_G
  \times (L \bij L_F \times L_G). \] By a similar argument to the one
  used above, this is equivalent to \[ \biguplus_{L_F,L_G \rectangle
    L} F\ L_F \times G L_G. \] In this case we also have $j(I) =
  j(\singleton) = \B(-,\singleton)$, the species which constructs all
  bijections between the label set and $\singleton$. There is only one
  such bijection whenever the label set is of size $1$ and none
  otherwise, so this is equivalent to the species $\X$, as expected.
\end{ex}

\begin{ex}
  We now verify that $\BT$ and $\ST$ have the right properties, so
  that partitional and arithmetic product are well defined on
  $(\fc \BT \ST)$-species.
  \begin{itemize}
  \item As with $\B$, there are monoidal structures on $\BT$
    corresponding to the coproduct and product of types. Note that
    when combining two finite types, their finiteness evidence must be
    somehow combined to create evidence for the finiteness of their
    product or coproduct.  For example, given equivalences $A \equiv \Fin
    m$ and $B \equiv \Fin n$, one must create an equivalence $A + B
    \equiv \Fin {(m + n)}$ (in the case of coproduct) or $A \times B
    \equiv \Fin {(mn)}$ (in the case of product). In the first case,
    this can be accomplished by combining the given equivalences with
    an equivalence $\Fin m + \Fin n \equiv \Fin {(m + n)}$, which can
    be implemented, say, by matching the elements of $\Fin m$ with the
    first $m$ elements of $\Fin {(m + n)}$, and the elements of $\Fin
    n$ with the remaining $n$ elements.  Likewise, $A \times B \equiv
    \Fin {(mn)}$ can be implemented via an equivalence $\Fin m \times
    \Fin n \equiv \Fin {(mn)}$, \eg the one which sends $(i,j)$ to $in
    + j$.  Fundamentally, there are many ways to implement such
    equivalences, but since everything is wrapped in a propositional
    truncation it does not ultimately matter, as long as there is
    \emph{some} way to implement them.
  \item $\BT$ can indeed be seen as enriched over $\ST$, since
    morphisms in $\BT$ are paths, which are equivalent to paths
    between the underlying sets, and because by \pref{cor:path-pres-set},
    $A = B$ is a set when $A$ and $B$ are.
  \item We have already seen that there is a symmetric monoidal
    structure on $\ST$ given by the product of types, which does
    preserve colimits.
  \item Finally, $\ST$ does have coends over $\BT$.  In fact, since
    $\BT$ is a groupoid, recall from \pref{sec:coends-hott}
    that coends are just $\Sigma$-types.
  \end{itemize}

  Given $F,G : \fc \BT \ST$, and picking the monoid corresponding to
  coproduct on $\BT$, we can instantiate the definition of Day
  convolution to get
  \[ (F \cdot G)\ L = \sum_{L_F, L_G} F\ L_F \times G\ L_G \times
  (L = L_F + L_G). \] That is, a value of type $(F \cdot G)\ L$
  consists of a choice of finite types $L_F$ and $L_G$, an $F$-shape
  and a $G$-shape, labelled by $L_F$ and $L_G$ respectively, and a
  path between $L$ and $L_F + L_G$.
\end{ex}

\section{Composition}
\label{sec:composition}

We have already seen that arithmetic product can be thought of as a
restricted sort of composition, where an $F$-structure contains
$G$-structures all of the same shape (or vice versa).  More generally,
there is an unrestricted version of composition, where $(F \comp
G)$-shapes consist of $F$-shapes containing \emph{arbitrary}
$G$-shapes.  That is, intuitively, to create an $(F \comp G)$-shape
over a given set of labels $L$, we first \emph{partition} $L$ into
subsets; create a $G$-shape over each subset; then create an $F$-shape
over the resulting set of $G$-shapes.

\subsection{Definition and examples}
\label{sec:comp-defn-and-examples}

We begin with the formal definition of \citet{bll}:
\begin{equation} \label{eq:composition-trad}
  (F \comp G)\ L = \sum_{\pi \partition L} F\ \pi \times \prod_{p \in
    \pi} G\ p
\end{equation}
(there are some subtle issues with this definition, to be discussed
shortly, but it will suffice to consider the general idea and some
examples). \pref{fig:composition} shows an abstract representation of
the definition, in which labels are shown as dots, and shapes are
represented abstractly as arcs drawn across edges leading to the
labels contained in the shape, identified by the name of a species.
So the diagram illustrates how an $(F \comp G)$-shape consists
abstractly of a top-level $F$-shape with subordinate $G$-shapes.
\begin{figure}
  \centering
  \begin{diagram}[width=250]
import SpeciesDiagrams

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
  \caption{Generic species composition}
  \label{fig:composition}
\end{figure}

\begin{ex}
  \pref{fig:composition-example} shows a concrete example of a $(\Bin
  \comp \List_+)$-shape, a binary tree containing nonempty lists.
\begin{figure}
  \centering
  \begin{diagram}[width=250]
import           Control.Lens                   (traverse, unsafePartsOf)
import           Data.List                      (permutations)
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

tOfLs = sampleBTree5
  # fmap ([2,3,1,3,1] !!)
  # fmap (\n -> replicate n ())
  # (unsafePartsOf (traverse.traverse) .~ [2,6,0,3,5,7,1,9,8,4])

treeOfLists =
  tree3 (\ls -> enrect (list2 ls (scale 0.5 . mloc) # centerX # scale 0.5 # fc black) # fc white)

enrect d = d <> roundedRect (width d + 0.2) (height d + 0.2) 0.2

tree3 nd
  = maybe mempty (renderTree nd (~~))
  . uniqueXLayout 1 1
  $ tOfLs  -- $

list2 ns nd = hcat' (with & sep .~ 1 & catMethod .~ Distrib)
  (map nd ns)
  <>
  hrule (fromIntegral (length ns - 1)) # alignL

dia = treeOfLists # frame 0.5 # lwO 0.7
  \end{diagram}
  \caption{An example $(\Bin \comp \List_+)$-shape}
  \label{fig:composition-example}
\end{figure}
\end{ex}

\begin{ex}
  As an example, we may define the species $\Par$ of \term{set
    partitions}, illustrated in \pref{fig:partitions}, by \[ \Par =
  \Bag \comp \Bag_+.\] That is, a set partition is a set of
  \emph{non-empty} sets. Similarly, the species $\Perm$ of
  permutations is given by $\Perm = \Bag \comp \Cyc$, a set of
  \emph{cycles}.
  \begin{figure}
    \centering
    \begin{diagram}[width=400]
import           Data.List
import           Data.List.Split
import qualified Math.Combinatorics.Multiset    as MS
import           SpeciesDiagrams

dia =
  hcat' (with & sep .~ 0.5)
  [ unord (map labT [0..3])
  , mkArrow 2 (txt "Par")
  , partStructures
  ]
  # centerXY
  # pad 1.1
  # lwO 0.7

drawPart = alignL . hcat' (with & sep .~ 0.2) . map (unord . map labT)

partStructures
  = centerXY
  . hcat' (with & sep .~ 1)
  . map (vcat' (with & sep .~ 0.5))
  . chunksOf 5
  . map drawPart
  . parts
  $ [0..3]
    \end{diagram}
    \caption{The species $\Par$ of partitions}
    \label{fig:partitions}
    %$
  \end{figure}

Given the species $\Par$, we may define the species $\Bin \times \Par$
of \term{partitioned trees}.  Structures of this species are labeled
binary tree shapes with a superimposed partitioning of the labels (as
illustrated in \pref{fig:partitioned-tree}), and can be used to model
trees containing data elements with decidable equality; the partition
indicates equivalence classes of elements.

\begin{figure}
  \centering
  \begin{diagram}[width=200]
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

t :: BTree Int
t = BNode 4 (BNode 2 Empty (leaf 5)) (BNode 1 (BNode 0 Empty (leaf 3)) (leaf 6))

dt = drawBinTree' (with & slHSep .~ 4 & slVSep .~ 3)

partitionedTree
  = dt (fmap (\n -> mloc n # named n) t)
  # applyAll (map drawPart [[4],[2],[5,1],[0,6],[3]])

drawPart :: [Int] -> Diagram B R2 -> Diagram B R2
drawPart [n] = withName n $ \sub -> atop (circle 1.3 # moveTo (location sub) # partStyle)
drawPart [n1,n2]
  = withNames [n1,n2] $ \[s1,s2] ->
      let p = location s1
          q = location s2
          c = alerp p q 0.5
          x = distance p q + 3
          r = direction (p .-. q)
      in  beneath (circle 1.5 # scaleToX x # rotate r # moveTo c
                     # partStyle)

partStyle x = x # lw thick # dashingG [0.1,0.1] 0 # lc (colors !! 2)

dia = partitionedTree
    # frame 0.5 # lwO 0.7
  \end{diagram}
  \caption{An example $(\Bin \times \Par)$-shape}
  \label{fig:partitioned-tree}
\end{figure}
\end{ex}

\begin{ex}
  The species $\Sp{R}$ of nonempty $n$-ary (``rose'') trees, with data
  stored at internal nodes, may be defined by the recursive species
  equation \[ \Rose = \X \sprod (\List \comp \Rose). \] An example
  $\Rose$-shape is shown in \pref{fig:rose-tree}.
  \begin{figure}
    \centering
    \begin{diagram}[width=150]
import SpeciesDiagrams

dia = tree # centerXY # frame 0.5 # lwO 0.7
    \end{diagram}
    \caption{An example $\Rose$-shape}
    \label{fig:rose-tree}
  \end{figure}
  Note the use of $\List$ means the children of each node are linearly
  ordered.  Using $\Bag$ in place of $\List$ yields a more
  graph-theoretic notion of a rooted tree, with no structure imposed
  on the neighbors of a particular node.

  $\Sp{Plan} = \X \cdot (\Cyc \comp \Rose)$ is the species of
  \emph{planar embeddings} of rooted trees, where the top-level
  subtrees of the root are ordered cyclically.  Each node other
  than the root, on the other hand, still has a linear order on
  its children, fixed by the distinguished edge from the node towards the
  root.
\end{ex}

\begin{ex}
  The species $\Sp{P}$ of \emph{perfect trees}, with data stored in
  the leaves, may be defined by \[ \Sp{P} = \X + (\Sp{P} \comp
  \X^2). \] That is, a perfect tree is either a single node, or a
  perfect tree containing \emph{pairs}.  Functional programmers will
  recognize this as a \term{non-regular} or \term{nested} recursive
  type; it corresponds to the Haskell type:
  \begin{spec}
    data P a = Leaf a | Branch (P (a,a))
  \end{spec}
  \pref{fig:perfect-shapes} illustrates some example $\Sp P$-shapes.
  \begin{figure}
    \centering
    \begin{diagram}[width=300]
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

pShape :: Int -> BTree (Maybe Int)
pShape = pShape' 0
  where
    pShape' i 0 = leaf (Just i)
    pShape' i n = BNode Nothing (pShape' i (n-1)) (pShape' (i + 2^ (n-1)) (n-1))

drawPShape :: BTree (Maybe Int) -> Diagram B R2
drawPShape = maybe mempty (renderTree (maybe mempty mloc) (~~)) . symmLayoutBin' tOpts

tOpts = with & slHSep .~ 2 & slVSep .~ 1.5

dia = hcat' (with & sep .~ 2) (map (alignB . drawPShape . pShape) [0..3])
   # frame 0.5
   # lwO 0.7
    \end{diagram}
    \caption{Example $\Sp P$-shapes}
    \label{fig:perfect-shapes}
  \end{figure}
\end{ex}

In addition to being the identity for $\aprod$, $\X$ is the
(two-sided) identity for $\comp$ as well.  We have \[ (\X \comp G)\ L
= \sum_{\pi \partition L} \X\ \pi \times \prod_{p \in \pi} G\ p, \] in
which $\X\ \pi$ is $\varnothing$ (cancelling the summands in which it
occurs) except in the case where $\pi$ is the singleton partition
$\{L\}$, in which case the summand is isomorphic to $G\ L$.  On the
other side, \[ (F \comp \X)\ L = \sum_{\pi \partition L} F\ \pi \times
\prod_{p \in \pi} \X\ p; \] the only way to get a product in which
none of the $\X\ p$ are $\varnothing$ is when $\pi \iso L$ is the
complete partition of $L$ into singleton subsets, in which case we
again have something isomorphic to $F\ L$.

As for generating functions, the mapping from species to egfs is
indeed homomorphic with respect to composition: \[ (F \comp G)(x) =
F(G(x)). \]  A direct combinatorial proof can be given, making use of
\emph{Fa{\`a} di Bruno's formula}~\citep{johnson2002curious}.

On the other hand, in general, \[ \unl{(F \comp G)}(x) \neq \unl
F(\unl G(x)). \] \citet[Exercise 1.4.3]{bll} pose the specific
counterexample of $\unl \Perm(x) \neq \unl \Bag(\unl \Cyc(x))$, which
is not hard to show (hint: $\unl \Perm(x) = \prod_{k \geq 1}
\frac{1}{1 - x^k}$ and $\unl \Cyc(x) = x + x^2 + x^3 + \dots =
\frac{x}{1-x}$).  A more intuitive explanation of the failure of ogfs
to be homomorphic with respect to composition---along with a
characterization of the situations when homomorphism does hold---is
left to future work.  In any case, to compute ogfs for composed
species, one may turn to \term{cycle index series}, which can be seen
as a generalization of both egfs and ogfs, and which retain more
information than either; see \citet[\Sect 1.2, \Sect 1.4]{bll} for
details.

As hinted previously, the formal definition of composition given in
\eqref{eq:composition-trad} requires additional qualification; in
particular, it requires delicate treatment with regard to partitions
and infinite families of shapes.  To see the issue, let $\Bin$ and
$\List$ be the species of binary trees and lists.  Consider the
species $\Bin \comp \List$, whose shapes should consist of binary
trees containing lists at their nodes.  Intuitively, this gives rise
to infinite families of shapes such as those illustrated in
\pref{fig:bin-comp-list-inf}, which are all of size $2$.

\begin{figure}
  \centering
  \begin{diagram}[width=350]
import           Data.Maybe                     (fromJust)
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

exampleTree 0 = leaf (Just [0,1])
exampleTree n = BNode (Just [0,1]) (emptyTree 0) (emptyTree (n-1))

emptyTree :: Int -> BTree (Maybe [Int])
emptyTree 0 = leaf Nothing
emptyTree n = BNode Nothing (emptyTree 0) (emptyTree (n-1))

enc g = fc white . enclose g 0.3

drawExampleTree
  = renderTree (maybe (enc 2.1 mempty) (enc 0.5 . fc black . drawList' mloc)) (~~)
  . fromJust
  . symmLayoutBin' (with & slHSep .~ 4 & slVSep .~ 3)
  . exampleTree

dots = hcat' (with & sep .~ 1) (replicate 3 dot)
  where dot = circle 0.2 # fc black

dia =
  (
    ( hcat' (with & sep .~ 3)
      [ drawExampleTree 0
      , drawExampleTree 1
      , drawExampleTree 2
      ]
    )
    # centerY
  ||||||
    strutX 3
  ||||||
    dots
  )
  # frame 0.5
  # lwO 0.7
  \end{diagram}
  \caption{An infinite family of $(\Bin \comp \List)$-shapes of size $2$}
  \label{fig:bin-comp-list-inf}
\end{figure}

There are several possible reactions to \pref{fig:bin-comp-list-inf},
depending on the exact setting in which we are working.
\begin{itemize}
\item If we are working in $(\fc \B \Set)$, where the set of shapes on
  a given set of labels may be infinite, then this should be allowed,
  and is exactly the meaning that composition ought to have in this
  case.  Note, however, that this means we would need to allow
  $\pi \partition L$ to include ``partitions'' with arbitrary numbers
  of \emph{empty} parts (to correspond to the empty lists).
  Typically, the notation $\pi \partition L$ denotes partitions into
  \emph{nonempty} parts.
\item On the other hand, if we are working in $(\fc \B \FinSet)$, as
  is more traditional in a combinatorial setting, this \emph{must not}
  be allowed.  One possibility would be to simply insist that
  $\pi \partition L$ in \eqref{eq:composition-trad} excludes
  partitions with empty parts, as is usual. But as we have just seen,
  this does not generalize nicely to $(\fc \B \Set)$, and in any case
  it would still be a bit strange, since, for example, $\Bin \comp
  \List$ and $\Bin \comp \List_+$ would ``silently'' end up being the
  same.  It is better to front the issue by simply insisting that $F
  \comp G$ is only defined when $G\ \varnothing = \varnothing$.
\end{itemize}

We can reformulate the definition of composition in a better way which
naturally allows for empty parts and which also makes for a clearer
path to a generalized notion of composition (to be discussed in the
next section).  In fact, \mbox{\citet[p. 11]{joyal}} already mentions
this as an alternative definition. The idea is to use another finite
set $P$, representing parts of a partition, and a function $\chi : L
\to P$ which assigns each $l \in L$ to some $p \in P$.  The fibers of
$\chi$, \ie the sets $\chi^{-1}(p)$ for $p \in P$, thus constitute a
partition of $L$.  Note, however, that this naturally allows for empty
parts, since $\chi$ may not be surjective.  We then say that an $(F
\comp G)$-shape on the labels $L$ consists of some set $P$, a
partition function $\chi : L \to P$, an $F$-shape on $P$, and
$G$-shapes on the fibers of $\chi$.  However, we must also quotient
out by bijections between $P$ and other finite sets; the precise
identity of $P$ should not matter.  We can thus define $(F \comp G)$
using a coend:
\begin{equation} \label{eq:composition-fibers}
(F \comp G)\ L = \coend {P \in \B} \sum_{\chi : L \to P} F\ P \times \prod_{p \in P} G\
  (\chi^{-1}\ p).
\end{equation}
In the case that $G\ \varnothing = \varnothing$ is required, only
surjective $\chi$ will result in shapes, so the coend reduces to the
original definition \eqref{eq:composition-trad}, using the notation
$\pi \partition L$ with its usual meaning of a partition into nonempty
parts.

\subsection{Generalized composition}
\label{sec:generalized-composition}

We first show how to carry out the definition of composition in $\fc
\B \Set$ even more abstractly, then discuss how it may be
generalized to other functor categories $\fc \Lab \Str$.
\citet{street2012monoidal} gives the following abstract definition of
composition:
\begin{equation} \label{eq:comp-street}
(F \comp G)\ L = \coend{K} F\ K \times G^{\size K}\ L,
\end{equation}
 where
$G^{n} = \underbrace{G \cdot \dots \cdot G}_n$ is the $n$-fold
partitional product of $G$.  Intuitively, this corresponds to a
top-level $F$-shape on labels drawn from the ``internal'' label set
$K$, paired with $\size K$-many $G$-shapes, with the labels from $L$
partitioned among all the $G$-shapes.  The coend abstracts over $K$,
ensuring that the precise choice of ``internal'' labels does not
matter up to isomorphism.

\begin{rem}
  Note how this corresponds to the second definition of composition
  given in \eqref{eq:composition-fibers}.  In particular, binary
  partitional product allows for the labels to be partitioned into the
  empty subset and the entire subset, so an iterated partitional
  product corresponds to partitions which contain an arbitrary number
  of empty parts.
\end{rem}

However, this definition is somewhat puzzling from a constructive
point of view, since it would seem that $G^{\size K}$ retains no
information about which element of $K$ corresponds to which $G$-shape
in the product.  The problem boils down, again, to the use of the
axiom of choice.  For each finite set $K$ we may choose some ordering
$K \bij \fin{\size K}$; this ordering then dictates how to match up
the elements of $K$ with the $G$-shapes in the product $G^{\size K}$.
More formally, given a species $G$ we can define the anafunctor $G^- :
\B \to \Spe$ which sends each finite set $K$ to the clique of $(\size
K)$-ary products of $G$, with the morphisms in the clique
corresponding to permutations (since $\Spe$ is symmetric monoidal with
respect to partitional product).  This then becomes a regular functor
in the presence of the axiom of choice.

In the particular case of $\fc \B \Set$, we can also avoid the axiom
of choice by using a more explicit construction (again due to
Street\footnote{Personal communication, 6 March 2014.}).  For a finite
set $K$ and category $\C$, recall that we may represent a $K$-indexed
tuple of objects of $\C$ by a functor $K \to \C$ (where $K$ is
considered as a discrete category).  It's important to note that this
``$K$-tuple'' has no inherent ordering (unless $K$ itself has
one)---it simply assigns an object of $\C$ to each element of $K$.
Denote by $\Delta_K : \C \to \C^K$ the diagonal functor which sends
an object $C \in \C$ to the $K$-tuple containing only copies of $C$.

Consider $\C = \FinSet$.  Given any discrete category $K$, the
diagonal functor $\Delta_K : \FinSet \to \FinSet^K$ has both a left
and right adjoint, which we call $\Sigma_K$ and $\Pi_K$: \[ \Sigma_K
\adj \Delta_K \adj \Pi_K. \] In particular, $\Sigma_K : \FinSet^K \to
\FinSet$ constructs $K$-indexed coproducts, and $\Pi_K$ constructs
indexed products. (In the special case $K = \disc{\cat{2}}$,
$\Sigma_{\disc{\cat{2}}}$ and $\Pi_{\disc{\cat{2}}}$ resolve to the
familiar notions of disjoint union and Cartesian product of
finite sets, respectively.)  One can see this by considering the
expansion of the adjoint relations as natural isomorphisms between
hom-sets.  For example, in the case of $\Pi_K$, we have \[ (\Delta_K\
A \to T) \iso (A \to \Pi_K\ T) \] where $A \in \FinSet$ and $T \in
\FinSet^K$.  Essentially this expands to something like \[ (A \to T_1)
\times \dots \times (A \to T_n) \iso (A \to \Pi_K\ T), \] and it is easy
to see that in order for the isomorphism to hold, we should have
$\Pi_K\ T = T_1 \times \dots \times T_N$. (In general, of course, $K$
need not have some associated indexing $1 \dots n$, but the same
argument can be generalized.)  We often omit the subscripts, writing
simply $\Sigma$ and $\Pi$ when $K$ is clear from the context.

Now consider $\C = \B$.  $\Delta_K$ does not have adjoints in $\B$; in
fact, categorical products and coproducts can be exactly characterized
as adjoints to $\Delta_{\disc{\cat{2}}}$, and we have already seen
that $\B$ does not have categorical products or coproducts.  However,
we can take $\Pi_K, \Sigma_K : \FinSet^K \to \FinSet$ and restrict
them to functors $\B^K \to \B$.  This is well-defined since $\FinSet$
and $\B$ have the same objects, and $\Pi_K$ and $\Sigma_K$ produce
only isomorphisms when applied to isomorphisms.  For example, if
$\alpha : A \bij A'$, $\beta : B \bij B'$, and $\gamma : C \bij C'$,
then $\Pi_{\disc{\cat{3}}} (\alpha, \beta, \gamma)$ is the isomorphism
$\alpha \times \beta \times \gamma : A \times B \times C \bij A'
\times B' \times C'$.

We can now define a general notion of indexed species product. For a
species $F : \fc \B \Set$ and $K \in \B$ a finite set, $F^K : \fc \B
\Set$ represents the $\size K$-fold partitional product of $F$,
indexed by the elements of $K$ (see
\pref{fig:indexed-species-product}): \[ F^K\ L = \coend{(P : \B^K)}
\B(\Sigma P, L) \times \Pi (F \comp P). \] Note that $K$ is regarded
as a discrete category, so $P \in \B^K$ is a $K$-indexed collection of
finite sets.  $\B(\Sigma P, L)$, a bijection between the coproduct of
$P$ and $L$, witnesses the fact that $P$ represents a partition of
$L$; the coend means there is only one shape per fundamentally
distinct partition. The composite $F \comp P = \xymatrix{K \ar[r]^P &
  \B \ar[r]^F & \Set}$ is a $K$-indexed collection of $F$-structures,
one on each finite set of labels in $P$; the $\Pi$ constructs their
product.

\begin{figure}
  \centering
  \begin{diagram}[width=300]
import           SpeciesDiagrams

mkFShape :: [Int] -> Diagram B R2
mkFShape labs = (es <> fShape) # connectUp
  where
    es = enRect (hcat' (with & sep .~ 0.5) (map mloc' labs)) # centerXY
    connectUp = applyAll
      [ withName l (\s -> beneath (location s ~~ topPt)) || l <- labs ]
    topPt = 0 ^& 2.5
    fShape =
      arc (9/16 @@@@ turn) (15/16 @@@@ turn) # scale 0.5 # moveTo topPt
      <>
      text "F" # scale 0.5 # moveTo topPt # translateX (-0.8)

mloc' :: Int -> Diagram B R2
mloc' n = mloc n # named n

fShapes =
  text "P" # scale 0.8
  |||||| strutX 1 ||||||
  hcat' (with & sep .~ 1)
  [ mkFShape [1,3,0]
  , mkFShape [5,2]
  , mkFShape [4,6]
  ]
  # centerX
  # underbrace (text "L" # scale 0.8 <> phantom (square 0.5 :: D R2))

underbrace lab d =
  vcat' (with & sep .~ 0.5)
  [ d
  , brace
  , lab
  ]
  where
    w = width d
    brace = centerX . strokeT . mconcat $  -- $
      [ corner
      , hrule ruleLen
      , corner # rotateBy (1/2) # reverseTrail
      , corner # rotateBy (-1/4) # reverseTrail
      , hrule ruleLen
      , corner # rotateBy (1/4)
      ]
    braceRad = 0.3
    ruleLen = (w - 4*braceRad) / 2
    corner = (arc (1/2 @@@@ turn) (3/4 @@@@ turn) # scale braceRad)

dia = fShapes
  # frame 0.5
  # lwO 0.7
  \end{diagram}
  \caption{Indexed species product}
  \label{fig:indexed-species-product}
\end{figure}

It is important to note that this is functorial in $K$: the action on
a morphism $\sigma : K \bij K'$ is to appropriately compose $\sigma$
with $P$.

The composition $F \comp G$ can now be defined by
\[ (F \comp G)\ L = \coend{K} F\ K \times G^K\ L. \]  This is
identical to the definition given in \eqref{eq:comp-street}, except
that $G^{\size K}$ has been replaced by $G^K$, which explicitly
records a mapping from elements of $K$ to $G$-shapes.

This explicit construction relies on a number of specific properties
of $\B$ and $\Set$, and it is unclear how it should generalize to other
functor categories. Fortunately, in the particular case of $\fc \BT
\ST$, in HoTT, this more complex construction is not necessary. The
anafunctor $G^- : \B \to \Spe$ discussed earlier corresponds in HoTT
to a regular functor $G^- : \BT \to (\fc \BT \ST)$: in a symmetric
monoidal category, the $(\size K)$-ary tensor product of $G$ is unique
up to isomorphism, which in an \hott{category} corresponds to actual
equality.

More generally, if we focus on the high-level definition \[ (F \comp
G)\ L = \coend K F\ K \times G^K\ L, \] leaving the definition of
$G^K$ abstract, we can enumerate the properties required of a general
functor category $\fc \Lab \Str$ to accommodate it: for starters,
$\Str$ must have coends over $\Lab$, and $(\Str, \times)$ must be
monoidal.  We can also say that, whatever the definition of $G^K$, it
will involve partitional product---so we must add in all the
requirements for that operation, enumerated in
\pref{sec:day-convolution}.  In fact, this already covers the
requirements of $\Str$ having coends and a monoid $\times$, so any
functor category $\fc \Lab \Str$ which supports partitional product
already supports composition as well.

For a formal proof that composition is associative, see
\citet[pp. 5--6]{kelly2005operads}, although some reflection on the
intuitive idea of composition should be enough to convince informally:
for example, a tree which contains cycles-of-lists is the same thing
as a tree-of-cycles containing lists.

Unlike the other monoidal structures on $\Spe$ (sum and Cartesian,
arithmetic, and partitional product), composition is not symmetric.
For example, as illustrated in \pref{fig:cyc-list-list-cyc}, there
are different numbers of $(\Cyc \comp \List)$-forms and $(\List \comp
\Cyc)$-forms of size $3$, and hence $\Cyc \comp \List \not \iso \List
\comp \Cyc$. \later{Some sort of connection to Traversable?}

\begin{figure}
  \centering
  \begin{diagram}[width=150]
import           Data.List                      (zip4)
import           SpeciesDiagrams

dot = circle 0.8 # fc black

enc = fc white . enclose 1 1

newCyc :: Double -> [Diagram B R2] -> Diagram B R2
newCyc r ds = position (zip posns (zipWith named [0 :: Int ..] ds)) <> circle r -- # markBorders
  where
    n = length ds
    triples = zip4 ([1 :: Int .. n-1] ++ [0])
                posns (tail (cycle posns)) ((tail . tail) (cycle posns))
    markBorders = withNames [0 :: Int .. n-1] $ \ss ->   -- $
      applyAll (map (mark2Borders ss) triples)
    mark2Borders ss (i,prev,cur,next) = id
      -- where
      --   pb = binarySearch
    posns :: [P2]
    posns
      || n == 1 = [0 ^& r]
      || otherwise = polygon (with & polyType .~ PolyRegular (length ds) r
                                  & polyOrient .~ NoOrient
                            )
                    # rotateBy (1/4)

cls = map (newCyc 2.5) ((map . map) (enc . drawList' (const dot) . flip replicate ()) [[1,1,1],[2,1],[3]])

lcs = map (drawList' id) ((map . map) (enc . newCyc 2 . flip replicate dot) [[1,1,1],[2,1],[1,2],[3]])

dia =
  hcat' (with & sep .~ 6)
  [ vcat' (with & sep .~ 3) cls # centerY
  , vcat' (with & sep .~ 3) lcs # centerY
  ]
  # frame 0.5
  # lwO 0.7
  \end{diagram}
  \caption{$(\Cyc \comp \List)$- and $(\List \comp \Cyc)$-forms of size 3}
  \label{fig:cyc-list-list-cyc}
\end{figure}

\begin{prop}
  $(\Spe, \comp, \X)$ is monoidal.
\end{prop}
\begin{proof}
  We have already seen that $\comp$ is associative and that $\X$ is an
  identity for composition. For formal proofs in a more generalized
  setting see, again, \citet{kelly2005operads}.
\end{proof}

Like associativity, the right-distributivity laws
\begin{gather*}
  (F + G) \comp H \iso (F \comp H) + (G \comp H) \\
  (F \cdot G) \comp H \iso (F \comp H) \cdot (G \comp H)
\end{gather*}
are easy to grasp on an intuitive level.  Their formal proofs are not
too difficult; the second specifically requires an isomorphism
$G^{K_1+K_2} \iso G^{K_1} \cdot G^{K_2}$, which ought to hold no
matter what the definition of $G^K$.  \later{Include these proofs?}
The reader may also enjoy discovering why the corresponding
left-distributivity laws are false (although they do correspond to
species \emph{morphisms} rather than isomorphisms).

\subsection{Internal Hom for composition}
\label{sec:internal-Hom-comp}

We have seen that $(\Spe, \comp, \X)$ is monoidal; in this section we
show that it is monoidal closed. Indeed, we can compute as follows
(essentially the same computation also appears in
\citet[p. 7]{kelly2005operads}, though in a more general form):

\begin{sproof}
  \stmt{\hom[\Spe]{F \comp G}{H}}
  \reason{\iso}{natural transformations are ends}
  \stmt{\eend L \hom[\Set] {(F \comp G)\ L}{H\ L}}
  \reason{\iso}{definition of $\comp$}
  \stmt{\eend L \hom[\Set]{(\coend K F\ K \times G^K\ L)}{H\ L}}
  \reason{\iso}{$(\hom[\Set] - {H\ L})$ turns colimits into limits}
  \stmt{\eend L \eend K \hom[\Set] {(F\ K \times G^K\ L)}{H\ L}}
  \reason{\iso}{currying}
  \stmt{\eend L \eend K \hom[\Set] {F\ K}{(\hom[\Set] {G^K\ L}{H\
        L})}}
  \reason{\iso}{$(\hom[\Set] {F\ K} -)$ preserves limits}
  \stmt{\eend K \hom[\Set] {F\ K}{\eend L (\hom[\Set] {G^K\ L}{H\
        L})}}
  \reason{\iso}{natural transformations are ends}
  \stmt{\eend K \hom[\Set] {F\ K}{(\hom[\Spe] {G^K}{H})}}
  \reason{\iso}{natural transformations are ends}
  \stmt{\hom[\Spe] F {(\hom[\Spe] {G^-}{H})}}
\end{sproof}

Thus we have the adjunction \[ (\hom[\Spe]{F \comp G}{H}) \iso
(\hom[\Spe]{F}{(\chom G H)}), \] where \[ (\chom G H) \defeq
(\hom[\Spe]{G^-}{H}) \] is the species whose $K$-labelled shapes are
species morphisms from $G^K$ to $H$. An illustrated example is shown
in \pref{fig:internal-Hom-comp-example}: a species morphism from a
binary tree of cycles to a rose tree is equivalent to a species
morphism that takes the underlying tree shape on the label set $K$ and
produces another species morphism, which itself expects a $K$-indexed
partitional product of cycles and produces a rose tree.  One can see
how the composition is decomposed into its constituent parts, with a
new label type $K$ introduced to mediate the relationship between
them.

\begin{figure}
  \centering
  \begin{diagram}[width=400]
import           Data.Tree
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams
import           Structures                     (pair)

mloc2 c = text [c] <> circle 0.8 # fc (colors !! 2)
enc = fc white . enclose 0.5 0.5

tData = BNode 2 (leaf 0) (BNode 1 (leaf 3) Empty)

cycs = map (flip cyc' 0.8 . map (scale 0.4 . fc black . mloc))
  [[1,3,7], [0], [2,4], [5,9,6,8]]

t = scale 0.5 . drawBinTree' (with & slHSep .~ 4 & slVSep .~ 3) . fmap (mloc2 . ("abcd"!!)) $ tData
toc = drawBinTree' (with & slHSep .~ 6 & slVSep .~ 4) (fmap (enc . (cycs!!)) tData)

r :: Tree Int
r = Node 7 [Node 9 [rleaf 4, rleaf 3, rleaf 2], rleaf 0, Node 1 [Node 5 [rleaf 8], rleaf 6]]
  where rleaf n = Node n []

rtree = scale 0.5 . renderTree mloc (~~) . symmLayout' (with & slHSep .~ 3 & slVSep .~ 4)  $ r

kcycs = hcat' (with & sep .~ 1) (map mkCyc [0..3])
  where
    mkCyc i = vcat' (with & sep .~ 0.2)
      [ mloc2 ("abcd" !! i) # scale 0.5
      , vrule 1
      , cycs !! i
      ]

lhs = fun toc rtree

rhs = fun t (enRect' 1 (fun kcycs rtree))

dia =
  vcat' (with & sep .~ 2)
  [ lhs # centerX
  , text "≅" # scale 2
  , rhs # centerX
  ]
  # frame 1
  # lwO 0.7
  \end{diagram}
  \caption{Internal Hom for composition}
  \label{fig:internal-Hom-comp-example}
\end{figure}

\section{Functor composition}
\label{sec:functor-composition}

There is a more direct variant of composition, known as \term{functor
  composition} \citep{bll, decoste1992functorial}.  When species are
defined as endofunctors $\B \to \B$, the functor composition $F \fcomp
G$ can literally be defined as the composition of $F$ and $G$ as
functors, that is, \[ (F \fcomp G)\ L = F\ (G\ L). \] However, if
species are viewed as functors $\B \to \Set$ then this operation is
not well-typed as stated, and indeed feels somewhat unnatural.  This
problem is discussed further in \pref{sec:gen-functor-composition}.
For the most part, incorporating functor composition into this
framework is left to future work, but it is worth describing briefly
here.

An $(F \fcomp G)$-shape on the set of labels $L$ can intuitively be
thought of as \mbox{consisting} of \emph{all possible} $G$-shapes on the
labels $L$, with an $F$-shape on this collection of $G$-shapes as
labels.  Functor composition thus has a similar relationship to
partitional composition as Cartesian product has to partitional
product.  With partitional \mbox{product}, the labels are partitioned into
two disjoint sets, whereas with Cartesian product the labels are
shared.  With partitional composition, the labels are partitioned into
(any number of) subsets with a $G$-shape on each; with functor
composition, the labels are shared among \emph{all possible}
$G$-shapes.

\begin{rem}
  There is no standard operation which directly creates an $F$-shape
  on only \emph{some} $G$-shapes, with the labels $L$ shared among
  them.  To accomplish this one can simply use $(F \cdot \Rubbish)
  \fcomp G$.
\end{rem}

\begin{ex}
  The species of simple, directed graphs can be described by \[ (\Bag
  \cdot \Rubbish) \fcomp (\X^2 \cdot \Rubbish). \] Each $(\X^2 \cdot
  \Rubbish)$-shape applied to the same set of labels $L$ picks out an
  ordered pair of distinct labels, which can be thought of as a
  directed edge.  Taking the functor composition with $(\Bag \cdot
  \Rubbish)$ thus picks out a subset of the total collection of
  possible directed edges.

  A number of variants are also possible.  For example, to allow
  self-loops, one can replace $\X^2$ by $(\X + \X^2)$; to use
  undirected instead of directed edges, one can replace $\X^2$ by
  $\Bag_2$; and so on.
\end{ex}

\section{Differentiation}
\label{sec:differentiation}

The derivative of container types is a notion already familiar to many
functional programmers through the work of \citet{Huet_zipper},
\citet{mcbride:derivative, mcbride_clowns_2008} and
\citet{abbott_deriv}: the derivative of a type is its type of
``one-hole contexts''.  For example, \pref{fig:derivative-example}
shows a $\Bin'$-shape, where $\Bin$ is the species of rooted binary
trees; there is a ``hole'' in a place where a label would normally be.

This section begins by presenting the formal definition of derivative
for species, along with some examples (\pref{sec:basic-diff}).  Some
related notions such as up and down operators
(\pref{sec:up-down-operators}) and pointing (\pref{sec:pointing})
follow.  The basic notion of differentiation does not generalize
nicely to other functor categories, but this is rectified by a more
general notion of higher derivatives, of which the usual notion of
derivative is a special case (\pref{sec:higher-derivatives}).
Finally, this notion of higher derivatives paves the way for
discussing the internal Hom functors for partitional and arithmetic
product (\pref{sec:internal-Hom-pprod-aprod}).

There is much more that can be said about differentiation
\citep{Menni2008, labelle2009general, piponi2010divided,
  piponi2010constraining, stay2014q, McBrideNaperian}; in general,
there seems to remain a great deal of rich material on differentiation
waiting to be explored.

\subsection{Differentiation in $\fc \B \Set$}
\label{sec:basic-diff}

Formally, we create a ``hole'' by adjoining a new distinguished
label to the existing set of labels:

\begin{figure}
  \centering
  \begin{diagram}[width=150]
import           Data.Tree
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

sampleT7' :: Tree (Maybe Int)
sampleT7' = fmap (\n -> if n == 4
                           then Nothing
                           else Just ((n + 3) `mod` 8)) sampleT7

derTree =
  renderTree
    (maybe holeNode mloc)
    (~~)
    (symmLayout' (with & slHSep .~ 4 & slVSep .~ 4) sampleT7')

dia = derTree
   # frame 0.5
   # lwO 0.7
  \end{diagram}
  \caption{An example $\Bin'$-shape}
  \label{fig:derivative-example}
\end{figure}

\begin{defn}
  The \term{derivative} $F'$ of a species $F$ is defined by \[ F'\ L =
  F\ (L \uplus \singleton). \] The transport of relabellings along the
  derivative is defined as expected, leaving the distinguished label
  alone and transporting the others.
\end{defn}
In other words, an $F'$-shape on the set of labels $L$ is an $F$-shape
on $L$ plus one additional distinguished label.  It is therefore
slightly misleading to draw the distinguished extra label as an
indistinct ``hole'', as in \pref{fig:derivative-example}, since, for
example, taking the derivative twice results in two \emph{different,
  distinguishable} holes.  But thinking of ``holes'' is still a good
intuition for most purposes.

\begin{ex}
  Denote by $\arbor$ the species of \emph{unrooted} trees, \ie
  trees in the pure graph-theoretic sense of a collection of vertices
  and unoriented edges with no cycles.  Also let $\Arbor = \X
  \cdot (\Bag \comp \Arbor)$ denote the species of rooted trees
  (where each node can have any number of children, which are
  unordered).  It is difficult to get a direct algebraic handle on
  $\arbor$; however, we have the relation \[ \arbor' \iso
  \Bag \comp \Arbor, \] since an unrooted tree with a hole in it is
  equivalent to the set of all the subtrees connected to the hole
  (\pref{fig:der-tree-pointed-trees}).  Note that the subtrees
  connected to the hole become \emph{rooted} trees; their root is
  distinguished by virtue of being the node adjacent to the hole.

  \begin{figure}
    \centering
    \begin{diagram}[width=350]
import           SpeciesDiagrams                   (holeNode, mloc, mlocColor)

import           Data.Graph.Inductive.Graph        (delNode, mkGraph)
import           Data.Graph.Inductive.PatriciaTree
import           Data.GraphViz
import           Data.List                         (findIndex)
import           Data.Maybe                        (fromJust)
import           Data.Tree
import           Data.Tuple                        (swap)
import           Diagrams.TwoD.Layout.Tree
import           System.IO.Unsafe

import           GraphViz

numNodes = 14

gEdges = map swap [(5,8),(12,8),(4,8),(8,13),(1,13),(3,13),(2,3),(9,2),(0,13),(10,0),(6,0),(11,6),(7,6)]

gr :: Gr () ()
gr = mkGraph [(n,()) || n <- [0..numNodes-1]] (map (\(x,y) -> (x,y,())) gEdges)

children r = map snd . filter ((==r) . fst) $ gEdges  -- $
roots = children 13

trees :: [Tree Int]
trees = subForest (getTree 13)

getTree r = Node r (map getTree (children r))

dn 13 = holeNode # scale 1.5
dn n  = mloc' n # scale 1.5

de n1 n2
  || n1 == n2 = id
  || otherwise = connectOutside' (with & arrowHead .~ noHead) n1 n2

tree' = graphToDia dn de (unsafePerformIO (graphToGraph' nonClusteredParams TwoPi gr))
  # frame 0.5 # lwO 0.7

rTrees = hcat' (with & sep .~ 2) (map dTree trees)

dTree = renderTree drn (~~) . symmLayout' (with & slHSep .~ 4 & slVSep .~ 3)
  where
    drn n || n `elem` roots = mloc' n <> circle (width (mloc n :: D R2) / 2 + 0.2) # fc white
          || otherwise      = mloc' n

mloc' n || n < 10    = mloc n
        || otherwise = text (show n) # scale 0.8 <> circle 0.8 # fc mlocColor

dia =
  hcat' (with & sep .~ 3)
  [ tree' # centerY
  , text "≅" # scale 3 <> phantom (square 3 :: D R2)
  , rTrees # centerY # scale 1.5
  ]
  # frame 0.5 # lwO 0.7
    \end{diagram}
    \caption{$\arbor' \iso \Bag \comp \Arbor$}
    \label{fig:der-tree-pointed-trees}
  \end{figure}
\end{ex}

\begin{ex}
  $\Cyc' \iso \List$, as illustrated in \pref{fig:cycle-deriv}.

  \begin{figure}[htp]
    \centering
    \begin{diagram}[width=250]
import           SpeciesDiagrams

ls = [2,0,1,3]

derCyc = cyc' (smallHoleNode : map labT ls) 1.1

derCycEquiv = hcat' (with & sep .~ 1)
  [ derCyc
  , text "≅" # scale 0.6
  , drawList' labT ls
  ]

dia = derCycEquiv
   # frame 0.5
   # lwO 0.7
    \end{diagram}
    \caption{$\Cyc' \iso \List$}
    \label{fig:cycle-deriv}
  \end{figure}
\end{ex}

\begin{ex}
  $\List' \iso \List^2$, as illustrated in \pref{fig:list-deriv}.
  \begin{figure}
    \centering
    \begin{diagram}[width=300]
import           SpeciesDiagrams

ls = [2,0,5,1,4,3] # map (\n -> if n == 5
                                   then Nothing
                                   else Just n)
pair x y = hcat
  [ roundedRect' 2 1 (with & radiusTL .~ 0.2 & radiusBL .~ 0.2) <> x
  , roundedRect' 3 1 (with & radiusTR .~ 0.2 & radiusBR .~ 0.2) <> y
  ]

listCycEquiv = hcat' (with & sep .~ 1)
  [ drawList' (maybe smallHoleNode labT) ls
  , text "≅" # scale 0.6
  , pair (drawList' labT [2,0]) (drawList' labT [1,4,3])
  ]

dia = listCycEquiv
   # frame 0.5
   # lwO 0.7
    \end{diagram}
    \caption{$\List' \iso \List^2$}
    \label{fig:list-deriv}
  \end{figure}
\end{ex}

\begin{ex}
  Well-scoped terms of the (untyped) lambda calculus may be
  represented as shapes of the species \[ \Lambda = \elts + \Lambda^2
  + \Lambda'. \] Recall that $\elts = \X \cdot \Rubbish$ is the
  species of elements.  (This example appears implicitly---without an
  explicit connection to species---in the work of
  \citet{altenkirch2010monads}, and earlier also in that of
  \citet{altenkirch1999monadic} and \citet{fiore2003abstract}.)
  Labels correspond to (free) variables, that is, the elements of
  $\Lambda\ V$ are well-scoped lambda calculus terms with free
  variables taken from the set $V$.  The above equation for $\Lambda$
  can thus be interpreted as saying that a lambda calculus term with
  free variables in $V$ is either
  \begin{itemize}
    \item an element of $V$, \ie a variable,
    \item a pair of terms (application), or
    \item a lambda abstraction, represented by a term with free
      variables taken from the set $V \uplus \singleton$.  The new
      variable $\star$ of course represents the variable bound by the
      abstraction.
  \end{itemize}
  The set of \emph{closed} terms is thus given by $\Lambda\
  \varnothing$.  Note that there are infinitely many terms with any
  given number of free variables, so this is not useful for doing
  \emph{combinatorics}; as an equation of generating functions,
  $\Lambda(x) = \elts(x) + \Lambda^2(x) + \Lambda'(x)$ has no
  solution.  To do combinatorics with lambda terms one must also count
  applications and abstractions as contributing to the size, \eg using
  a two-sort species (\pref{sec:multisort}) such as \[ \Xi = \X \cdot
  \Bag + \Y \cdot \Xi^2 + \Y \cdot \frac{\partial}{\partial \X} \Xi \]
  which uses labels of sort $\Y$ to mark occurrences of applications
  and abstractions. For a similar approach see \citet{grygiel2013counting,
    lescanne2013counting}.
\end{ex}

The operation of species differentiation obeys laws which are familiar
from calculus:
\begin{gather*}
  \One' \iso \Zero \\
  \X' \iso \One \\
  \Bag' \iso \Bag \\
  (F + G)' \iso F' + G' \\
  (F \cdot G)' \iso F' \cdot G + F \cdot G' \\
  (F \comp G)' \iso (F' \comp G) \cdot G'
\end{gather*}
The reader may enjoy working out \emph{combinatorial} interpretations
of these laws.

In addition, differentiation of species corresponds to differentiation
of exponential generating functions, as one might hope. We have
\begin{align*}
\ddx (F(x)) &= \ddx \left( \sum_{n \geq 0} f_n
  \frac{x^n}{n!} \right) \\
&= \sum_{n \geq 1} f_n \frac{x^{n-1}}{(n-1)!} \\
&= \sum_{n \geq 0} f_{n+1} \frac{x^n}{n!} \\
&= \left(\ddx F\right)(x),
\end{align*}
since by definition the number of $(F')$-shapes of size $n$ is indeed
equal to $f_{n+1}$, the number of $F$-shapes on $n+1$ labels.

Unfortunately, once again \[ \unl{(F')}(x) \neq \unl F'(x) \] in
general, \later{Explain why? Intuition?} though a corresponding
equation does hold for cycle index series, which may be used to
compute the ogf for a species defined via differentiation.

\subsection{Up and down operators}
\label{sec:up-down-operators}

\citet[\Sect 8.12]{aguiar2010monoidal} define \term{up} and \term{down
  operators} on species; although the import or usefulness of up and
down operators is not yet clear to me, my instinct tells me that they
will indeed have important roles to play, so I include a brief
discussion of them here.

\begin{defn}
  An \term{up operator} on a species $F$ is a species morphism $u : F
  \to F'$.
\end{defn}
Since a species morphism is a natural, label-preserving map, an up
operator must essentially ``add'' an extra ``hole'' somewhere in a
shape. (Of course it can also rearrange existing labels, as long as it
does so in a natural way that does not depend on the identity of the
labels at all.)

\begin{ex}
  The species $\Bag$ of sets has a trivial up operator which sends the
  unique set shape on $L$ to the unique set shape on $L \uplus
  \singleton$ (\pref{fig:up-down-set}).
  \begin{figure}
    \centering
    \begin{diagram}[width=200]
import           SpeciesDiagrams

set = tag 0 (decoratePath (pentagon 1) (map labT [0..3] ++ [mempty]))

set' = tag 0 (decoratePath (pentagon 1) (map labT [0..3] ++ [smallHoleNode]))

dia =
  hcat' (with & sep .~ 0.5)
    [ set
    , vcat' (with & sep .~ 0.3) . map centerX $ [arrow 1.5, arrow 1.5 # reflectX]  -- $
    , set'
    ]
  # frame 0.5 # lwO 0.7
    \end{diagram}
    \caption{The trivial up and down operators on $\Bag$}
    \label{fig:up-down-set}
  \end{figure}
\end{ex}

\begin{ex}
  The species $\List$ of linear orders has an up operator which adds a
  hole in the leftmost position (\pref{fig:up-list}).  There is a
  similar operator which adds a hole in the rightmost position.  In fact,
  there are many other examples (particularly since species maps are
  allowed to do something completely different at every size), but
  these are two of the most apparent.
  \begin{figure}
    \centering
    \begin{diagram}[width=300]
import           SpeciesDiagrams

list = drawList' labT [3,0,1,2]
list' = drawList' id (smallHoleNode : map labT [3,0,1,2])

dia =
  hcat' (with & sep .~ 0.5)
    [ list
    , arrow 1
    , list'
    ]
  # frame 0.5 # lwO 0.7
    \end{diagram}
    \caption{An up operator on $\List$}
    \label{fig:up-list}
  \end{figure}
\end{ex}

\begin{ex}
  We can similarly make an up operator for the species $\Bin$ of
  binary trees, which adds a hole as the leftmost (or rightmost) leaf
  (\pref{fig:up-btree}).
  \begin{figure}
    \centering
    \begin{diagram}[width=350]
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

t1 = BNode 2 (leaf 1) (leaf 0)
t2 = BNode 3 (BNode 1 Empty (leaf 4)) (BNode 0 Empty (leaf 2))

up = addLeftmost Nothing . fmap Just

addLeftmost a Empty = leaf a
addLeftmost a (BNode b l r) = BNode b (addLeftmost a l) r

tree1 = fmap labT t1
tree1' = fmap (maybe smallHoleNode labT) (up t1)
tree2 = fmap labT t2
tree2' = fmap (maybe smallHoleNode labT) (up t2)

dia =
  hcat' (with & sep .~ 0.5)
    [ drawBinTree tree1
    , arrow 1 # translateY (-1)
    , drawBinTree tree1'
    , strutX 1
    , drawBinTree tree2
    , arrow 1 # translateY (-1)
    , drawBinTree tree2'
    ]
  # frame 0.5 # lwO 0.7
    \end{diagram}
    \caption{An up operator on $\Bin$}
    \label{fig:up-btree}
  \end{figure}
\end{ex}

\begin{ex}
  The species $\Cyc$ of cycles, on the other hand, has no up
  operator. Recall that $\Cyc' = \List$; there is no way to define a
  \emph{natural} map $\varphi : \Cyc \to \List$.  As a counterexample,
  consider \[ \xymatrix{ \Cyc\ \cat{2} \ar[r]^{\varphi_\cat{2}}
    \ar[d]_{\Cyc\ \sigma} & \List\ \cat{2} \ar[d]^{\List\ \sigma} \\
    \Cyc\ \cat{2} \ar[r]_{\varphi_{\cat{2}}} & \List\ \cat{2}} \]
  where $\cat{2} = \{0,1\}$ is a two-element set, and $\sigma :
  \cat{2} \bij \cat{2}$ is the permutation that swaps $0$ and $1$.
  The problem is that $C\ \sigma$ is the identity on $\Cyc\ \cat{2}$,
  but $\List\ \sigma$ is not the identity on $\List\ \cat{2}$, so this
  square cannot possibly commute.

  Generalizing from this example, one intuitively expects that there is
  no up operator whenever taking the derivative breaks some
  symmetry, as in the case of $\Cyc$.  Formalizing this intuitive
  observation is left to future work.
\end{ex}

\term{Down operators} are defined dually, as one would expect:
\begin{defn}
  A \term{down operator} on a species $F$ is a species morphism $d :
  F' \to F$.
\end{defn}

\begin{ex}
  Again, $\Bag$ has a trivial down operator, which is the inverse of
  its up operator.
\end{ex}

\begin{ex}
  Although we saw previously that the species $\Cyc$ of cycles has no
  up operator, it has an immediately apparent down operator, namely,
  the natural map $\Cyc' \to \Cyc$ which removes the hole from a
  cycle, that is, which glues together the two ends of a list.
  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import           SpeciesDiagrams

ls = [2,0,1,3]

derCyc = cyc' (smallHoleNode : map labT ls) 1.1

theCyc = cyc' (map labT ls) 0.9

downCyc = hcat' (with & sep .~ 1)
  [ derCyc
  , arrow 1
  , theCyc
  ]

dia = downCyc
   # frame 0.5
   # lwO 0.7
    \end{diagram}
    \caption{A down operator on $\Cyc$}
    \label{fig:down-cyc}
  \end{figure}
\end{ex}

\begin{ex}
  The species $\List$ of linear orders also has an apparent down
  operator, which simply removes the hole.

\begin{rem}  % mbox needed to mitigate some strange interaction of rem
             % environment and citet command, which makes "Remark"
             % show up at the beginning of the *following* para.
  \mbox{}\citet[p. 275, Example 8.56]{aguiar2010monoidal} define a down
  operator on $\List$ which removes the hole \emph{if} it is in the
  leftmost position, and ``sends the order to $0$'' otherwise.
  However, this seems bogus.  First of all, it is not clear what is
  meant by $0$ in this context; assuming it denotes the empty list, it
  is not well-typed, since species morphisms must be label-preserving.
\end{rem}
\end{ex}

\begin{ex}
  It takes a bit more imagination, but it is not too hard to come up
  with examples of down operators for the species $\Bin$ of binary
  trees.  For example, the two subtrees beneath the hole can be
  ``stacked'', with the first subtree added as the leftmost leaf of
  the remaining tree, and the other subtree added as \emph{its}
  leftmost leaf (\pref{fig:down-btree-stack}), or nodes could be
  iteratively promoted to fill the hole, say, preferring the
  left-hand node when one is available
  (\pref{fig:down-btree-promote}).
  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

t1 = BNode (Just 3) (leaf (Just 0)) (BNode Nothing (BNode (Just 1) Empty (BNode (Just 2) (leaf (Just 6)) (leaf (Just 7)))) (BNode (Just 5) Empty (leaf (Just 4))))

downOp :: BTree (Maybe a) -> BTree (Maybe a)
downOp t = addLeftmost r (addLeftmost l t')
  where
    Just (t',l,r) = deleteHole t
    deleteHole Empty = Nothing
    deleteHole (BNode Nothing l r) = Just (Empty, l, r)
    deleteHole t@@(BNode (Just a) l r) =
      case (deleteHole l, deleteHole r) of
        (Nothing,Nothing) -> Nothing
        (Just (l', ls, rs), _) -> Just (BNode (Just a) l' r, ls, rs)
        (_, Just (r', ls, rs)) -> Just (BNode (Just a) l r', ls, rs)

addLeftmost t Empty = t
addLeftmost a (BNode b l r) = BNode b (addLeftmost a l) r

renderBT = fmap (maybe smallHoleNode labT)

dia =
  hcat' (with & sep .~ 0.5)
    [ drawBinTree (renderBT t1)
    , arrow 1 # translateY (-2)
    , drawBinTree (renderBT $ downOp t1)  -- $
    ]
  # frame 0.5 # lwO 0.7
    \end{diagram}
    \caption{An example down operator on $\Bin$, via stacking}
    \label{fig:down-btree-stack}
  \end{figure}

  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

t1 = BNode (Just 3) (leaf (Just 0)) (BNode Nothing (BNode (Just 1) Empty (BNode (Just 2) (leaf (Just 6)) (leaf (Just 7)))) (BNode (Just 5) Empty (leaf (Just 4))))

promote :: BTree (Maybe a) -> BTree (Maybe a)
promote Empty = Empty
promote (BNode (Just a) l r) = BNode (Just a) (promote l) (promote r)
promote (BNode Nothing Empty Empty) = Empty
promote (BNode Nothing Empty (BNode a l r)) = BNode a Empty (promote (BNode Nothing l r))
promote (BNode Nothing (BNode a l r) r') = BNode a (promote (BNode Nothing l r)) r'

renderBT = fmap (maybe smallHoleNode labT)

dia =
  hcat' (with & sep .~ 0.5)
    [ drawBinTree (renderBT t1)
    , arrow 1 # translateY (-2)
    , drawBinTree (renderBT $ promote t1)  -- $
    ]
  # frame 0.5 # lwO 0.7
    \end{diagram}
    \caption{An example down operator on $\Bin$, via promotion}
    \label{fig:down-btree-promote}
  \end{figure}

  These operators are somewhat reminiscent of deletion from data
  structures such as binary search trees or heaps.  Those algorithms
  rely on a linear order on the labels, and hence do not qualify as
  natural species morphisms.  However, they do indeed qualify as down
  operators on the $\L$-species of binary search trees and heaps,
  respectively (see \pref{sec:manifestly-finite} and
  \pref{sec:L-species}).
\end{ex}

\subsection{Pointing}
\label{sec:pointing}

\begin{defn}
The operation of \term{pointing} can be defined in terms of the
species of elements, $\elts = \X \cdot \Rubbish$, and Cartesian
product:
 \[ \pt F = \elts \times F. \]
\end{defn}
As illustrated on the left-hand side of \pref{fig:pointing}, an $\pt F$-structure can be
thought of as an $F$-structure with one particular distinguished
element.
  \begin{figure}
    \centering
    \begin{diagram}[width=300]
import           Data.Tree
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

sampleT7' :: Tree (Either Int Int)
sampleT7' = fmap (\n -> if n == 4
                           then Left n
                           else Right n) sampleT7

derTree =
  renderTree
    (either (const holeNode) mloc)
    (~~)
    (symmLayout' (with & slHSep .~ 4 & slVSep .~ 4) sampleT7')

pair x y = hcat
  [ roundedRect' (width x + 1) ht (with & radiusTL .~ 1 & radiusBL .~ 1) <> x # centerXY
  , roundedRect' (width y + 1) ht (with & radiusTR .~ 1 & radiusBR .~ 1) <> y # centerXY
  ]
  where
    ht = max (height x) (height y) + 1

xTreePair = pair (mloc 4) derTree

pointedTree =
  renderTree
    (either ((<> (circle 1 # fc white)) . mloc) mloc)
    (~~)
    (symmLayout' (with & slHSep .~ 4 & slVSep .~ 4) sampleT7')
  # centerXY

dia = hcat' (with & sep .~ 2)
   [ pointedTree
   , text "≅" # scale 2
   , xTreePair
   ]
   # frame 0.5
   # lwO 0.7
    \end{diagram}
    \caption{Species pointing}
    \label{fig:pointing}
  \end{figure}

  As is also illustrated in \pref{fig:pointing}, pointing can also be
  expressed in terms of differentiation, \[ \pt F \iso \X \cdot F'. \]

Similar laws hold for pointing as for differentiation; they are left
for the reader to discover.

\later{Is there more to say about pointing?}

\subsection{Higher derivatives}
\label{sec:higher-derivatives}

\citet[\Sect 8.11]{aguiar2010monoidal} describe a generalization of
species derivatives to ``higher derivatives''.  The idea of higher
derivatives in the context of functions of a single variable should be
familiar: the usual derivative is the \emph{first} derivative, and by
iterating this operation, one obtains notions of the second, third,
\dots derivatives.  More abstractly, we generalize from a single
notion of ``derivative'', $f'$, to a whole family of higher
derivatives $f^{(n)}$, parameterized by a \emph{natural number} $n$.

Note that taking the derivative of a polynomial reduces the degree of
all its terms by one.  More generally, the $n$th derivative reduces
the degrees by $n$.  According to the correspondence between species
and generating functions, the \emph{degrees} of terms in a generating
function correspond to the \emph{sizes} of label sets.  Recall that
the general principle of the passage from generating functions to
species is to replace natural number sizes by finite sets of labels
having those sizes.  Accordingly, just as higher derivatives of
generating functions are parameterized by a natural number which acts
on the degree, higher derivatives of species are parameterized by
a finite set which acts on the labels.

\begin{defn} \label{defn:higher-deriv}
  For a species $F$ and finite set $K$, the $K$-derivative of $F$ is
  defined by \[ \hder K F\ L = F\ (K \uplus L). \]
\end{defn}
As should be clear from the above discussion, the exponential
generating function corresponding to the $K$-derivative of $F$ is \[
(\hder K F)(x) = F^{(\size K)}(x), \] \ie the $(\size K)$-th
derivative of $F$. Note that we recover the simple derivative of $F$
by setting $K = \singleton$. Note also that $\hder {\varnothing} F = F$.

An $\hder K F$-shape with labels $L$ is an $F$-shape populated by both
$L$ \emph{and} $K$.  The occurrences of labels from $K$ can be thought
of as ``$K$-indexed holes'', since they do not contribute to the size.
For example, an ``$\hder K F$-shape of size $3$'' consists of an
$F$-shape with three labels that ``count'' towards the size, as well
as one ``hole'' for each element of $K$.
\pref{fig:higher-derivative-example} illustrates a $\hder K
\Bin$-shape of size $3$, where $K = \{a,b,c,d,e\}$.
\begin{figure}
  \centering
  \begin{diagram}[width=150]
import           Data.Char                      (chr)
import           Data.Tree
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

sampleT7' :: Tree (Either Int Char)
sampleT7' = fmap (\n -> if n > 2
                           then Right (chr (n + 94))
                           else Left n) sampleT7

derTree =
  renderTree
    (either mloc khole)
    (~~)
    (symmLayout' (with & slHSep .~ 4 & slVSep .~ 4) sampleT7')

khole c
  = text [c] # fc (colors !! 2)
  <>
    circle 0.8
  # lc (colors !! 2)
  # fc white
  # lwO 1.4
  # dashingL [0.15,0.15] 0

dia = derTree
   # frame 0.5
   # lwO 0.7
  \end{diagram}
  \caption{An example $\hder K \Bin$-shape}
  \label{fig:higher-derivative-example}
\end{figure}

Higher derivatives generalize easily to any functor category $\fc \Lab
\Str$ where $(\Lab, \oplus, I)$ is monoidal; we simply define \[ \hder
K F\ L \defeq F\ (K \oplus L). \]

\subsection{Internal Hom for partitional and arithmetic product}
\label{sec:internal-Hom-pprod-aprod}

As promised, we now return to consider the existence of an internal
Hom functor corresponding to partitional product.  We are looking for
some \[ \phom - - : \Spe^\op \times \Spe \to \Spe \] for
which \begin{equation} \label{eq:internal-Hom-pprod-adj}
(\hom[\Spe]{F \cdot G}{H}) \iso (\hom[\Spe]{F}{(\phom G H)}). \end{equation}
Intuitively, this is just like currying---although there are labels to
contend with which make things more interesting.

Recall that an $(F \cdot G)$-shape on $L$ is a partition $L_1 \uplus
L_2 = L$ together with shapes from $F\ L_1$ and $G\ L_2$.  Another way
of saying this is that an $(F \cdot G)$-shape consists of an $F$-shape
and a $G$-shape on two different sets of labels, whose disjoint union
constitutes the label set for the entire product shape.  Thus, a
morphism out of $F \cdot G$ should be a morphism out of $F$, which
produces another morphism that expects a $G$ and produces an $H$ on
the disjoint union of the label sets from the $F$- and $G$-shapes.

This can be formalized using the notion of higher derivatives
developed in the previous subsection. In particular, define $\phom -
-$ by \[ (\phom G H)\ L \defeq \hom[\Spe]{G}{\hder L H}. \]  That is,
a $(\phom G H)$-shape with labels taken from $L$ is a species
morphism, \ie a natural, label-preserving map, from $G$ to the
$L$-derivative of $H$.  This definition is worth rereading a few times
since it mixes levels in an initially surprising way---the
\emph{shapes} of the species $\phom G H$ are \emph{species morphisms}
between other species.  However, this should not ultimately be too
surprising to anyone used to the idea of higher-order functions; it
corresponds to the idea that functions can output other functions.

Thus, a $(\phom G H)$-shape with labels from $L$ is a natural function
that takes a $G$-shape as input and produces an $H$-shape which uses
the disjoint union of $L$ and the labels from $G$.  This is precisely
what is needed to effectively curry a species morphism out of a
product while properly keeping track of the labels, as illustrated in
\pref{fig:internal-Hom-pprod-example}.  The top row of the diagram
illustrates a particular instance of a species morphism from $\List
\cdot \Bin$ to $\List$.  The bottom row shows the ``curried'' form,
with a species morphism that sends a list to another species morphism,
which in turn sends a tree to a higher derivative of a list,
containing holes corresponding to the original list.

\begin{figure}
  \centering
  \begin{diagram}[width=300]
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams
import           Structures                     (pair)

t = BNode 2 (leaf 1) (BNode 0 (leaf 3) Empty)
l = ['b','a']

r = [Left 3, Left 1, Right 'a', Left 0, Right 'b', Left 2]

mloc2 c = text [c] <> circle 0.8 # fc (colors !! 2)

ld = drawList' mloc2 l
td = drawBinTree' (with & slHSep .~ 4 & slVSep .~ 3) (fmap mloc t)
rd = drawList' (either mloc mloc2) r

lhs = fun (pair ld td) rd

rhs = fun ld (enRect' 1 (fun td rd))

dia =
  vcat' (with & sep .~ 2)
  [ lhs # centerX
  , text "≅" # scale 2
  , rhs # centerX
  ]
  # frame 1
  # lwO 0.7
  \end{diagram}
  \caption{``Currying'' for partitional product of species}
  \label{fig:internal-Hom-pprod-example}
\end{figure}

Formally, we have the adjunction \eqref{eq:internal-Hom-pprod-adj}.
The same result appears in \citet{kelly2005operads} in a slightly
different guise.

This result hints at a close relationship between partitional product
and higher derivatives.  In particular, both are defined using the
\emph{same} monoidal structure on $\B$ (the one corresponding to
disjoint union of finite sets), and this gives rise to the fundamental
Leibniz-like law relating the two, \[ \hder L {(F \cdot G)} = \sum_{J
  \uplus K = L} \hder J F \cdot \hder K G. \] Setting $L = \singleton$
yields the familiar product rule for differentiation, \[ (F \cdot G)'
= F' \cdot G + F \cdot G', \] since there are only two possibilities
for $J$ and $K$ given $J \uplus K = \singleton$.  This generalizes to
functor categories other than $\fc \B \Set$: any functor category
which supports a Day convolution product also has a corresponding
notion of higher derivatives, and a corresponding Leibniz law.

This also suggests considering an alternate sort of higher derivative,
based on the other monoidal structure on $\B$ (corresponding to
Cartesian product of finite sets), and thus related to arithmetic
product rather than partitional product.  In particular, we define the
\term{arithmetic derivative} by \[ \ader K F\ L = F\ (K \times L). \]
We have \[ (\hom[\Spe]{F \aprod G}{H}) \iso (\hom[\Spe]{F}{(\ahom G
  H)}) \] where \[ (\ahom G H) \defeq (\hom[\Spe] {G}{\ader L H}). \]
This is a bit harder to visualize, but works on a similar principle to
higher derivative for partitional product.  The problem, from a
visualization point of view, is that no specific labels correspond to
``holes''; an $\ader K F$-shape with labels taken from $L$ actually
has $(\size K)(\size L)$ labels, with an entire $K$-indexed set of
labels corresponding to each element of $L$.
\pref{fig:internal-Hom-aprod-example} illustrates the adjunction: a
natural, label-preserving map from an arithmetic product $F \aprod G$
to some other species (here a cycle) corresponds to a nested map that
takes each of $F$ and $G$ in turn and then produces a species on the
product of their labels.

\begin{figure}
  \centering
  \begin{diagram}[width=300]
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

grays  = map (\k -> blend k black white) [0, 0.2, 0.8, 1, 0.5]
shapes = [circle 0.2, triangle 0.4, square 0.4]

theTree = tree3 (\n -> mkLeaf (circle 0.4 # fc (grays !! n)) n)

theList r = list2 (\n -> (mkLeaf ((shapes !! n) # rotateBy (-r) <> circle 0.4) n)) # rotateBy r

grid = vcat' (with & sep .~ 0.5)
  [ theTree # translateX 3.4
  , hcat' (with & sep .~ 0.5)
    [ theList (3/4)
    , theGrid
    ]
  ]
  where

shapeGrid =
  [ [ (shapes !! i) # fc (grays !! j)
    || j <- [1,0,3,2,4]
    ]
  || i <- [0..2]
  ]

theGrid :: Diagram B R2
theGrid = vcat . map hcat $ (map . map) (<> square 1) shapeGrid

tree3 nd
  = maybe mempty (renderTree nd (~~))
  . uniqueXLayout 1 1
  $ sampleBTree5

list2 nd = hcat' (with & sep .~ 1 & catMethod .~ Distrib)
  (map nd [0 :: Int .. 2])
  <>
  hrule 2 # alignL
  where
    aSty = with & arrowHead .~ noHead

theCycle = cyc' (map (scale 2) $ concat shapeGrid) 5  -- $

lhs = fun (grid # scale 2) theCycle

rhs = fun (theList 0 # scale 2) (enRect' 1 (fun (theTree # scale 2) theCycle))

dia =
  vcat' (with & sep .~ 2)
  [ lhs # centerX
  , text "≅" # scale 2
  , rhs # centerX
  ]
  # frame 1
  # lwO 0.7
  \end{diagram}
  \caption{``Currying'' for arithmetic product of species}
  \label{fig:internal-Hom-aprod-example}
\end{figure}

If $F(x) = \sum_{n \geq 0} f_n \frac{x^n}{n!}$, then \[ \ader K F(x) =
\sum_{n \geq 0} f_{kn} \frac{x^n}{n!}, \] where $k = \size K$; I do
not know whether there is a nice way to express this transformation on
generating functions.

\section{Regular, molecular and atomic species}
\label{sec:molecular-atomic}

We now consider the three related notions of \term{regular},
\term{molecular}, and \term{atomic} species.  \term{Regular} species,
roughly speaking, are those that correspond to algebraic data types in
Haskell or OCaml.  A first characterization is as follows:
\begin{defn} \label{defn:regular-closed}
  The class of \term{regular} species consists of the smallest class
  containing $\Zero$, $\One$, and $\X$, and closed under (countable)
  sums and products.
\end{defn}
There are a few apparent differences between regular species and
algebraic data types.  First, programming languages do not actually
allow \emph{infinite} sums or products.  For example, the species \[
\X^2 + \X^3 + \X^5 + \X^7 + \X^{11} + \dots \] of prime-length lists
is a well-defined regular species, but is not expressible as, say, a
data type in Haskell\footnote{At least not in Haskell 2010.}.  Second,
Haskell and OCaml also allow recursive algebraic data types.  However,
this is not a real difference: the class of regular species is also
closed under least fixed points (any implicit recursive definition of
a species can in theory be unfolded into an infinite sum or product).
Essentially, recursion in algebraic data types can be seen as a tool
that allows \emph{some} infinite sums and products to be encoded via
finite expressions.

However, there is a more abstract characterization of regular species
which does a better job of capturing their essence.  We first define
the \term{symmetries} of a structure. Recall that $\S_n$ denotes the
\term{symmetric group} of permutations on $n$ elements under
composition.

\begin{defn}
  A permutation $\sigma \in \S_n$ is a \term{symmetry} of an
  $F$-shape $f \in F\ L$ if and only if $\sigma$ fixes $f$,
  that is, $F\ \sigma\ f = f$.
\end{defn}

\begin{ex}
  The $\Cyc$-shape in the upper left of \pref{fig:cyc-symmetries} has
  the cyclic permutation $(01234)$ as a symmetry, because applying it
  to the labels results in the same cycle (in the upper right).  On
  the other hand, $(12)$ is not a symmetry; it results in the cycle on
  the lower left, which is not the same as the original cycle.
\begin{figure}[htp]
  \centering
  \begin{diagram}[width=300]
import           SpeciesDiagrams

cyc1 = cyc' (map labT [0..4]) 1
cyc2 = cyc' (map labT ([1..4]++ [0])) 1
cyc3 = cyc' (map labT [0,2,1,3,4]) 1

dia =
  vcat' (with & sep .~ 0.5)
  [ hcat' (with & sep .~ 0.5)
    [ cyc1
    , text "=" # scale 0.8 <> phantom (square 1 :: D R2)
    , cyc2
    ]
  , (text "≠" # scale 0.8 <> phantom (square 1 :: D R2)) # rotateBy (-1/4)
  , cyc3
  ]
  # frame 0.5
  # lwO 0.7
  \end{diagram}
  \caption{A symmetry and a non-symmetry of a $\Cyc$-shape}
  \label{fig:cyc-symmetries}
\end{figure}
\end{ex}

\begin{ex}
  An $\List$-shape has no nontrivial symmetries: applying any
  permutation other than the identity to a linear order results in a
  different linear order.
\end{ex}

\begin{ex}
  An $\Bag$-shape has all possible symmetries: applying any
  permutation to the labels in a set results in the same set.
\end{ex}

We can now state the more abstract definition of regular species; this
definition and \pref{defn:regular-closed} turn out to be equivalent.
\begin{defn}
  A species $F$ is \term{regular} if every $F$-shape has the identity
  permutation as its only symmetry. Such shapes are also called
  regular.
\end{defn}

\begin{ex}
  Regular species include $\Zero$, $\One$, $\X$, linear orders
  ($\List$), rooted binary trees ($\Bin$), and rose trees ($\Rose$).
  Non-regular species include sets ($\Bag$), cycles ($\Cyc$), and any
  sum or product of a non-regular species with any other species.
\end{ex}

\begin{rem}
  According to this definition, in addition to least fixed points,
  regular species are also closed under Cartesian and arithmetic
  product, since the Cartesian or arithmetic product of two regular
  shapes is also regular.  That is, Cartesian and arithmetic product
  cannot introduce any symmetries if none are present. Given the
  previous definition, this means that if $F$ and $G$ are two species
  expressed entirely in terms of $\One$, $\X$, sum, and partitional
  product, the Cartesian or arithmetic products of $F$ and $G$ are
  both themselves isomorphic to some species expressed using only
  those operations, without any mention of Cartesian or arithmetic
  product.  This is certainly far from obvious. \later{give an example
    of doing the translation}

  This definition also shows why regular species can be characterized
  as those for which $F(x) = \unl F(x)$: with no symmetries, each
  $F$-form of size $n$ corresponds to $n!$ distinct labelled shapes.
  Hence \[ F(x) = \sum_{n \geq 0} f_n \frac{x^n}{n!} = \sum_{n \geq 0}
  \unl{f_n} n! \frac{x^n}{n!} = \sum_{n \geq 0} \unl{f_n} x^n = \unl
  F(x). \]
\end{rem}

That species built from $\Zero$, $\One$, $\X$, sum, product, and fixed
point have no symmetries is not hard to see intuitively; less obvious
is the fact that up to isomorphism, every species with no symmetries
can be expressed in this way.  To understand why this is so, we turn
to molecular species.

\begin{defn}
  A species \F\ is \term{molecular} if there is only a single
  $F$-form, that is, all $F$-shapes are related by relabelling.
\end{defn}
\begin{ex}
The species $\X^2$ of ordered pairs is molecular, since
any two ordered pairs are related by relabelling.
\end{ex}
\begin{ex}
  On the other hand, the species $\List$ of linear orderings is not
  molecular, since list structures of different lengths are
  fundamentally non-isomorphic.
\end{ex}

Any two shapes with different numbers of labels are unrelated by
relabelling.  Thus, any molecular species $M$ necessarily has a
\term{size}, \ie some $n \in \N$ such that all $M$-shapes have size
$n$.  In other words, $M \iso M_n$ (where $M_n$ is the restriction of
$M$ to cardinality $n$; see \pref{sec:cardinality-restr}).

Clearly, any species of the form $F + G$ is not molecular (as long as
$F$ and $G$ are not $\Zero$), since the set of $(F+G)$-forms consists
of the disjoint union of the sets of $F$-forms and $G$-forms.  It
turns out that the converse is true as well:
\begin{prop}[\citet{yeh1985combinatorial,yeh-k-species}]
  The molecular species are precisely those that cannot be decomposed
  as the sum of two nonzero species.
\end{prop}

Molecular species can be characterized more deeply yet, via
\term{quotient species}. Recall first the definition of a group
action:

\begin{defn}
  An \term{action} of a group $G$ on a set $S$ is a function \[ - \act
  - : G \times S \to S \] such that, for all $g,h \in G$ and $s \in S$,
  \begin{itemize}
  \item $\id \act s = s$ and
  \item $g \act (h \act s) = (gh) \act s$.
  \end{itemize}
\end{defn}

\begin{rem}
  Note that this is identical to the definition of a monoid action
  \citep{yorgey2012monoids}; the only difference is that $G$ has
  inverses, but no special laws are needed to deal with the
  interaction of inverses with the action.

  If the action function is curried, $G \to (S \to S)$, then the laws
  state that a group action must be a group homomorphism from $G$ into
  the symmetric group of bijections on $S$.  Intuitively, a group
  action can be thought of as describing symmetries of the set $S$.
\end{rem}

\begin{defn}
  Let $H$ be a group and $F$ a species. $H$ is said to \term{act
    naturally} on $F$ if there is a family of group actions \[ \rho_L
  : H \times F\ L \to F\ L \] such that the following diagram
  commutes for all $\sigma : L \bij K$: \[ \xymatrix{ H \times F\ L
    \ar[r]^-{\rho_L} \ar[d]_{\id \times F\ \sigma} & F\ L \ar[d]^{F\
      \sigma} \\ H \times F\ K \ar[r]_-{\rho_K} & F\ K} \]
\end{defn}

\begin{ex}
  Intuitively, $H$ acts naturally on $F$ if its action does not depend
  on the particular identity of the labels---that is, if it commutes
  with relabelling.  For example, consider the species $\List_5$, of
  linear orders on exactly 5 labels, and the cyclic group $\Z_5 = \{0,
  \dots, 4\}$ under addition modulo $5$.  There is an action of $\Z_5$
  on $\List_5$, where $n \in \Z_5$ sends the list $a_0, \dots, a_4$ to
  the list $a_n, \dots, a_{n+4}$ (where the indices are taken modulo
  $5$).  In other words, $n \in \Z_5$ ``rotates'' the list $n$ places
  to the left.  It is clear that this is a group action (rotating a
  list by $0$ places is indeed the identity; rotating by $m$ and then
  by $n$ is the same as rotating by $m + n$).  It is also natural: the
  action does not depend on the identity of the labels, and is fully
  compatible with relabelling.
\end{ex}

\begin{ex}
  More generally, by Cayley's theorem, any group of order $n$ is
  isomorphic to a group of permutations, and thus has a natural action
  on $\List_n \iso \X^n$, given by permuting the list elements.
\end{ex}

\begin{ex}
  $\Z_2$ has an action on $\List$ (the species of linear orders of
  \emph{any} length) whereby the non-identity element acts on a linear
  order by reversing it.
\end{ex}

\begin{ex}
  $\Z_2$ also acts on $\List_{\geq 2}$ by swapping the first two
  elements, and leaving the rest alone.
\end{ex}

\begin{defn}[Quotient species \citep{labelle1985quelques}]
  Let $F$ be a species and let $H$ act naturally on $F$.  Then define
  the \term{quotient species} $F/H$ as the species which sends the
  finite set of labels $L$ to the set of orbits of $F\ L$ under the action of
  $H$.

  Put another way, for $f_1, f_2 \in F\ L$, define $f_1 \eqrel_H f_2$ if there
  is some $h \in H$ such that $h \act f_1 = f_2$; this defines an
  equivalence relation on $F\ L$, and we define $(F/H)\ L$ to be the
  set of equivalence classes under this equivalence relation.

  For a given $\sigma : L \bij K$, we define $(F/H)\ \sigma : (F/H)\ L
  \to (F/H)\ K$ by \[ F\ \sigma\ [f] \defeq [F\ \sigma\ f]. \] For
  this to be well-defined, we must show that if $f_1 \eqrel_H f_2$ then $F\
  \sigma\ f_1 \eqrel_H F\ \sigma\ f_2$.  This follows from the naturality
  of the action of $H$: if $f_1 \eqrel_H f_2$, that is, there is some $h
  \in H$ such that $h \act f_1 = f_2$, then $h \act (F\ \sigma\ f_1) =
  F\ \sigma\ (h \act f_1) = F\ \sigma\ f_2$, that is, $F\ \sigma\ f_1
  \eqrel_H F\ \sigma\ f_2$.  It is also easy to see that $F/H$ inherits
  the functoriality of $F$.
\end{defn}

\begin{ex}
  Consider again the action of $\Z_5$ on $\List_5$ described
  previously. Each orbit under the action of $\Z_5$ contains five
  elements: all the possible cyclic rotations of a given linear order.
  In fact, $\List_5 / \Z_5$ is isomorphic to $\Cyc_5$, the species of
  size-$5$ cycles. Each equivalence class of five lists is sent to the
  unique cycle which results from ``gluing'' the beginning and end of
  each list together; conversely, each cycle is sent to the
  equivalence class consisting of all possible ways of cutting the
  cycle to obtain a list (\pref{fig:iso-list-quot-cyc}).

  \begin{figure}
    \centering
    \begin{diagram}[width=300]
import           Data.List                      (tails)
import           SpeciesDiagrams

baseList = [1,3,4,0,2]

lists = map (take 5) . take 5 . tails . cycle $ baseList

listCycles = enclose 0.5 0.5 $ vcat' (with & sep .~ 0.5) (map (drawList' labT) lists)

theCycle = cyc' (map labT baseList) 1

iff = arrow' (with & arrowTail .~ dart') 2

dia = hcat' (with & sep .~ 1) [listCycles, iff, theCycle]
  # frame 0.5
  # lwO 0.7
    \end{diagram}
    \caption{Isomorphism between $\List_5 / \Z_5$ and $\Cyc_5$}
    \label{fig:iso-list-quot-cyc}
  \end{figure}
\end{ex}

\begin{ex}
  Considering the reversing action of $\Z_2$ on $\List$, shapes of the
  quotient $\List / \Z_2$ consist of (unordered) pairs of lists which
  are the reverse of each other.  This can be thought of as the
  species of ``unoriented lists'' (sometimes called the species of
  \term{chains}).
\end{ex}

\begin{ex}
  Considering the action of $\Z_2$ on $\List_{\geq 2}$ which swaps the
  first two elements, the quotient $\List_{\geq 2} / \Z_2$ is
  isomorphic to the species $\Bag_2 \cdot \List$
  (\pref{fig:iso-l2z2-e2l}).

  \begin{figure}
    \centering
    \begin{diagram}[width=350]
import           Data.List                      (tails)
import           SpeciesDiagrams
import           Structures                     (pair)

baseList :: [Int]
baseList = [1,3,4,0,2]

swap2 :: [Int] -> [Int]
swap2 (x:(y:zs)) = (y:x:zs)   -- Need the extra parens as workaround
                              -- for haskell-src-exts pretty-printing bug (?)

lists :: [[Int]]
lists = [baseList, swap2 baseList]

equivClass = enclose 0.5 0.5 $ vcat' (with & sep .~ 0.5) (map (drawList' labT) lists) -- $

e2l = pair (cat' (3 ^& 1) (with & sep .~ 0.5) (map labT (take 2 baseList))) (drawList' labT (drop 2 baseList))

iff = arrow' (with & arrowTail .~ dart') 2

dia = hcat' (with & sep .~ 1) [equivClass, iff, e2l]
  # frame 0.5
  # lwO 0.7
    \end{diagram}
    \caption{Isomorphism between $\List_{\geq 2} / \Z_2$ and $E_2 \cdot \List$}
    \label{fig:iso-l2z2-e2l}
  \end{figure}
\end{ex}

We can now state the following beautiful result:

\begin{prop}[\citet{bll}]
  Every molecular species is isomorphic to $\X^n / H$ for some natural
  number $n$ and some subgroup $H$ of the symmetric group $\S_n$.
  Moreover, $\X^n / G$ and $\X^n / H$ are isomorphic if and only if
  $G$ and $H$ are conjugate (that is, if there exists some $\varphi
  \in \S_n$ such that $G = \varphi H \varphi^{-1}$).
\end{prop}

In particular, this means that, up to isomorphism, molecular species
of size $n$ are in one-to-one correspondence with conjugacy classes of
subgroups of $\S_n$.  This gives a complete classification of
molecular species.  For example, it is not hard to verify that there
are four conjugacy classes of subgroups of $\S_3$, yielding the four
molecular species illustrated in \pref{fig:molec-three}.  The leftmost
is $\X^3$, corresponding to the trivial group.  The second is $\X
\cdot \Bag_2$, corresponding to the subgroups of $\S_3$ containing
only a single swap.  The third is $\Cyc_3$, corresponding to $\Z_3$.
The last is $\Bag_3$, corresponding to $\S_3$ itself.

\begin{figure}
  \centering
  \begin{diagram}[width=300]
import           SpeciesDiagrams
import           Structures                     (pair)

dot = circle 0.3 # fc black

x3 = drawList' (const dot) [(),(),()]
c3 = cyc' (replicate 3 dot) 0.8
e3 = position (zip (triangle 1) (repeat dot))
xe2 = pair dot (dot === strutY 0.5 === dot)

dia = hcat' (with & sep .~ 1) [x3, xe2, c3, e3]
  # frame 0.5
  # lwO 0.7
  \end{diagram}
  \caption{The four molecular species of size $3$}
  \label{fig:molec-three}
\end{figure}

This can in fact be extended to a classification of all species: up to
isomorphism, every species has a unique decomposition as a sum of
molecular species. As a very simple example, the molecular
decomposition of $\List$ is \[ \List = \One + \X + \X^2 + \X^3 +
\dots. \] \citet[p. 141]{bll} give a more complex example: \[ \Arbor =
\X + \X^2 + (\X^3 + \X \cdot \Bag_2) + (2\X^4 + \X^2 \cdot \Bag_2 + \X
\cdot \Bag_3) + \dots \]

\begin{rem}
  We can now see why the two definitions of regular species given
  previously are equivalent. Any regular species must be isomorphic to
  a sum of regular \mbox{molecular} species; but regular molecular species
  must be of the form $\X^n$.  Hence, up to isomorphism, regular
  species are always of the form $\sum_{n \geq 0} a_n \X^n$ with $a_n
  \in \N$.
\end{rem}

The story does not end here, however; molecular species can be
decomposed yet further.

\begin{defn}
  An \term{atomic} species $F \neq \One$ is one which is
  indecomposable under partitional product. That is, $F$ is atomic if
  $F = G \cdot H$ implies $G = \One$ or $H = \One$.
\end{defn}

\begin{thm}[\citet{yeh1985combinatorial}]
  Every molecular species $M$ can be uniquely decomposed as a product
  of atomic species \[ M = A_1^{n_1} \cdot A_2^{n_2} \dots
  A_k^{n_k}.\]
\end{thm}

\begin{rem}
  Of course ``unique'' here means ``unique up to isomorphism'', which
  includes reordering of the factors.
\end{rem}

\begin{ex}
  Of the four molecular species of size $3$ shown in
  \pref{fig:molec-three}, only the last two ($\Cyc_3$ and $\Bag_3$)
  are atomic.  The first two, $\X^3$ and $\X \cdot \Bag_2$, decompose
  as the product of three and two atomic species, respectively.
\end{ex}

\section{Species eliminators}
\label{sec:elim-species}

With the molecular and atomic decompositions of species under our
belt, we now turn to \term{eliminators} for species.  Generally
speaking, this is not of much interest to combinatorialists, but it will
play an important role in using species as a basis for data types, to
be explored in the next chapter.

The idea is to characterize outgoing species morphisms.  That is, for
a given species $F$, what can one say about species morphisms $\hom F
G$ for arbitrary species $G$?

\paragraph{Zero}

Since $\Zero\ L = \varnothing$ for all label sets $L$, there is only a
single species morphism $\hom \Zero G$ for any species $G$, namely, the
one which consists of the empty function at every size.

\paragraph{One}

There is only a single $\One$-shape, which has size zero, so a species
morphism $\hom \One G$ is equivalent to a specified inhabitant of $G\
\varnothing$.

\paragraph{Singleton}

By a similar argument, a species morphism $\hom \X G$ is equivalent to
a specified inhabitant of $G\ \singleton$.

\paragraph{Sum}

Intuitively, a species morphism $\hom{(F + G)} H$ should correspond to a
pair of morphisms $(\hom F H) \times (\hom G H)$, characterizing the
morphism in terms of the two possible cases.  Indeed, this follows
abstractly from the fact that contravariant Hom functors turn colimits
(here, a coproduct of species) into limits (here, the product in
$\Set$).  One may also calculate this result more directly by
expanding the species morphism as an end and manipulating morphisms in
$\Set$.

\paragraph{Products}

Species morphisms out of various types of product (Cartesian,
partitional, and arithmetic) have already been characterized in terms
of the internal Hom functors for these operations (see
\pref{sec:internal-Hom-cprod} and
\pref{sec:internal-Hom-pprod-aprod}):
\begin{gather*}
  (\hom {(F \times G)} H) \iso (\hom F {H^G}) \\
  (\hom {(F \cdot G)} H) \iso (\hom F {(\phom G H)}) \\
  (\hom {(F \aprod G)} H) \iso (\hom F {(\ahom G H)})
\end{gather*}
where $H^G$ is defined in \pref{sec:internal-Hom-cprod}, and $\phom G
H$ and $\ahom G H$ are defined in
\pref{sec:internal-Hom-pprod-aprod}. Note that in all three cases, one
may continue to recursively characterize the results in terms of
an eliminator for $F$. It ought to be the case that the internal Hom
functors can likewise be characterized in terms of an eliminator for
$G$, although the details are not yet clear to me.

\paragraph{Composition}

Species morphisms out of compositions have also already been
characterized in terms of an internal Hom functor, in
\pref{sec:internal-Hom-comp}: \[ (\hom {(F \comp G)} H) \iso (\hom F
{(\chom G H)}). \]

\paragraph{Molecular and atomic species}

We first consider molecular species, which by the discussion in the
previous section are equivalent to $\X^n / H$ for some $H \subgroup
\S_n$.  Unfolding definitions,
\begin{sproof}
  \stmt{\hom[\Spe]{\X^n / H}{G}}
  \reason{=}{definition}
  \stmt{\eend L \hom[\Set]{(\X^n/H)\ L}{G\ L}}
  \reason{=}{definition of $F / H$}
  \stmt{\eend L \hom[\Set]{(\X^n\ L) / \mathord{\eqrel_H}}{G\ L}}
\end{sproof}
where $f_1 \eqrel_H f_2$ iff there exists some $\sigma \in H$ such
that $\X^n\ \sigma\ f_1 = f_2$.  We now note that a function out of a
set of equivalence classes can be characterized as a function out of
the underlying set which respects the equivalence relation.  That is,
the last line of the computation above is isomorphic to \[ (f : \eend
L \hom[\Set]{\X^n\ L}{G\ L}) \times ((\sigma \in H) \to (f = f \comp
(\X^n\ \sigma)), \] \ie a species morphism $\hom {\X^n}{G}$ paired with a
proof that it respects the equivalence induced by $H$.  Note that the
same argument applies unchanged to the more general case of a quotient
species $F/H$.

\begin{ex}
  Consider species morphisms $\psi : \Cyc_5 \to \Bin_5$, from cycles
  to binary trees of size $5$. (You may want to pause to think about
  what such morphisms could look like.)

  As noted earlier, $\Cyc_5 \iso \X^5 / \Z_5$.  So any $\psi : \Cyc_5
  \to \Bin_5$ is isomorphic to a species morphism $\chi : \X^5 \to
  \Bin_5$ together with a proof that $\chi = \chi \comp (\X^5\
  \sigma)$ for all $\sigma \in \Z_5$.  By naturality of $\chi$, we
  have $\chi \comp (\X^5\ \sigma) = (\Bin_5\ \sigma) \comp \chi$, and
  hence $\chi = (\Bin_5\ \sigma) \comp \chi$.  However, we now see
  that this was something of a trick ``example'': since $\Bin_5$ is
  regular, $\Bin_5\ \sigma$ has no fixed points unless $\sigma = \id$,
  and $\Z_5$ certainly contains nontrivial permutations.  Therefore no
  such morphisms $\psi : \Cyc_5 \to \Bin_5$ can exist!
\end{ex}

\later{An actual example}
% \begin{ex}
%   \later{An actual example. $\Cyc_{2n} \to \Bag_2 \comp \Cyc$?  $\Cyc
%     \to \Cyc$?}
% \end{ex}

For molecular species which are not atomic, of course it is possible
to decompose them as a product, and characterize morphisms out of them
via currying.  So in some sense we are only ``forced'' to use the
above characterization of morphisms out of quotient species in the
case of atomic species.

\later{eliminators via Conor ``down'' operator}

