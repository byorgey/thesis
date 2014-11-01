%% -*- mode: LaTeX; compile-command: "mk" -*-

%include thesis.fmt

\chapter{Lifting monoids}
\label{chap:lifting-monoids}

\todo{Edit}

We now turn to a detailed and fully general construction which shows
how monoids (and many other structures of interest) can be lifted from
a category $\Str$ to a functor category $\fc \Lab \Str$.  The
high-level ideas of this construction seem to be ``folklore'', but I
have been unable to find any detailed published account, so it seemed
good to include some proofs here for completeness.  Unfortunately, the
proof presented here is still incomplete; as future work I hope to
completely understand the proof in detail.

We must first develop some technical machinery regarding functor
categories.  In particular, we show how to lift objects, functors, and
natural transformations based on the category $\Str$ into related
objects, functors, and natural transformations based on the functor
category $\Str^\Lab$.

\begin{lem} \label{lem:lift-object}
  An object $D \in \D$ lifts to an object (\ie a functor) $D^\C \in
  \D^\C$, defined as the constant functor $\Delta_D$.
\end{lem}

\begin{lem} \label{lem:lift-functor}
  Any functor $F : \D \to \E$ lifts to a functor $F^\C : \D^\C \to
  \E^\C$ given by postcomposition with $F$.  That is, $F^\C(G) = F
  \comp G = FG$, and $F^\C(\alpha) = F\alpha$.
\end{lem}

\begin{proof}
  $F\alpha$ denotes the ``right whiskering'' of $\alpha$ by $F$,
  \[ \xymatrix{ \C \rtwocell^G_H{\alpha} & \D \ar[r]^F & \E. } \]
  $F^\C$ preserves identities since
  \[ \xymatrix{ \C \ar[r]^G & \D \ar[r]^F & \E } \]
  can be seen as both $F \id_G$ and $\id_{FG}$, and it preserves
  composition since
  \[ \xymatrixrowsep{1pc}
     \xymatrix{ \C \ruppertwocell{\alpha} \rlowertwocell{\beta} \ar[r]
              & \D \ar[r]^F & \E }
     =
     \vcenter{
     \xymatrix{ \C \ruppertwocell{\alpha} \ar[r] & \D \ar[r]^F & \E \\
                \C \rlowertwocell{\beta} \ar[r] & \D \ar[r]_F & \E }
     }
  \] \later{Improve this picture with composition symbols?}
  by the interchange law for horizontal and vertical composition.
\end{proof}

Natural transformations lift in the same way:

\begin{lem} \label{lem:lift-nt} Given functors $F,G : \D \to \E$,
  any natural transformation $\alpha : \nt F G$ lifts to a natural
  transformation $\alpha^\C : \nt {F^\C} {G^\C} : \D^\C \to \E^\C$
  given by postcomposition with $\alpha$.  That is, the component of
  $\alpha^\C$ at $H :\C \to \D$ is $\alpha^\C_H = \alpha H$. Moreover,
  if $\alpha$ is an isomorphism then so is $\alpha^\C$.
\end{lem}

\begin{proof}
  Here $\alpha H$ denotes the ``left whiskering'' of $\alpha$ by $H$,
  \[ \xymatrix{ \C \ar[r]^H & \D \rtwocell^F_G{\alpha} & \E. } \]
  Note that $\alpha^\C_H$ should be a morphism $\mor {F^\C H} {G^\C
    H}$ in $\E^\C$, that is, a natural transformation $\nt {FH} {GH}$,
  so $\alpha H$ has the right type.  The naturality square for
  $\alpha^\C$ is
  \[ \xymatrix {
        FH \ar[r]^{\alpha^\C_H} \ar[d]_{F\beta}
      & GH \ar[d]^{G\beta}
     \\ FJ \ar[r]_{\alpha^\C_J}
      & GJ
     }
  \]
  which commutes by naturality of $\alpha$: at any particular $C \in
  \C$ the above diagram reduces to:
  \[ \xymatrix{
        FHC \ar[r]^{\alpha_{HC}} \ar[d]_{F\beta_C}
      & GHC \ar[d]^{G\beta_C}
     \\ FJC \ar[r]_{\alpha_{JC}}
      & GJC
     }
  \]
  If $\alpha$ is an isomorphism, then $(\alpha^{-1})^\C$ is the
  inverse of $\alpha^\C$: for any $H$, $\alpha^{-1}H \cdot \alpha H =
  (\alpha^{-1} \cdot \alpha) H = \id_{FH}$.
  \[ {\xymatrixcolsep{5pc} \xymatrix{ \C \ar[r]^H & \D
     \ruppertwocell^F{\mathrlap{\alpha}} \ar[r] \rlowertwocell_F{\mathrlap{\alpha^{-1}}} & \E
     }}
     =
     \xymatrix{ \C \ar[r]^H & \D \ar[r]^F & \E }
   \]
\end{proof}

Finally, we need to know that \emph{laws}---expressed as commutative
diagrams---also lift appropriately from $\D$ to $\D^\C$.  For example,
if we lift the functor and natural transformations defining a monoid
in $\D$, we need to know that the resulting lifted functor and lifted
natural transformations still define a valid monoid in $\D^\C$.

The first step is to understand how to appropriately encode laws as
categorical objects.  Consider a typical commutative diagram, such as
the following diagram expressing the coherence of the associator for a
monoidal category.  The parameters to all the instances of $\alpha$
have been written out explicitly, to make the subsequent discussion
clearer, although in common practice these would be left implicit.
\[ \xymatrix{ & ((A \oplus B) \oplus C) \oplus D
  \ar[dl]_{\alpha_{A,B,C} \oplus \id_D} \ar[dr]^{\alpha_{A \oplus
      B,C,D}} & \\ (A \oplus (B \oplus C)) \oplus D
  \ar[d]_{\alpha_{A,B \oplus C,D}} & & (A \oplus B) \oplus (C \oplus
  D) \ar[d]^{\alpha_{A,B,C \oplus D}} \\ A \oplus ((B \oplus C) \oplus
  D) \ar[rr]_{\id_A \oplus \alpha_{B,C,D}} & & A \oplus (B \oplus (C
  \oplus D)) } \] There are two important points to note.  The first
is that any commutative diagram has a particular \emph{shape} and can
be represented as a functor from an ``index category'' representing
the shape (in this case, a category having five objects and morphisms
forming a pentagon, along with the required composites) into the
category in which the diagram is supposed to live. Such a functor will
pick out certain objects and morphisms of the right ``shape'' in the
target category, and the functor laws will ensure that the target
diagram commutes in the same ways as the index category. (This much
should be familiar to anyone who has studied abstract limits and
colimits.)  The second point is that this diagram, like many such
diagrams, is really supposed to hold for \emph{all} objects $A$, $B$,
$C$, $D$.  So instead of thinking of this diagram as living in a
category $\C$, where the vertices of the diagram are objects of $\C$
and the edges are morphisms, we can think of it as living in $\fc
{\C^4} \C$, where the vertices are \emph{functors} $\C^4 \to \C$ (for
example, the top vertex is the functor which takes the quadruple of
objects $(A,B,C,D)$ and sends them to the object $((A \oplus B) \oplus
C) \oplus D$), and the edges are natural transformations.

All told, then, we can think of a typical diagram $D$ in $\C$ as a
functor $D : J \to (\fc {\C^A} \C)$, where $A$ is some (discrete)
category recording the arity of the diagram.

\begin{lem}
  Any diagram $D : J \to (\fc {\C^A} \C)$ in $\C$ lifts to a diagram
  $D^\D : J \to (\fc {(\C^\D)^A} {\C^\D})$ in $\C^\D$.
\end{lem}

\begin{proof}
  This amounts to implementing a higher-order function with the
  type \[ (J \to (A \to \C) \to \C) \to J \to (A \to \D \to \C) \to \D
  \to \C \] which can be easily done as follows: \[ \Phi\ D\ j\ g\ d =
  D\ j\ (\fun a {g\ a\ d}). \] Of course there are some technical
  conditions to check, but they all fall out easily.
\end{proof}

At this point there is a gap in the proof.  To know that this lifting
does the right thing, one must show that the lifted diagram defined
above is ``about'' (\ie has as its vertices and edges) the lifted
versions of the vertices and edges of the original diagram.  Even this
is still not quite enough; to really know that the lifted diagram
``says the same thing'' as the unlifted diagram, we need to show not
just that the vertices and edges of the lifted diagram are lifted
versions of the original diagram's vertices and edges, but that these
lifted vertices and edges are themselves composed of lifted versions
of the components of the originals. For example, we want to ensure
that the lifting of the example diagram shown above still expresses
coherence of the lifted associator with respect to the lifted tensor
product. It is not enough to have vertices like $(((A \oplus B) \oplus
C) \oplus D)^\D$; we must show this is the same as $((A^\D \oplus^\D
B^\D) \oplus^\D C^\D) \oplus^\D D^\D$, so that it says something about
the lifted tensor product $\oplus^\D$.

The basic idea would be to write down a formal syntax for the functors
and natural transformations that may constitute a diagram, and show
that the lifting of an expression is the same as the original
expression with its atomic elements each replaced by their lifting.

Assuming this result for now, we can go on to show how monoids lift
into a functor category.

\begin{thm} \label{thm:lift-monoid}
  Any monoidal structure $(\otimes, I, \alpha, \lambda, \rho)$ on a
  category $\Str$ lifts pointwise to a monoidal structure $(\otimes^\Lab,
  I^\Lab, \alpha^\Lab, \lambda^\Lab, \rho^\Lab)$ on the functor category
  $\fc \Lab \Str$.
\end{thm}

\begin{proof}
  Immediate from Propositions \ref{lem:lift-object},
  \ref{lem:lift-functor}, and \ref{lem:lift-nt}, and our assumed
  result that diagrams lift to diagrams which ``say the same thing''
  as the original, but say it ``about'' lifted things.
\end{proof}

In \pref{prop:lift-monoid-simple} it was claimed that this lifting
preserves products, coproducts, symmetry, and distributivity.  We can
already show that symmetry and distributivity are preserved:

\begin{prop}
  The lifting defined in \pref{thm:lift-monoid} preserves symmetry.
\end{prop}

\begin{proof}
  Symmetry is given by a natural isomorphism $\all {X Y} {X \otimes Y
    \equiv Y \otimes X}$. By our previous assumption, this lifts to a
  natural isomorphism $\all {F G} {F \otimes^\Lab G \equiv G
    \otimes^\Lab F}$.
\end{proof}

\begin{prop}
  The lifting defined in \pref{thm:lift-monoid} preserves
  distributivity.
\end{prop}

\begin{proof}
  In any category with all products and coproducts, there is a natural
  transformation $\all {X Y Z} {X \times Y + X \times Z \to X \times
    (Y + Z)}$, given by
  $\fork{\choice{\pi_1}{\pi_1}}{\choice{\pi_2}{\pi_2}}$.  The category
  is \term{distributive} if this is an isomorphism.  Again by our
  assumption about lifting, such an isomorphism lifts to another
  natural isomorphism \[ \all {F G H} {(F \times^\Lab G) +^\Lab (F
    \times^\Lab H) \to F \times^\Lab (G +^\Lab H)}. \]
\end{proof}

To show that products and coproducts are preserved requires first
showing that lifting preserves adjunctions.

\begin{lem} \label{lem:lift-adj}
  Let $F : \D \to \E$ and $G : \D \leftarrow \E$ be functors.  If $F
  \adj G$, then $F^\C \adj G^\C$.
\end{lem}

\begin{proof}
  Since $F \adj G$, assume we have $\gamma_{A,B} : \E(FA, B) \iso
  \D(A, GB)$.  To show $F^\C \adj G^\C$, we must define a natural
  isomorphism $\gamma^\C_{H,J} : \E^\C(F \comp H, J) \iso \D^\C(H, G
  \comp J)$.  Given $\phi \in \E^\C(FH,J)$, that is, $\phi : \nt {FH}
  J : \C \to \E$, and an object $C \in \C$, define \[
  \gamma^\C_{H,J}(\phi)_C = \gamma_{HC,JC}(\phi_C). \]  Note that
  $\gamma_{HC,JC} : \E(FHC,JC) \iso \D(HC,GJC)$, so it sends $\phi_C
  : FHC \to JC$ to a morphism $HC \to GJC$, as required.

  From the fact that $\gamma$ is an isomorphism it thus follows
  directly that $\gamma^\C$ is an isomorphism as well.  Naturality of
  $\gamma^\C$ also follows straightforwardly from naturality of
  $\gamma$. For a more detailed proof, see
  \citet[pp. 17--18]{hinze2012kan}.
\end{proof}

\begin{prop}
  The lifting defined in \pref{thm:lift-monoid} preserves coproducts
  and products.
\end{prop}

\begin{proof}
  Consider a category $\Str$ with coproducts, given by a bifunctor $+
  : \Str \times \Str \to \Str$.  Lifting yields a functor $+^\Lab :
  (\Str \times \Str)^\Lab \to \Str^\Lab$.  Note that $(\Str \times
  \Str)^\Lab \iso \Str^\Lab \times \Str^\Lab$, so we may consider
  $+^\Lab$ as a bifunctor $\Str^\Lab \times \Str^\Lab \to \Str^\Lab$.

  There is \latin{a priori} no guarantee that $+^\Lab$ has any special
  properties, but it turns out that $+^\Lab$ is a coproduct on
  $\Str^\Lab$, which we demonstrate as follows.  The key idea is that
  the property of being a coproduct can be described in terms of an
  adjunction: in particular, $+$ is a coproduct if and only if it is
  left adjoint to the diagonal functor $\Delta : \Str \to \Str \times
  \Str$.\footnote{Proving this standard fact takes a bit of work but
    mostly just involves unfolding definitions, and is left as a nice
    exercise for the interested reader.}  Since lifting preserves
  adjunctions (\pref{lem:lift-adj}), we must have $+^\Lab \adj
  \Delta^\Lab$. But note we have $\Delta^\Lab : \Str^\Lab \to (\Str
  \times \Str)^\Lab \iso \Str^\Lab \times \Str^\Lab$, with
  $\Delta^\Lab (F) = \Delta \comp F \iso (F,F)$, so in fact
  $\Delta^\Lab$ is the diagonal functor on $\Str^\Lab$.  Hence
  $+^\Lab$, being left adjoint to the diagonal functor, is indeed a
  coproduct on $\Str^\Lab$.

  Of course, this dualizes to products as well, which are
  characterized by being right adjoint to the diagonal functor.
\end{proof}


