%% -*- mode: LaTeX; compile-command: "mk" -*-

\chapter{Conclusion and future work}
\label{chap:conclusion}

This dissertation has laid the theoretical groundwork to pursue
applications of combinatorial species (and variants thereof) to
algebraic data types in functional programming languages. It is too
early to say with confidence what sorts of applications there might
be, though the future work laid out below hints at some ideas.

Two aspects of this work have turned out to be particularly surprising
and gratifying to me.  The first is the host of nontrivial issues that
arise when attempting to formalize species in a constructive type
theory---and the way that homotopy type theory is able to neatly
dispatch them all.  I hope I have successfully made the case that HoTT
is the right framework in which to carry out this work; in any case it
is a lot of fun to see such a recent and groundbreaking theory put to
productive work in a different area of mathematics (namely,
combinatorics).  The second gratifying aspect of this work is the way
that analytic functors neatly encapsulate the idea of labelled shapes
associated with a mapping from labels to data.  Indeed, Jacques and I
had the basic idea of associating shapes and mappings for a long time
before realizing that what we were thinking of were ``just'' analytic
functors.

Although this dissertation merely hints at practical applications, I
feel that building on the foundations of this work, practical
applications will not be far behind.  In general, there is no shortage
of future work!  This dissertation has just scratched the surface of
what is possible, and indeed, some of my initial conceptions of what
my thesis would contain seem to actually constitute a viable five- or
ten-year research program.  I mention here some of the most promising
avenues for continued work in this area.

\begin{itemize}
\item This dissertation discussed exponential and ordinary generating
  functions, but omitted \term{cycle index series}, which are a
  generalization of both (and which are necessary for computing, \eg,
  ogfs of compositions).  For that matter, even ogfs were not
  discussed much, but correspond to ``unlabelled'' structures, which
  may often be what one actually wants to work with.  My gut sense is
  that there is quite a lot more that could be said about
  computational interpretation of generating functions, and that this
  may have very practical applications, for example, in the enumeration
  and random generation of data structures.

\item As mentioned in the discussion of
  \pref{conj:linear-equipotence}, it seems promising to translate the
  theory of molecular and atomic species into homotopy type theory,
  ideally using Coq or Agda to formalize the development.  My sense is
  that this will shed additional light on the theory, and may have
  some practical applications as well.

\item It seems there is something interesting that could be said about
  recursively defined $(\fc \B \Set)$-species, where infinite families
  of same-size shapes are allowed.  Some of the criteria for the
  implicit species theorems presented in \pref{sec:recursive} work
  simply to prevent such infinite families, and hence are not needed
  in such a setting.  It would be interesting to explore minimal
  criteria for analogues of the implicit species theorems in more
  generalized settings.

\item Although the introduction mentions generic programming, the
  remainder of the dissertation has little to say on the topic, but
  there are certainly interesting connections to be made.  In a
  practical vein, using generic programming, it should be possible to
  create tools that allow algebraic data types to be manipulated via
  generic ``views'' as species.

% \item There is much more to explore with respect to $\BTSub$ and its
%   related notions of species. In particular, \later{finish this once
%     I've written more about it.}

\item It seems that there ought to be some sort of connection between
  species and linear logic.  In general, labels are ``treated
  linearly''; partitional product feels analogous to multiplicative
  conjunction, Cartesian product to additive conjunction, and species
  sum to additive disjunction.  This suggests looking for a species
  operation analogous to multiplicative disjunction, although I have
  not been able to make sense of such an operation\footnote{Much like
    multiplicative disjunction itself.}. It seems worthwhile to
  investigate the possibility of a real, deeper connection between
  species and linear logic.

\item \pref{sec:analytic-partial} considered a variant of $\analytic F
  A$ which ``removed the coend'', exposing the labels in the type: \[
  \LStr F L A \defeq (\iota L \to A) \times F\ L. \] It is still not
  clear, however, whether there is any benefit to being able to
  explicitly talk about the label type in this way.  Coming up with a
  more precise story about such ``exposed'' labelled structures---or
  showing conclusively why one does not want to work with them---would
  be an important next step.
\end{itemize}

\later{Say something to wrap up\dots  something about ``feels like a
  beginning rather than an ending''? How do you end a 200-page
  document without sounding hoky?}
