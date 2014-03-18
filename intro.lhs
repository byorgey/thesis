%% -*- mode: LaTeX; compile-command: "mk" -*-

%include polycode.fmt

\chapter{Introduction}
\label{chap:intro}

\todo{describe big ideas here}

\section{Homotopy type theory}
\label{sec:HoTT}

\todo{put intro to HoTT here}

Basics of type theory (copy from other paper).

Equality/paths.  Univalence.  Intuition: richer space of equalities.
We have Leibniz equality (transport) but transport may involve some
work.

Mere propositions, sets. Truncation. Recursion principle for
truncation, intuition.

\section{Category theory}
\label{sec:category-theory}

Make extensive use of category theory.  Assume basics (categories,
functors, natural transformations).

Groupoids.

Talk about connection between natural transformations and polymorphic
functions, specific ways it plays out in a dependent type
theory---e.g. can we assume parametricity for functions that abstract
over things classified by |*|? Cite Bernardy et al.

Monoidal categories.