%% -*- mode: LaTeX; compile-command: "mk" -*-
\documentclass[xcolor=svgnames,12pt]{beamer}

\newcommand{\pkg}[1]{\texttt{#1}}

\usepackage{haskell}

%include lhs2TeX-extra.fmt

\renewcommand{\onelinecomment}{\quad--- \itshape}
\renewcommand{\Varid}[1]{{\mathit{#1}}}

\newcommand{\pt}[1]{\ensuremath{#1^{\bullet}}}
\newcommand{\down}{\chi}

% \setbeamertemplate{footline}{\insertframenumber}

\setbeamertemplate{items}[circle]

\mode<presentation>
{
  \usetheme{default}                          % use a default (plain) theme

  \setbeamertemplate{navigation symbols}{}    % don't show navigation
                                              % buttons along the
                                              % bottom
  \setbeamerfont{normal text}{family=\sffamily}

  % XXX remove this before giving actual talk!
  % \setbeamertemplate{footline}[frame number]
  % {%
  %   \begin{beamercolorbox}{section in head/foot}
  %     \vskip2pt
  %     \hfill \insertframenumber
  %     \vskip2pt
  %   \end{beamercolorbox}
  % }

  \AtBeginSection[]
  {
    \begin{frame}<beamer>
      \frametitle{}
      \begin{center}
        {\Huge \insertsectionhead}
      \end{center}
    \end{frame}
  }
}

\defbeamertemplate*{title page}{customized}[1][]
{
  \vbox{}
  \vfill
  \begin{centering}
    \begin{beamercolorbox}[sep=8pt,center,#1]{title}
      \usebeamerfont{title}\inserttitle\par%
      \ifx\insertsubtitle\@@empty%
      \else%
        \vskip0.25em%
        {\usebeamerfont{subtitle}\usebeamercolor[fg]{subtitle}\insertsubtitle\par}%
      \fi%
    \end{beamercolorbox}%
    \vskip1em\par
    {\usebeamercolor[fg]{titlegraphic}\inserttitlegraphic\par}
    \vskip1em\par
    \begin{beamercolorbox}[sep=8pt,center,#1]{author}
      \usebeamerfont{author}\insertauthor
    \end{beamercolorbox}
    \begin{beamercolorbox}[sep=8pt,center,#1]{institute}
      \usebeamerfont{institute}\insertinstitute
    \end{beamercolorbox}
    \begin{beamercolorbox}[sep=8pt,center,#1]{date}
      \usebeamerfont{date}\insertdate
    \end{beamercolorbox}
  \end{centering}
  \vfill
}

% uncomment me to get 4 slides per page for printing
% \usepackage{pgfpages}
% \pgfpagesuselayout{4 on 1}[uspaper, border shrink=5mm]

% \setbeameroption{show only notes}

\usepackage[english]{babel}
\usepackage{graphicx}
\usepackage{ulem}
\usepackage{url}
\usepackage{fancyvrb}
\usepackage{amsmath}
\usepackage{amsthm}

\newtheorem{thm}{Theorem}

\usepackage[outputdir=diagrams]{diagrams-latex}
\graphicspath{{images/}}

\renewcommand{\emph}{\textbf}

\title{Combinatorial Species and Algebraic Data Types}
\date{Dissertation Proposal \\ March 2, 2013}
\author{Brent Yorgey}
\titlegraphic{}  % \includegraphics[width=2in]{foo}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\begin{frame}[fragile]
   \titlepage
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Outline}
  \begin{itemize}
  \item Algebraic data types
  \item Combinatorial species
  \item Species types
  \item The \pkg{species} library
  \item Timeline
  \end{itemize}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Algebraic data types}
\label{sec:ADTs}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Algebraic data types}

  \begin{center}
\includegraphics[width=1in]{ocaml-logo} \hspace{1in}
\includegraphics[width=1in]{haskell-logo}
  \end{center}

\begin{itemize}
\item Base types (|Int|, |Char|, \dots)
\item Unit type ( |Unit| )
\item Sum types (tagged union, |Either|)
\item Product types (tupling, |Pair|)
\item Recursion
\end{itemize}

AKA \emph{polynomial functors}.  Note: no arrow types!
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}
  Binary tree type:

%format Tree  = "\tycon{Tree}"
%format Empty = "\con{Empty}"
%format Node  = "\con{Node}"

XXX todo: picture here

  \begin{spec}
data Tree
  =  Empty
  |  Node Tree Int Tree
  \end{spec}

  \begin{spec}
type Tree = Either () (Tree, (Int, Tree))
  \end{spec}

\[ T = 1 + T \times |Int| \times T \]
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}
  A really fruitful idea!
  \begin{itemize}
  \item Initial algebra semantics, folds, ``origami'' programming
  \item Generic programming
  \item Connections to algebra and calculus (\emph{e.g.} zippers)
  \end{itemize}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section{Combinatorial species}
\label{sec:species}



\begin{frame}
  \emph{What are species, and what do they have to do with programming languages?}

  XXX picture

  A theory of \emph{labeled structures}
\end{frame}

\begin{frame}{Before species\dots}
  Collection of techniques for dealing with combinatorial
  classes.

  Connection with generating functions known (XXX cite EC, gfology -- note
  Herb Wilf)

  But all rather ad-hoc.
\end{frame}

\begin{frame}{Species!}
  Joyal, 198? XXX -- ``Une ???''
\end{frame}

\begin{frame}{Species and ADTs?}
  The connection is ``obvious''.

  \emph{A beautiful Answer in search of a Question.}
\end{frame}

\begin{frame}{Species definition}
  XXX definition
\end{frame}

\begin{frame}{Examples}
  XXX species examples
\end{frame}

\begin{frame}
  XXX Vennish diagram showing species, algebra of species, ADTs.
\end{frame}

\begin{frame}{Algebra of species}
  XXX the algebra of species
\end{frame}

\begin{frame}
  Presentation will be a contribution of my thesis.

  XXX picture of BLL -- not accessible, expensive
\end{frame}

\begin{frame}{Remaining work}
  XXX have begun with blog posts + proposal document
  \begin{itemize}
    \item $\mathbb{L}$-species
    \item Virtual species
    \item Molecular and atomic species
  \end{itemize}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section{Species types}
\label{sec:species-types}

\begin{frame}
  \emph{Can we use the theory of species as a foundational basis for
    container types?}
\end{frame}

\subsection{XXX relationship}
\label{sec:relationship}

\begin{frame}{Relationship of species to data types}
  XXX explain here.  From proposal.
\end{frame}

\subsection{Eliminators for species types}
\label{sec:elim}

\begin{frame}[fragile]{Symmetry}
  % Symmetric structure examples: cycles, bags, hierarchies,
  % heaps\dots
  \begin{center}
  \begin{diagram}[width=75]
import Species
dia = cyc [0..4] 1.2 # pad 1.1
  \end{diagram}
  % XXX vertically center, if time
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
dia = drawSpT t # pad 1.1
  \end{diagram}
  \bigskip

  \onslide<2>\dots how can we program with these?
  \end{center}
\end{frame}

\begin{frame}[fragile]{Eliminating symmetries?}
  \begin{center}
  \begin{diagram}[width=200]
import Species
dia = (cyc [0..4] 1.2 ||-|| elimArrow ||-|| (text "?" <> square 1 # lw 0)) # pad 1.1
  \end{diagram}
  \end{center}

  \onslide<2>Want: compiler guarantee that eliminators are oblivious
  to ``representation details''.
\end{frame}

\begin{frame}{Species decomposition}
    Every nonempty species is isomorphic to
    \begin{itemize}
    \item<+-> the unit species,
    \item<+-> a sum,
    \item<+-> a product,
    \item<+-> or an \emph{atomic} species $X^n/\mathcal{H}$
      \begin{itemize}
      \item<+-> (where $\mathcal{H}$ acts transitively on $\{0, \dots,
        n-1\}$).
      \end{itemize}
  \end{itemize}
\end{frame}

\begin{frame}
  So we can build eliminators in a type-directed way, using ``high
  school algebra'' laws for exponents:
  \begin{center}
    \begin{tabular}{ccc}
      $1[A] \to B$ & $\cong$ & $B$ \\
      \\
      $X[A] \to B$ & $\cong$ & $A \to B$ \\
      \\
      $(F+G)[A] \to B$ & $\cong$ & $(F[A] \to B) \times (G[A] \to B)$ \\
      \\
      $(F \cdot G)[A] \to B$ & $\cong$ & $F[A] \to (G[A] \to B)$ \\
      \onslide<2> & & \\
      $(X^n/\mathcal{H})[A] \to B$ & $\cong$ & $ ?$
    \end{tabular}
  \end{center}
\end{frame}

\begin{frame}{Eliminating symmetries}
  \begin{gather*}
    (X^n/\mathcal{H})[A] \to B \\
    \cong \\
    \Sigma f : X^n \to B. \Pi \sigma \in \mathcal{H}. f = f \circ \sigma
  \end{gather*}
\end{frame}

\section{Eliminators, take 2!}

\begin{frame}[fragile]{Poking and pointing}
  The \emph{derivative} $F'$ of $F$ represents $F$-structures with a
  hole.

  \begin{center}
  \begin{diagram}[width=100]
    import Species
    dia = drawSpT (nd 'F' (map lf [Leaf, Hole, Leaf, Leaf])) # pad 1.1
  \end{diagram}
  \end{center}

  The \emph{pointing} of $F$, $\pt{F} \triangleq X \cdot F'$,
  represents $F$-structures with a distinguished element.

  \begin{center}
  \begin{diagram}[width=100]
    import Species
    dia = drawSpT (nd 'F' (map lf [Leaf, Point, Leaf, Leaf])) # pad 1.1
  \end{diagram}
  \end{center}

  \onslide<2> Pointing \emph{breaks symmetry}.
\end{frame}

\begin{frame}[fragile]{Pointing}
  \begin{center}
  \begin{diagram}[width=250]
    import Species
    f   = drawSpT (nd 'F' (map lf [Leaf, Leaf, Leaf, Leaf])) # pad 1.1
    fpt = drawSpT (nd 'F' (map lf [Point, Leaf, Leaf, Leaf])) # pad 1.1

    dia = [f, elimArrow, fpt] # map centerY # foldr1 (||-||)
  \end{diagram}
  \end{center}

  \[ \pt{(-)} : F \to \pt{F} ? \]

  \begin{center}
  \onslide<2>\emph{Only} for polynomials!
  \end{center}
\end{frame}

\begin{frame}[fragile]{Pointing in context}
  \dots but Peter Hancock's ``cursor down'' operator is fine: \[ \down
  : F \to F \pt{F} \]

  \begin{diagram}[width=300]
    import Species
    c = Cyc [lab 0, lab 2, lab 3]
    d1 = draw c
    d2 = draw (down c)
    dia = (d1 ||-|| elimArrow ||-|| d2) # pad 1.05
  \end{diagram}
\end{frame}

\begin{frame}[fragile]{Eliminating with $\down$}
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
\end{frame}

\begin{frame}[fragile]{Other uses of $\down$}
  %% XXX 4  -- draw example of another thing "down" is useful for
%  Note $\down$ is useful for other things too. ``Map in context''.
%  e.g. cycles.
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
\end{frame}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section{The \pkg{species} library}
\label{sec:species-lib}

\begin{frame}
  \emph{XXX need a question here}
\end{frame}


-------------------------------------------------------------------------------
















%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% \begin{frame}
%   \begin{center}
%     \vspace{1em}
%     Joint work (in progress) with: \bigskip

%     \begin{tabular}{cc}
%     \includegraphics[height=1in]{jacques}
%     & \includegraphics[height=1in]{gershom} \\
%     Jacques Carette & Gershom Bazerman
%     \end{tabular}
%   \end{center}
% \end{frame}

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% \begin{frame}{Combinatorial species}
% \begin{center}
%     \onslide<2->{\vfill{\Large ?}\vfill}
%     \onslide<3>{For today: think ``container types'', \emph{i.e.} functors.}
% \end{center}
% \end{frame}

% %% Idea: use them as basis for programming.  First steps: eliminators.

% \begin{frame}[fragile]{Polynomial functors}
%   \begin{center}
%   \begin{tabular}{cl}
%     $1$ & unit\\
%     $X$ & identity \\
%     $F + G$ & sums \\
%     $F \cdot G$ & products
%   \end{tabular}
%   \end{center}

%   \begin{center}
%     \onslide<2-> \emph{e.g.} $1 + X$, $X^2$, \dots

%     \onslide<3> \vspace{1em} No symmetry!
%   \end{center}
% \end{frame}

% \begin{frame}[fragile]{Symmetry}
%   % Symmetric structure examples: cycles, bags, hierarchies,
%   % heaps\dots
%   \begin{center}
%   \begin{diagram}[width=75]
% import Species
% dia = cyc [0..4] 1.2 # pad 1.1
%   \end{diagram}
%   % XXX vertically center, if time
%   \begin{diagram}[width=60]
% import Species
% dia = ( roundedRect 2 1 0.2
%         <> (lab 0 |||||| strutX 0.3 |||||| lab 3)
%            # centerXY
%       )
%       # pad 1.1
%       # lw 0.02
%   \end{diagram}
%   \begin{diagram}[width=75]
% import Species
% import Data.Tree
% t   = Node Bag [lf (Lab 1), lf (Lab 2), Node Bag [lf (Lab 0), lf (Lab 3)]]
% dia = drawSpT t # pad 1.1
%   \end{diagram}
%   \bigskip

%   \onslide<2>\dots how can we program with these?
%   \end{center}
% \end{frame}

% \begin{frame}[fragile]{Eliminating symmetries?}
%   \begin{center}
%   \begin{diagram}[width=200]
% import Species
% dia = (cyc [0..4] 1.2 ||-|| elimArrow ||-|| (text "?" <> square 1 # lw 0)) # pad 1.1
%   \end{diagram}
%   \end{center}

%   \onslide<2>Want: compiler guarantee that eliminators are oblivious
%   to ``representation details''.
% \end{frame}

% \begin{frame}{Species decomposition}
%     Every nonempty species is isomorphic to
%     \begin{itemize}
%     \item<+-> the unit species,
%     \item<+-> a sum,
%     \item<+-> a product,
%     \item<+-> or an \emph{atomic} species $X^n/\mathcal{H}$
%       \begin{itemize}
%       \item<+-> (where $\mathcal{H}$ acts transitively on $\{0, \dots,
%         n-1\}$).
%       \end{itemize}
%   \end{itemize}
% \end{frame}

% \begin{frame}
%   So we can build eliminators in a type-directed way, using ``high
%   school algebra'' laws for exponents:
%   \begin{center}
%     \begin{tabular}{ccc}
%       $1[A] \to B$ & $\cong$ & $B$ \\
%       \\
%       $X[A] \to B$ & $\cong$ & $A \to B$ \\
%       \\
%       $(F+G)[A] \to B$ & $\cong$ & $(F[A] \to B) \times (G[A] \to B)$ \\
%       \\
%       $(F \cdot G)[A] \to B$ & $\cong$ & $F[A] \to (G[A] \to B)$ \\
%       \onslide<2> & & \\
%       $(X^n/\mathcal{H})[A] \to B$ & $\cong$ & $ ?$
%     \end{tabular}
%   \end{center}
% \end{frame}

% \begin{frame}{Eliminating symmetries}
%   \begin{gather*}
%     (X^n/\mathcal{H})[A] \to B \\
%     \cong \\
%     \Sigma f : X^n \to B. \Pi \sigma \in \mathcal{H}. f = f \circ \sigma
%   \end{gather*}
% \end{frame}

% \section{Eliminators, take 2!}

% \begin{frame}[fragile]{Poking and pointing}
%   The \emph{derivative} $F'$ of $F$ represents $F$-structures with a
%   hole.

%   \begin{center}
%   \begin{diagram}[width=100]
%     import Species
%     dia = drawSpT (nd 'F' (map lf [Leaf, Hole, Leaf, Leaf])) # pad 1.1
%   \end{diagram}
%   \end{center}

%   The \emph{pointing} of $F$, $\pt{F} \triangleq X \cdot F'$,
%   represents $F$-structures with a distinguished element.

%   \begin{center}
%   \begin{diagram}[width=100]
%     import Species
%     dia = drawSpT (nd 'F' (map lf [Leaf, Point, Leaf, Leaf])) # pad 1.1
%   \end{diagram}
%   \end{center}

%   \onslide<2> Pointing \emph{breaks symmetry}.
% \end{frame}

% \begin{frame}[fragile]{Pointing}
%   \begin{center}
%   \begin{diagram}[width=250]
%     import Species
%     f   = drawSpT (nd 'F' (map lf [Leaf, Leaf, Leaf, Leaf])) # pad 1.1
%     fpt = drawSpT (nd 'F' (map lf [Point, Leaf, Leaf, Leaf])) # pad 1.1

%     dia = [f, elimArrow, fpt] # map centerY # foldr1 (||-||)
%   \end{diagram}
%   \end{center}

%   \[ \pt{(-)} : F \to \pt{F} ? \]

%   \begin{center}
%   \onslide<2>\emph{Only} for polynomials!
%   \end{center}
% \end{frame}

% \begin{frame}[fragile]{Pointing in context}
%   \dots but Peter Hancock's ``cursor down'' operator is fine: \[ \down
%   : F \to F \pt{F} \]

%   \begin{diagram}[width=300]
%     import Species
%     c = Cyc [lab 0, lab 2, lab 3]
%     d1 = draw c
%     d2 = draw (down c)
%     dia = (d1 ||-|| elimArrow ||-|| d2) # pad 1.05
%   \end{diagram}
% \end{frame}

% \begin{frame}[fragile]{Eliminating with $\down$}
%   \begin{diagram}[width=300]
%     import Species
%     c = Cyc [lab 0, lab 2, lab 3]
%     d1 = draw c
%     d2 = draw (down c)
%     d3 = draw (Cyc (replicate 3 d4))
%     d4 :: Diagram Cairo R2
%     d4 = square 1 # fc purple
%     x ||/|| y = x |||||| strutX 0.5 |||||| y
%     t s = (text s <> strutY 1.3) # scale 0.5
%     dia = (d1 ||/||
%                arrow 1 (t "χ") ||/||
%            d2 ||/||
%                arrow 1 (t "F e'") ||/||
%            d3 ||/||
%                arrow 1 (t "δ") ||/||
%            d4
%           )
%           # pad 1.05
%   \end{diagram}
% \end{frame}

% \begin{frame}[fragile]{Other uses of $\down$}
%   %% XXX 4  -- draw example of another thing "down" is useful for
% %  Note $\down$ is useful for other things too. ``Map in context''.
% %  e.g. cycles.
%   \begin{diagram}[width=300]
%     import Species
%     c = Cyc (map lab' [blue, red, yellow])
%     d1 = draw c
%     d2 = draw (down c)
%     d3 = draw (fmap firstTwo (down c))
%     d4 = draw (Cyc (map lab' [purple, orange, green]))
%     firstTwo = map unPoint . take 2 . dropWhile isPlain . cycle . getCyc
%     isPlain (Plain x) = True
%     isPlain _         = False
%     unPoint (Plain x) = x
%     unPoint (Pointed x) = x
%     t s = (text s <> strutY 1.3) # scale 0.5
%     x ||/|| y = x |||||| strutX 0.5 |||||| y
%     infixl 6 ||/||
%     dia = (
%           ( d1 ||/||
%               arrow 1 (t "χ") ||/||
%             d2 ||/||
%               arrow 3 (t "F (id × head)" # scale 0.8)
%           )
%           ===
%           strutY 1
%           ===
%           ( square 1 # lw 0 ||/||
%             d3 ||/||
%               arrow 1 (t "F ⊕") ||/||
%             d4
%           )

%           )
%           # pad 1.05
%   \end{diagram}
% \end{frame}

% \begin{frame}
%   Future work:
%   \begin{itemize}
%   \item What do proof obligations for eliminators with $\down$ look
%     like in practice?
%   \item Relationship to quotient containers?
%   \end{itemize}
% \end{frame}
\end{document}
