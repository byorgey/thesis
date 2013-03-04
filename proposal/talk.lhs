%% -*- mode: LaTeX; compile-command: "mk" -*-
\documentclass[xcolor=svgnames,12pt]{beamer}

\usepackage{haskell}
%include lhs2TeX-extra.fmt

\usepackage{brent}
\usepackage{species}
\usepackage[outputdir=diagrams]{diagrams-latex}
\graphicspath{{images/}}

\usepackage[percent]{overpic}

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

  % XX remove this before giving actual talk!
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

\renewcommand{\emph}{\textbf}

\title{Combinatorial Species and Algebraic Data Types}
\date{Dissertation Proposal \\ March 2, 2013}
\author{Brent Yorgey}
\titlegraphic{}  % \includegraphics[width=2in]{foo}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\begin{frame}[fragile]
   \titlepage
   \hfill \includegraphics[width=0.5in]{plclub}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Outline}
  \begin{itemize}
  \item History
  \item Algebraic data types
  \item Combinatorial species
  \item Species types
  \item The \pkg{species} library
  \item Timeline
  \end{itemize}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{History}
\label{sec:history}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Before species\dots}
  \begin{itemize}
  \item Collections of techniques for dealing with combinatorial objects
  \item Largely centered around \emph{generating functions} (Stanley,
    Enumerative Combinatorics; Wilf, generatingfunctionology)
  \item All rather ad-hoc.
  \end{itemize}
\end{frame}

\begin{frame}{Species!}
  \begin{center}
    Andr\'e Joyal, 1981: \raisebox{-.5\height}{\includegraphics[height=0.8\textheight]{joyal-species}}
  \end{center}
\end{frame}

\begin{frame}{Species!}
  \begin{center}
    1997: \hspace{0.5in} \raisebox{-.5\height}{\includegraphics[width=1.5in]{BLL-cover}}
  \end{center}
\end{frame}

\begin{frame}{Species and computer science}
  \begin{itemize}
  \item Flajolet, Salvy, \& Zimmermann --- LUO, combstruct, combinat
  \item Carette \& Uszkay
  \item Joachim Kock
  \end{itemize}
\end{frame}

\begin{frame}{Species and ADTs?}
  \begin{center}
    The connection is ``obvious''. \bigskip

    \onslide<2->
    \dots but what can we do with it? \bigskip

    \onslide<3->
    \emph{A beautiful Answer in search of a Question.}
  \end{center}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Algebraic data types}
\label{sec:ADTs}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}[fragile]{Algebraic data types}

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

\onslide<2->
\begin{center}
  Note: no arrow types in this talk!
  \begin{minipage}[c]{1in}
  \begin{diagram}[width=50]
arrow = (hrule 1 # alignR <> arrowhead) # lw 0.1 # centerX
arrowhead = fromVertices [ (-1) & 0, origin, ((-1) & 0) # rotate (70 :: Deg) ]
          # rotate (-35 :: Deg)
          # scale 0.3
no = (circle 1 <> hrule 2 # rotateBy (1/8))
   # lw 0.2 # lc red
dia = (no <> arrow) # pad 1.2
  \end{diagram}
  \end{minipage}
\end{center}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}[fragile]{ADT example}
  Binary tree type:
  \begin{diagram}[width=75]
import           Diagrams.TwoD.Layout.Tree
import Diagrams (drawBinTree)

t = BNode 1 (BNode 8 (leaf 7) (leaf 2)) (BNode 6 (BNode 5 (leaf 2) (leaf 1)) (leaf 4))

tree = drawBinTree with . fmap drawNode $ t

drawNode n = text (show n) # fontSize 0.5 <> circle 0.3 # fc white

dia = tree # centerXY # pad 1.1
  \end{diagram}
%$

%format Tree  = "\tycon{Tree}"
%format Empty = "\con{Empty}"
%format Node  = "\con{Node}"
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

\begin{frame}{The fruits of algebra}
  \begin{center}
    \includegraphics[width=2in]{orange-tree}
  \end{center}

  \begin{itemize}
  \item Initial algebra semantics, folds, ``origami'' programming
  \item Generic programming
  \item Connections to algebra and calculus (e.g. zippers)
  \end{itemize}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Combinatorial species}
\label{sec:species}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}[fragile]{Species}
  \begin{center}
    The theory of combinatorial species is a theory of \\
    \emph{labeled structures}. \bigskip

  \begin{diagram}[width=200]
import Diagrams
dia = (octo [0..7] |||||| strutX 4 |||||| tree # centerXY)
    # centerXY
    # pad 1.1
  \end{diagram}
  \end{center}
\end{frame}

\begin{frame}[fragile]{Data structure = shape + data}
\begin{diagram}[width=300]
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
\end{frame}

\begin{frame}[fragile]{Species definition}
  \begin{center}
  Big idea: structures \emph{indexed by size}.

  \begin{diagram}[width=300]
import Diagrams
import Diagrams.TwoD.Layout.Tree

enumTreesU :: Int -> [BTree ()]
enumTreesU 0 = [Empty]
enumTreesU n = [ BNode () l r
               || k <- [0..n-1]
               , l <- enumTreesU (n-1-k)
               , r <- enumTreesU k
               ]

dia = pad 1.1
    . centerXY
    . vcat' with { sep = 2 }
    . zipWith (\n row -> (text (show n) # fontSize 1.5 <> square 1 # lw 0) |||||| strutX 2 |||||| row) [0..]
    . map
      ( centerY
      . hcat' with { sep = 1 }
      . map (drawBinTree with)
      . (map . fmap) (const (circle 0.3 # fc black))
      . enumTreesU
      )
    $ [0..4]
  \end{diagram}
%$
  \note{Simple but gives us lots of traction.  Asymptotics, random
    generation, ...}
\end{center}
\end{frame}

\begin{frame}[fragile]{Species definition}
  \begin{center}
    Better idea (Joyal's key insight): index by \emph{labels} and
    insist the \emph{particular labels used don't matter}.
    \begin{diagram}[width=300]
import           Diagrams.TwoD.Layout.Tree
import           Diagrams (drawBinTree, loc, select, subsets)
import Data.List (intercalate)

enumTrees :: [a] -> [BTree a]
enumTrees [] = [Empty]
enumTrees as = [ BNode a l r
               || (a,as') <- select as
               , (ls,rs) <- subsets as'
               , l <- enumTrees ls
               , r <- enumTrees rs
               ]

ellipsis = hcat' with {sep = 0.4} (replicate 3 (circle 0.3 # fc black))

dia = pad 1.1
    . centerXY
    . vcat' with { sep = 2 }
    . zipWith (\n row -> (text ("{" ++ intercalate "," (map show [0..n-1]) ++ "}" ) # fontSize 1 <> square 1 # lw 0) |||||| strutX 2 |||||| row) [0..]
    . map
      ( centerY
      . (\l -> if length l <= 10
                 then hcat' with { sep = 1 } l
                 else hcat' with { sep = 1 } (take 10 l) # centerY |||||| ellipsis)
      . map (drawBinTree with { slVSep = 2, slHSep = 2 })
      . (map . fmap) loc
      . enumTrees
      . (\n -> [0..n-1])
      )
    $ [0..3]
    \end{diagram}
%$
% XX if time, come back and redraw the same thing with a different
% set of labels
  \end{center}
  \note{note also distinct labelings.  This is a feature, not a bug ---
  allows to seamlessly talk about non-regular structures as well as
  ``unlabelled'' structures.}
\end{frame}

\begin{frame}{Species definition}
  A \term{species} $F$ is a pair of mappings which
\begin{itemize}
\item<2-> sends any finite set $U$ (of \term{labels}) to a finite set
  $F[U]$ (of \term{structures}), and
\item<3-> sends any bijection on finite sets $\sigma : U \bij V$ (a
  \term{relabeling}) to a function $F[\sigma] : F[U] \to F[V]$
\end{itemize}
\onslide<4->
satisfying the following functoriality conditions:
\begin{itemize}
\item $F[id_U] = id_{F[U]}$, and
\item $F[\sigma \circ \tau] = F[\sigma] \circ F[\tau]$.
\end{itemize}
\onslide<5->
\begin{center}
  (Functors from $\B$ to $\FinSet$.)
\end{center}
\end{frame}

\begin{frame}{Relabeling}
  \begin{center}
    \includegraphics{relabeling}
  \end{center}
\end{frame}

\begin{frame}[fragile]{Examples}
\begin{center}
    \begin{diagram}[width=300]
import Species
import Data.List
import Data.List.Split

dia =
  hcat' with {sep = 0.5}
  [ unord (map labT [0..2])
  , arrow 2 (txt "L")
  , enRect listStructures
  ]
  # centerXY
  # pad 1.1

drawList = hcat . intersperse (arrow 0.4 mempty) . map labT

listStructures =
    hcat' with {sep = 0.7}
  . map (vcat' with {sep = 0.5})
  . chunksOf 2
  . map drawList
  . permutations
  $ [0..2]
    \end{diagram}
%$
\end{center}
\end{frame}

% \begin{frame}[fragile]{Examples}
%   \begin{center}
% \begin{diagram}[width=300]
% import Species
% import Diagrams
% import Data.Tree
% import Diagrams.TwoD.Layout.Tree

% dia =
%   hcat' with {sep = 0.5}
%   [ unord (map labT [0..2])
%   , arrow 2 (txt "T")
%   , enRect treeStructures
%   ]
%   # centerXY
%   # pad 1.1

% drawTreeStruct = renderTree id (~~) . symmLayout . fmap labT

% -- this is actually generating only FULL binary trees, where each node
% -- has 0 or 2 children.

% trees []   = []
% trees [x]  = [ Node x [] ]
% trees xxs  = [ Node x [l,r]
%              || (x,xs) <- select xxs
%              , (ys, zs) <- subsets xs
%              , l <- trees ys
%              , r <- trees zs
%              ]

% treeStructures =
%     hcat' with {sep = 0.5}
%   . map drawTreeStruct
%   . trees
%   $ [0..2]
% \end{diagram}
% %$
%   \end{center}
% \end{frame}

\begin{frame}[fragile]{Examples}
  \begin{diagram}[width=300]
import Species
import Data.List (permutations)

dia =
  hcat' with {sep = 0.5}
  [ unord (map labT [0..3])
  , arrow 2 (txt "C")
  , enRect cycleStructures
  ]
  # centerXY
  # pad 1.1

cycleStructures =
    hcat' with {sep = 0.5}
  . map (flip cyc' 1 . map labT . (0:))
  . permutations
  $ [1..3]
  \end{diagram}
  %$
\end{frame}

\begin{frame}[fragile]{Examples}
\begin{diagram}[width=300]
import           Data.List.Split                (chunksOf)
import qualified Data.Map                       as M
import           Diagrams                       (drawGraph)
import           Species

dia =
  hcat' with {sep = 0.5}
  [ unord (map labT [0..3])
  , arrow 2 (txt "G")
  , enRect graphStructures
  ]
  # centerXY
  # pad 1.1

-- generated using species library,
--  map (map ((\[x,y] -> (x,y)) . getSet) . getSet . unComp) (enumerate simpleGraphs [0..2] :: [(Set :.: Set) Int])
all3graphs = [[],[(0,1)],[(0,2)],[(0,2),(0,1)],[(1,2)],[(1,2),(0,1)],[(1,2),(0,2)],[(1,2),(0,2),(0,1)]]

all4graphs = [[],[(0,1)],[(0,2)],[(0,2),(0,1)],[(0,3)],[(0,3),(0,1)],[(0,3),(0,2)],[(0,3),(0,2),(0,1)],[(1,2)],[(1,2),(0,1)],[(1,2),(0,2)],[(1,2),(0,2),(0,1)],[(1,2),(0,3)],[(1,2),(0,3),(0,1)],[(1,2),(0,3),(0,2)],[(1,2),(0,3),(0,2),(0,1)],[(1,3)],[(1,3),(0,1)],[(1,3),(0,2)],[(1,3),(0,2),(0,1)],[(1,3),(0,3)],[(1,3),(0,3),(0,1)],[(1,3),(0,3),(0,2)],[(1,3),(0,3),(0,2),(0,1)],[(1,3),(1,2)],[(1,3),(1,2),(0,1)],[(1,3),(1,2),(0,2)],[(1,3),(1,2),(0,2),(0,1)],[(1,3),(1,2),(0,3)],[(1,3),(1,2),(0,3),(0,1)],[(1,3),(1,2),(0,3),(0,2)],[(1,3),(1,2),(0,3),(0,2),(0,1)],[(2,3)],[(2,3),(0,1)],[(2,3),(0,2)],[(2,3),(0,2),(0,1)],[(2,3),(0,3)],[(2,3),(0,3),(0,1)],[(2,3),(0,3),(0,2)],[(2,3),(0,3),(0,2),(0,1)],[(2,3),(1,2)],[(2,3),(1,2),(0,1)],[(2,3),(1,2),(0,2)],[(2,3),(1,2),(0,2),(0,1)],[(2,3),(1,2),(0,3)],[(2,3),(1,2),(0,3),(0,1)],[(2,3),(1,2),(0,3),(0,2)],[(2,3),(1,2),(0,3),(0,2),(0,1)],[(2,3),(1,3)],[(2,3),(1,3),(0,1)],[(2,3),(1,3),(0,2)],[(2,3),(1,3),(0,2),(0,1)],[(2,3),(1,3),(0,3)],[(2,3),(1,3),(0,3),(0,1)],[(2,3),(1,3),(0,3),(0,2)],[(2,3),(1,3),(0,3),(0,2),(0,1)],[(2,3),(1,3),(1,2)],[(2,3),(1,3),(1,2),(0,1)],[(2,3),(1,3),(1,2),(0,2)],[(2,3),(1,3),(1,2),(0,2),(0,1)],[(2,3),(1,3),(1,2),(0,3)],[(2,3),(1,3),(1,2),(0,3),(0,1)],[(2,3),(1,3),(1,2),(0,3),(0,2)],[(2,3),(1,3),(1,2),(0,3),(0,2),(0,1)]]

the3Map = M.fromList (zip [0..] (triangle 2))
the4Map = M.fromList (zip [0..] (square 2))

graphStructures
  = vcat' with {sep = 0.5}
  . map (hcat' with {sep = 0.5})
  . chunksOf 8
  . map (\es -> drawGraph labT (the4Map, es) # scale 0.5)
  $ all4graphs
\end{diagram}
%$
\end{frame}

\begin{frame}{Too many species!}
  \begin{center}
    \includegraphics[width=\textwidth]{universe}
  \end{center}
\end{frame}

\begin{frame}[fragile]{Algebraic species}
  \begin{columns}[t]
    \begin{column}{0.5 \textwidth}
      Primitive species:
      \begin{itemize}
      \item $\Zero$
      \item $\One$
      \item $\X$
      \end{itemize}
    \end{column}
    \begin{column}{0.5 \textwidth}
      Species operations:
      \begin{itemize}
      \item $F + G$
      \item $F \sprod G$
      \end{itemize}
    \end{column}
\end{columns}
\onslide<2->
\begin{center}
  \begin{diagram}[width=130]
    import Species

    theDia = struct 5 "F+G" |||||| strutX 1 |||||| txt "=" ||||||
             strutX 1 |||||| ( struct 5 "F" === txt "+" === struct 5 "G" )
             # centerY

    dia = theDia # centerXY # pad 1.1
  \end{diagram}
  \begin{diagram}[width=130]
    import Species

    theDia = struct 5 "F•G" |||||| strutX 1 |||||| txt "=" ||||||
             strutX 1 |||||| ( struct 2 "F" === strutY 0.2 === struct 3 "G" )
             # centerY

    dia = theDia # centerXY # pad 1.1
  \end{diagram}
\end{center}
\end{frame}

\begin{frame}{Algebraic species examples}
  \[ \L = \One + \X \sprod \L \]
  \[ \T = \One + \X \sprod \T^2 \]
\end{frame}

\begin{frame}{Algebraic species}
  \begin{columns}[t]
    \begin{column}{0.5 \textwidth}
      Primitive species:
      \begin{itemize}
      \item $\Zero$
      \item $\One$
      \item $\X$
      \item<2-> $\Cyc$
      \item<2-> $\E$
      \item<2-> \dots
      \end{itemize}
    \end{column}
    \begin{column}{0.5 \textwidth}
      Species operations:
      \begin{itemize}
      \item $F + G$
      \item $F \sprod G$
      \item<2-> $F \comp G$
      \item<2-> $F \times G$
      \item<2-> $F'$
      \item<2-> $\pt{F}$
      \item<2-> $F \fcomp G$
      \item<2-> \dots
      \end{itemize}
    \end{column}
\end{columns}
\end{frame}

\begin{frame}[fragile]{Algebraic species example}
  \begin{center}
    The species of \emph{simple graphs} can be described by:

    \[ \mathcal{G} = (\E \sprod \E) \fcomp (\X^2 \sprod \E) \]

    \begin{diagram}[width=200]
import Diagrams

dia = gr # centerXY # pad 1.1
    \end{diagram}
%$
  \end{center}
\end{frame}

\begin{frame}{Generating functions}
  \[ F(x) = \sum_{n \geq 0} ||F[n]|| \frac{x^n}{n!} \]

\[ \L(x) = 1 + x + x^2 + \dots = \frac{1}{1-x} \]
\[ \E(x) = 1 + x + \frac{x^2}{2} + \frac{x^3}{3!} + \dots = e^x \]
\end{frame}

\begin{frame}{Homomorphism!}
  \[ \Zero(x) = 0 \]
  \[ \One(x) = 1 \]
  \[ \X(x) = x \]
  \[ (F + G)(x) = F(x) + G(x) \]
  \[ (F \sprod G)(x) = F(x)G(x) \]
  \begin{center}
  \dots
  \end{center}
\onslide<2->
Enumeration, asymptotics, random generation, \dots
\end{frame}

\begin{frame}{Exposition}
    A key contribution of my dissertation will be \emph{an exposition
      of the theory of species},
    \onslide<2-> accessible to functional
    programmers and computer scientists in general.
\end{frame}

\begin{frame}
  \begin{center}
    \begin{overpic}[width=1in]{BLL-cover}
      \put(20,30){\huge \$\$\$}
      \put(20,60){\huge ???}
    \end{overpic}
  \end{center}
\end{frame}

\begin{frame}{Exposition: remaining work}
  \begin{itemize}
    \item Molecular and atomic species
    \item Weighted species
    \item Virtual species
    \item $\mathbb{L}$-species
    \item \dots
  \end{itemize}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Species types}
\label{sec:species-types}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}
  \begin{center}
    \emph{Can we use the theory of species as a foundational basis for
      container types?}
  \end{center}
\end{frame}

\begin{frame}{What would we need?}
  \begin{itemize}
  \item Formal way to interpret species as data types
  \item Introduction and elimination forms
  \item \dots?
  \end{itemize}
\end{frame}

\subsection{Eliminators for species types}
\label{sec:elim}

\begin{frame}[fragile]{Symmetry}
  % Symmetric structure examples: cycles, bags, hierarchies,
  % heaps\dots
  \begin{center}
  \begin{diagram}[width=250]
import Species
import Data.Tree

dia1 = cyc [0..4] 1.2 # pad 1.1

dia2 = ( roundedRect 2 1 0.2
         <> (lab 0 |||||| strutX 0.3 |||||| lab 3)
            # centerXY
       )
       # pad 1.1
       # lw 0.02

t   = Node Bag [lf (Lab 1), lf (Lab 2), Node Bag [lf (Lab 0), lf (Lab 3)]]
dia3 = drawSpT' mempty with t # pad 1.1

dia = hcat' with {sep = 1} . map centerXY $ [dia1, dia2, dia3]
  \end{diagram}
  %$
  \bigskip

%  \onslide<2>\dots how can we program with these?
  \end{center}
\end{frame}

\begin{frame}[fragile]{Eliminating symmetries?}
  \begin{center}
  \begin{diagram}[width=200]
import Species
dia = (cyc [0..4] 1.2 ||-|| elimArrow ||-|| (text "?" <> square 1 # lw 0)) # pad 1.1
  \end{diagram}
  \end{center}
  \begin{center}
    \onslide<2>Want a compiler guarantee that eliminators are
    oblivious to ``representation details''.
  \end{center}
\end{frame}

% \begin{frame}
%   XX redo this slide.  What exactly do I want to say?
%   We can build eliminators in a type-directed way, using ``high
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
%     \end{tabular}
%   \end{center}
% \end{frame}

\begin{frame}[fragile]{Molecular species}
  \begin{center}
    The essence of symmetry: $\X^n/\H$, where $\H \subseteq \S_n$
    \bigskip

  \begin{overprint}
    \onslide<1>
    \centering
  \begin{diagram}[width=200]
import Species
dia = hcat $ zipWith (\i n -> named i . (<> square 1) . labT $ n) ([0..] :: [Int]) [0..4]
  \end{diagram}
  \onslide<2>
  \centering
  \begin{diagram}[width=200]
import Species
dia = hcat $ zipWith (\i n -> named i . (<> square 1) . labT $ n) ([0..] :: [Int]) (4 : [0..3])
  \end{diagram}
  \end{overprint}
  \end{center}
\end{frame}

\begin{frame}{Eliminating symmetries}
  \begin{gather*}
    (X^n/\mathcal{H})[A] \to B \\
    \cong \\
    \Sigma f : X^n \to B.\;\; \Pi \sigma \in \mathcal{H}.\;\; f = f \circ \sigma
  \end{gather*}
\end{frame}

\subsection{Eliminators, take 2}
\label{sec:elim2}

\begin{frame}{Eliminators, take 2}
  A different way to think about eliminators\dots
\end{frame}

\begin{frame}[fragile]{Poking and pointing}
  The \emph{derivative} $F'$ of $F$ represents $F$-structures with a
  hole.

  \begin{center}
  \begin{diagram}[width=200]
import Species

theDia = struct 4 "F'"
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
  \end{center}
\end{frame}

\begin{frame}[fragile]{Poking and pointing}
  The \emph{pointing} of $F$, $\pt{F} \triangleq X \cdot F'$,
  represents $F$-structures with a distinguished element.

  \begin{center}
  \begin{diagram}[width=200]
import Species

theDia = drawSpT (struct'' 5 ((text "F" <> rect 1 1 # lw 0) |||||| circle 0.2 # fc black # translateY 0.2)) # centerXY
         ||||||
         strutX 1
         ||||||
         txt "="
         ||||||
         strutX 1
         ||||||
         ( struct 1 "X" # alignR
           ===
           strutY 0.1
           ===
           drawSpT
           ( nd (txt "F")
             [ lf Leaf
             , lf Leaf
             , lf Leaf
             , lf Hole
             , lf Leaf
             ]
           ) # alignR
         ) # centerXY
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
  \end{center}

  \onslide<2> Pointing \emph{breaks symmetry}.
\end{frame}

\begin{frame}[fragile]{Pointing}
  \begin{center}
  \begin{diagram}[width=250]
import           Species
f   = drawSpT (nd (label 'F') (map lf [Leaf, Leaf, Leaf, Leaf])) # pad 1.1
fpt = drawSpT (nd (label 'F') (map lf [Point, Leaf, Leaf, Leaf])) # pad 1.1

label c = text [c] <> rect 2 1 # lw 0

dia = [f, elimArrow, fpt] # map centerY # foldr1 (||-||)
  \end{diagram}
  \end{center}

  \[ \pt{(-)} : F \to \pt{F} ? \]

  \begin{center}
  \onslide<2>\emph{Only} for polynomial species!
  \end{center}
\end{frame}

\begin{frame}[fragile]{Pointing in context}
  The trick is to choose every point at once: \[ \down
  : F \to F \comp \pt{F} \]

  \begin{diagram}[width=300]
    import Species
    c = Cyc [lab 0, lab 2, lab 3]
    d1 = draw c
    d2 = draw (down c)
    t s = (text s <> strutY 1.3) # scale 0.5
    dia = (d1 ||-|| arrow 2 (t "χ") ||-|| d2) # pad 1.05
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

\begin{frame}{Species types: remaining work}
  \begin{itemize}
  \item Introduction forms
  \item Relate two formulations of eliminators
  \item Extend theory to multi-sort species and recursive species
  \item Make all of this practical for programming!
  \end{itemize}
\end{frame}

% \begin{frame}{What if something goes wrong?}
%   XX need to address that concern here.
% \end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{The \pkg{species} library}
\label{sec:species-lib}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}
  \begin{center}
    \includegraphics[width=4in]{species-package.png}
  \end{center}
\end{frame}

\begin{frame}{Example usage}
  \begin{center} {\small
\begin{verbatim}
>>> take 10 . labeled $ set `o` nonEmpty sets
[1,1,2,5,15,52,203,877,4140,21147]

>>> take 10 . unlabeled $ set `o` nonEmpty sets
[1,1,2,3,5,7,11,15,22,30]

>>> enumerate (set `o` nonEmpty sets) [1,2,3]
      :: [(Set :.: Set) Int]
[{{1,2,3}},{{2,3},{1}},{{2},{1,3}},
 {{3},{1,2}},{{3},{2},{1}}]
\end{verbatim}
    }
  \end{center}
\end{frame}

\begin{frame}{Proposed feature: random generation}

  \begin{itemize}
  \item<+-> \emph{e.g.} randomly generate size-100 trees. (QuickCheck
    cannot do this!)
  \item<+-> Less urgent now that we have \texttt{gencheck} and \texttt{FEAT}\dots
  \item<+-> \dots but neither can deal with non-polynomial species.
  \end{itemize}

% One major missing feature of the library which I propose to add is the
% ability to randomly generate structures of user-defined data types,
% perhaps in concert with an existing test-generation framework such as
% FEAT~\citep{duregaard2012feat} or gencheck~\citep{gencheck}.  In
% particular, no existing frameworks can randomly generate structures
% corresponding to non-regular (symmetric) species.
\end{frame}

\begin{frame}{Why a library?}
  \begin{itemize}
  \item Of interest: doing all of this in a \emph{typed} setting.
  \item Opportunities for genuine contributions in generative combinatorics?
  \item Testbed and dissemination platform for ideas.
  \item Still a useful contribution to the community even if not a
    research contribution in and of itself.
  \end{itemize}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Timeline}
\label{sec:timeline}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Timeline}
  \begin{itemize}
  \item<+-> March--August 2013: exposition, and theory of species types
  \item<+-> September--December 2013: \texttt{species} library
  \item<+-> January--April 2014: writing
  \item<+-> May 2014: defense
  \end{itemize}

% \textbf{March--August 2013}: my focus during this period will be
% twofold: to develop an exposition of species theory, both through my
% blog and in a form suitable to eventually go in my dissertation; and,
% in parallel, to work out a theory of species data types as outlined in
% \pref{sec:species-as-data-types}.
% \textbf{September--December 2013}: My focus during this period will be
% on development of the \texttt{species} library, as outlined in
% \pref{sec:species-library}.
% \textbf{January--April 2014} My focus during the first part of 2014
% will be on writing my dissertation, with the goal of defending in May.
\end{frame}

\begin{frame}[fragile]
  \begin{center}
    Thank you! \bigskip

  \begin{diagram}[width=250]
import Species
import Data.Tree

dia1 = cyc [0..4] 1.2 # pad 1.1

dia2 = ( roundedRect 2 1 0.2
         <> (lab 0 |||||| strutX 0.3 |||||| lab 3)
            # centerXY
       )
       # pad 1.1
       # lw 0.02

t   = Node Bag [lf (Lab 1), lf (Lab 2), Node Bag [lf (Lab 0), lf (Lab 3)]]
dia3 = drawSpT' mempty with t # pad 1.1

dia = hcat' with {sep = 1} . map centerXY $ [dia1, dia2, dia3]
  \end{diagram}
  %$
  \end{center}
\end{frame}

\end{document}
