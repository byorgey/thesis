%% -*- mode: LaTeX; compile-command: "mk" -*-
\documentclass[xcolor=svgnames,12pt]{beamer}

%include polycode.fmt

\usepackage[outputdir=diagrams]{diagrams-latex}
\graphicspath{{images/}}

\usepackage{prettyref}
\usepackage{xspace}
\usepackage{ulem}

\usepackage{../defs}

\newif \iftodos \todostrue

% argh, this isn't working
\renewcommand{\todo}[1]{\iftodos{\usebeamercolor[fg]{alerted text} [TODO: #1]}\fi}

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

% \setbeameroption{show notes}

\setbeamercolor{alerted text}{fg=red}

\renewcommand{\emph}{\textbf}
\renewcommand{\ie}{\textit{i.e.}\xspace}
\renewcommand{\eg}{\textit{e.g.}\xspace}

\title{Combinatorial Species and Labelled Structures}
\date{PhD Dissertation Defense \\ October 14, 2014 }
\author{Brent Yorgey}
\titlegraphic{}  % \includegraphics[width=2in]{foo}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\begin{frame}[fragile]
   \titlepage
   \hfill \includegraphics[width=0.5in]{plclub}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}
\label{sec:intro}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}[fragile]{A Tale of Two \sout{Cities} Worlds}
  \note{This thesis is a story about two worlds.  One, the world of
    combinatorics, i.e. mathematics of counting things.  Two, the
    world of PL.  This diss: building a partiuclar bridge between
    them.}
\onslide<2->{
  \begin{minipage}{0.33\linewidth}
    \begin{center}
      \emph{Combinatorics}
      \begin{gather*}
        1, 2, 3, 4, 5, \dots \\
        \sum_{n \geq 0} f_n \frac{x^n}{n!}
      \end{gather*}
      \includegraphics[width=0.75in]{BinTree}
    \end{center}
  \end{minipage}
  }
  \onslide<4->{
  \begin{minipage}{0.23\linewidth}
    \begin{center}
      \todo{bridge}
    \end{center}
  \end{minipage}
  }
  \onslide<3->{
  \begin{minipage}{0.33\linewidth}
    \begin{center}
      \emph{Programming Languages}
      \begin{gather*}
        \lam {f : \tau \to \tau} {\lam {a : \tau} {f \; a}}
      \end{gather*}
\begin{verbatim}
data Tree a
  = Empty | ...
\end{verbatim}
      \includegraphics[width=0.75in]{BinTree}
    \end{center}
  \end{minipage}
  }
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}[fragile]{Example: trees}
  \note{As an example of the connection, consider binary trees.}

\begin{center}
    \begin{diagram}[width=100]
import SpeciesDiagrams
import Data.Tree
import Diagrams.TwoD.Layout.Tree
import Control.Arrow (first, second)
import Data.List.Split (chunksOf)
import Data.Maybe (fromJust)

dia = (drawBinTreeWide . fmap labT) sampleBTree7
  # centerXY
  # pad 1.1
  # lwO 0.7

nil = square 0.2 # fc black

treeStructures
  = centerXY
  . vcat' (with & sep .~ 0.5)
  . map (centerX . hcat' (with & sep .~ 0.5))
  . chunksOf 10
  . map (drawBinTreeWide . fmap labT)
  . enumTrees
  $ [0..2]   -- $
    \end{diagram}
\end{center}

  \onslide<2->{
  \begin{minipage}{0.4\linewidth}
    \begin{gather*}
    T = 1 + \X \cdot T^2 \\
    T(x) = 1 + x + 2x^2 + 5x^3 + \dots
    \end{gather*}
  \end{minipage}
  }
  \onslide<3->{
  \begin{minipage}{0.5\linewidth}
    \begin{spec}
data Tree a
  =  Empty
  |  Node a (Tree a) (Tree a)
    \end{spec}
  \end{minipage}
  }
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}[fragile]{Why is this interesting?}
  \note{
    \begin{itemize}
    \item species that are not ADTs; maybe this will give us tools for
      working with them
    \item Potential for interesting tools to work with existing data
      types (enumeration, random generation, generic manipulation,
      memory layout (!))
    \item doing things constructively gives us additional insight into
      the math.
    \end{itemize}
  }
  \begin{overprint}

    \onslide+<1>
    \begin{itemize}
    \item Species that are not algebraic data types
    \end{itemize}
    \begin{center}
      \begin{diagram}[width=100]
        import SpeciesDiagrams

        dia = cyc' (map labT [0,2,1,3]) 1
          # frame 0.5
          # lwO 0.7
      \end{diagram}
      % \todo{Something else: bag? hierarchy? parallel/series graphs?}
      % \begin{diagram}[width=100]
      %   import SpeciesDiagrams

      %   dia = circle 1
      % \end{diagram}
    \end{center}

    \onslide+<2>
    \begin{itemize}
    \item Tools for working with existing algebraic data types
    \end{itemize}
    % \todo{example pictures illustrating enumeration, random
    %   generation, memory layout}
    \begin{center}
      \begin{diagram}[width=300]
import           Control.Arrow                  (first, second)
import           Data.List.Split                (chunksOf)
import           Data.Maybe                     (fromJust)
import           Data.Tree
import           Diagrams.TwoD.Layout.Tree
import           Diagrams.TwoD.Path.Metafont
import           SpeciesDiagrams
import           Structures                     (pair)

dia
  = vcat' (with & sep .~ 2)
    [ hcat' (with & sep .~ 5) [trees # centerY, randomTree # scale 0.25 # centerY] # centerX
    , sharedMem # centerX # scale 0.3
    ]
  # centerXY
  # frame 1
  # lwO 0.7

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
  # centerXY

part1, part2 :: [Int]
part1 = [3,0,1,2,6]
part2 = [5,4,7]

trees = treeStructures # scale 0.5

nil = square 0.2 # fc black

treeStructures
  = centerXY
  . vcat' (with & sep .~ 0.5)
  . map (centerX . hcat' (with & sep .~ 0.5))
  . chunksOf 10
  . map (drawBinTreeWide . fmap labT)
  . enumTrees
  $ [0..2]  -- $

data PTree = PLeaf || PBranch PTree PTree

bigTree = tToB (PBranch (PBranch (PBranch (PBranch (PBranch (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch PLeaf PLeaf)) PLeaf)) PLeaf) PLeaf) PLeaf) (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf PLeaf) PLeaf)) (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch (PBranch (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch (PBranch PLeaf PLeaf) PLeaf))) (PBranch PLeaf PLeaf)) (PBranch PLeaf (PBranch PLeaf (PBranch PLeaf PLeaf)))) (PBranch (PBranch PLeaf PLeaf) PLeaf))) (PBranch PLeaf (PBranch PLeaf PLeaf))))) (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf PLeaf) PLeaf)) (PBranch (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) (PBranch PLeaf PLeaf))) PLeaf)) (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) (PBranch PLeaf PLeaf)) (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf (PBranch PLeaf PLeaf)) (PBranch PLeaf (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf PLeaf)) (PBranch PLeaf (PBranch PLeaf (PBranch PLeaf PLeaf))))) (PBranch PLeaf PLeaf)) PLeaf)) (PBranch PLeaf PLeaf))) PLeaf))))) PLeaf)) (PBranch (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) (PBranch PLeaf (PBranch PLeaf PLeaf))) PLeaf) PLeaf))) PLeaf)))) (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) (PBranch PLeaf (PBranch (PBranch (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf PLeaf)) (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) PLeaf) (PBranch PLeaf (PBranch (PBranch PLeaf PLeaf) PLeaf))))) PLeaf) (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf PLeaf)) (PBranch (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) (PBranch PLeaf (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) (PBranch PLeaf PLeaf)) PLeaf))) (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf PLeaf))) PLeaf)) PLeaf)) (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf PLeaf))) PLeaf)))))))) PLeaf)) PLeaf)) (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch PLeaf PLeaf))) (PBranch PLeaf (PBranch PLeaf (PBranch PLeaf (PBranch PLeaf (PBranch PLeaf (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf PLeaf)) PLeaf) PLeaf)))))))))) PLeaf))) (PBranch PLeaf PLeaf))) PLeaf) (PBranch PLeaf PLeaf)) (PBranch PLeaf PLeaf)))) (PBranch (PBranch (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf (PBranch (PBranch (PBranch (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf (PBranch (PBranch PLeaf PLeaf) PLeaf))) PLeaf) (PBranch PLeaf PLeaf)) PLeaf) PLeaf) (PBranch PLeaf (PBranch (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch (PBranch PLeaf PLeaf) PLeaf)) PLeaf)) (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf PLeaf)) (PBranch PLeaf (PBranch (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch (PBranch PLeaf PLeaf) PLeaf)) PLeaf))) PLeaf) PLeaf) PLeaf)))) (PBranch PLeaf PLeaf)) PLeaf)) PLeaf))) PLeaf)))) (PBranch (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) PLeaf) (PBranch PLeaf (PBranch PLeaf PLeaf)))) (PBranch PLeaf PLeaf)) PLeaf)) PLeaf)))))) (PBranch PLeaf (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) PLeaf)))) PLeaf) PLeaf)) PLeaf))) (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch PLeaf PLeaf)) PLeaf))))) (PBranch (PBranch (PBranch (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) (PBranch PLeaf (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf PLeaf)))) PLeaf) (PBranch PLeaf (PBranch PLeaf PLeaf))) PLeaf) (PBranch (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf (PBranch PLeaf PLeaf)) PLeaf) PLeaf))) (PBranch (PBranch (PBranch (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch PLeaf PLeaf))) (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch PLeaf PLeaf))) PLeaf)) PLeaf) (PBranch PLeaf PLeaf)) PLeaf))) PLeaf) (PBranch (PBranch (PBranch (PBranch (PBranch (PBranch (PBranch (PBranch (PBranch (PBranch (PBranch PLeaf (PBranch PLeaf PLeaf)) (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch (PBranch PLeaf (PBranch PLeaf PLeaf)) PLeaf)) PLeaf)) (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf PLeaf)))) PLeaf) (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) PLeaf))) (PBranch PLeaf PLeaf)) PLeaf)) PLeaf) PLeaf) (PBranch PLeaf PLeaf)) (PBranch PLeaf PLeaf)) (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch (PBranch PLeaf PLeaf) PLeaf)) (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch PLeaf PLeaf))) (PBranch PLeaf (PBranch (PBranch (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch (PBranch (PBranch (PBranch (PBranch PLeaf (PBranch PLeaf PLeaf)) PLeaf) PLeaf) (PBranch (PBranch (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf PLeaf))) (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch PLeaf PLeaf)) PLeaf)) PLeaf)) (PBranch PLeaf PLeaf)) (PBranch PLeaf PLeaf))) (PBranch (PBranch PLeaf PLeaf) (PBranch (PBranch PLeaf PLeaf) PLeaf))) (PBranch (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch PLeaf (PBranch PLeaf PLeaf)))) PLeaf) PLeaf)) PLeaf)) PLeaf)) PLeaf) (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf PLeaf) (PBranch (PBranch PLeaf PLeaf) (PBranch (PBranch PLeaf PLeaf) PLeaf)))) PLeaf)) PLeaf)) (PBranch PLeaf (PBranch PLeaf (PBranch (PBranch PLeaf PLeaf) (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch (PBranch (PBranch (PBranch (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf (PBranch PLeaf PLeaf)) (PBranch (PBranch PLeaf PLeaf) PLeaf)) (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf (PBranch (PBranch (PBranch (PBranch PLeaf (PBranch PLeaf PLeaf)) PLeaf) (PBranch PLeaf PLeaf)) PLeaf))) PLeaf) PLeaf))) (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) (PBranch (PBranch PLeaf PLeaf) PLeaf)) (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch PLeaf PLeaf)) (PBranch PLeaf (PBranch PLeaf PLeaf))))) (PBranch PLeaf PLeaf)))))) (PBranch PLeaf (PBranch PLeaf PLeaf))) (PBranch (PBranch PLeaf PLeaf) (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch PLeaf PLeaf))) PLeaf)))) PLeaf)) PLeaf)) PLeaf)) PLeaf)) PLeaf) PLeaf) (PBranch PLeaf PLeaf)) PLeaf))) (PBranch (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) (PBranch PLeaf PLeaf)) (PBranch PLeaf PLeaf)) PLeaf)) PLeaf)) (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf PLeaf) PLeaf)) (PBranch PLeaf PLeaf)))))))))))) PLeaf) PLeaf)) (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch PLeaf (PBranch (PBranch PLeaf PLeaf) PLeaf))) (PBranch PLeaf PLeaf)))) PLeaf)))) PLeaf) PLeaf) PLeaf) (PBranch PLeaf PLeaf))))))) (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf (PBranch (PBranch (PBranch (PBranch (PBranch PLeaf PLeaf) PLeaf) PLeaf) PLeaf) PLeaf))) (PBranch (PBranch (PBranch PLeaf (PBranch PLeaf PLeaf)) (PBranch PLeaf PLeaf)) (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf (PBranch (PBranch PLeaf PLeaf) (PBranch PLeaf PLeaf))) PLeaf)) (PBranch PLeaf PLeaf))) PLeaf) PLeaf)) PLeaf)))) (PBranch PLeaf PLeaf))) PLeaf)

tToB PLeaf = Empty
tToB (PBranch l r) = BNode () (tToB l) (tToB r)

drawT = maybe mempty (renderTree (const (circle 0.05 # fc black)) (~~))
       . symmLayoutBin' (with & slVSep .~ 0.5)

randomTree = drawT bigTree
      \end{diagram}
    \end{center}

    \onslide+<3>
    \begin{itemize}
    \item Additional insight into the mathematics
    \end{itemize}
    \begin{center}  % p. 75 of my thesis. Teaser!
  \begin{diagram}[width=300]
import           Control.Arrow
import           SpeciesDiagrams

permToList = hcat' (with & sep .~ 1)
  [ drawPerm [[3,5],[2,6],[0,1,4]]
  , arrow 1
  , mountainRange labT [3,5,2,6,0,1,4]
  ]

mountainRange nd ns = lst # applyAll [conn i || i <- [0 :: Int .. length ns - 2]] # centerY
  where
    elts = map (id &&& nd) ns # zipWith (second . named) [0 :: Int ..] # map (\(i,n) -> n # translateY (fromIntegral i / 2))
    w    = (maximum . map width) elts
    lst  = hcat' (with & sep .~ w/2) elts
    conn i = withNames [i,i+1] (\[a,b] -> beneath (location a ~~ location b))

dia = permToList
  # lwO 0.7
  # frame 0.5
  \end{diagram}
    \end{center}
  \end{overprint}
\end{frame}

\begin{frame}{Contributions}
  \note{This dissertation --- start by bringing species across the
    bridge into PL-world.  More subtle than you might think ---
    connection seems ``obvious''.  }
  \begin{itemize}
  \item \emph{Port} species to PL-world
  \item \emph{Categorical requirements} for operations on generalized species
  \item ``Labelled structures'' via \emph{analytic functors}
  \item Exposition of species for a PL audience
  \item \dots and many smaller things!
  \end{itemize}
\end{frame}

\begin{frame}{Outline}
  \begin{itemize}
  \item Species---examples and formal definition
  \item ``Bringing species across the bridge''---species in homotopy
    type theory
  \item Labelled structures
  \item Conclusions and future work
  \end{itemize}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Species}
\label{sec:species}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Intuition and examples}
  \begin{center}
    A species is a \emph{family of labelled shapes}.
  \end{center}
\end{frame}

\begin{frame}[fragile]{Examples}
  \begin{center}
    \begin{diagram}[width=200]
import SpeciesDiagrams
import Data.List
import Data.List.Split

dia =
  hcat' (with & sep .~ 0.5)
  [ listStructures
  ]
  # centerXY
  # pad 1.1
  # lwO 0.7

listStructures
  = centerXY
  . hcat' (with & sep .~ 0.7)
  . map (vcat' (with & sep .~ 0.5))
  . chunksOf 2
  . map (drawList' labT)
  . permutations
  $ [0..2] -- $
    \end{diagram}
  \end{center}
\end{frame}

\begin{frame}[fragile]{Examples}
  \begin{center}
    \begin{diagram}[width=300]
import SpeciesDiagrams
import Data.Tree
import Diagrams.TwoD.Layout.Tree
import Control.Arrow (first, second)
import Data.List.Split (chunksOf)
import Data.Maybe (fromJust)

dia =
  hcat' (with & sep .~ 0.5)
  [ treeStructures # scale 0.5
  ]
  # centerXY
  # pad 1.1
  # lwO 0.7

nil = square 0.2 # fc black

treeStructures
  = centerXY
  . vcat' (with & sep .~ 0.5)
  . map (centerX . hcat' (with & sep .~ 0.5))
  . chunksOf 10
  . map (drawBinTreeWide . fmap labT)
  . enumTrees
  $ [0..2]  -- $
    \end{diagram}
  \end{center}
\end{frame}

\begin{frame}[fragile]{Examples}
  \begin{center}
    \begin{diagram}[width=150]
import SpeciesDiagrams
import Data.List
import Data.List.Split

dia =
  hcat' (with & sep .~ 0.5)
  [ cycleStructures
  ]
  # centerXY
  # pad 1.1
  # lwO 0.7

cycleStructures
  = centerXY
  . hcat' (with & sep .~ 0.7)
  . map (vcat' (with & sep .~ 0.5))
  . chunksOf 2
  . map ((\l -> cyc' l 0.8) . map labT)
  . cycles
  $ [0..3]  -- $
    \end{diagram}
  \end{center}
\end{frame}

\begin{frame}[fragile]{Examples}
  \begin{center}
    \begin{diagram}[width=200]
import           Data.List
import           Data.List.Split
import           SpeciesDiagrams

dia =
  hcat' (with & sep .~ 0.5)
  [ permStructures
  ]
  # centerXY
  # pad 1.1
  # lwO 0.7

permStructures
  = centerXY
  . hcat' (with & sep .~ 1)
  . map (vcat' (with & sep .~ 0.5))
  . chunksOf 6
  . map drawPerm
  . perms
  $ [0..3]  -- $
    \end{diagram}
  \end{center}

%  \todo{Example of series-parallel graphs?}
\end{frame}

\begin{frame}[fragile]{Labels}
  \note{What do we really mean by ``labelled'' ?}
  \begin{center}
    A species is a family of \emph{labelled} shapes.
  \end{center}

  \begin{itemize}
  \item<2-> Labels are names for \emph{locations}
  \item<3-> Labels are taken from a \emph{finite} set
  \end{itemize}

\begin{center}
    \begin{diagram}[width=75]
import SpeciesDiagrams
import Data.Tree
import Diagrams.TwoD.Layout.Tree
import Control.Arrow (first, second)
import Data.List.Split (chunksOf)
import Data.Maybe (fromJust)

dia = (drawBinTreeWide . fmap labT) sampleBTree7
  # centerXY
  # pad 1.1
  # lwO 0.7

nil = square 0.2 # fc black

treeStructures
  = centerXY
  . vcat' (with & sep .~ 0.5)
  . map (centerX . hcat' (with & sep .~ 0.5))
  . chunksOf 10
  . map (drawBinTreeWide . fmap labT)
  . enumTrees
  $ [0..2]   -- $
    \end{diagram}
\end{center}
\end{frame}

\begin{frame}[fragile]{Relabelling}
  \note{What do we mean by a ``family'' of labelled structures?  The
    labels ``shouldn't really matter'', so we require to be able to
    \emph{relabel}.}
  \begin{center}
    A species is a \emph{family} of labelled shapes.
  \end{center}

  \onslide<2->
  We must be able to \emph{relabel}:
  \begin{center}
  \begin{diagram}[width=300]
import           Data.Char                      (ord)
import           Data.Maybe                     (fromMaybe)
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

t :: BTree Int
t = BNode 1 (leaf 0) (BNode 2 (leaf 3) (leaf 4))

sig :: Int -> Char
sig = ("acebd"!!)

mkNamedNode :: IsName n => (Int -> n) -> (Int -> String) -> Int -> Diagram B R2
mkNamedNode name sh n = (text (sh n) # scale labR <> lab n) # named (name n)

mkNamedTree :: IsName n => (Int -> n) -> (Int -> String) -> BTree Int -> BTree (Diagram B R2)
mkNamedTree name sh = fmap (mkNamedNode name sh)

t1 = drawBinTreeWide . mkNamedTree id show $ t
t2 = drawBinTreeWide . mkNamedTree sig ((:[]) . sig) $ t

linkedTrees = hcat' (with & sep .~ 0.5) [t1, t2]
  # applyAll (map conn [0..4 :: Int])
  where
    conn i = connectOutside'
      (with & arrowShaft .~ selectShaft i
            & shaftStyle %~ dashingG [0.05,0.05] 0
            & arrowHead .~ noHead
      )
      i (sig i)
    selectShaft i || i `elem` [0,3] = theArc # reverseTrail
                  || i `elem` [2,4] = theArc
    selectShaft _ = hrule 1
    theArc = arc (0 @@@@ deg) (75 @@@@ deg)

drawSig :: Int -> (Int -> Char) -> Diagram B R2
drawSig n sig = hcat' (with & sep .~ 0.1) (map drawOne [0..(n-1)])
  where
    drawOne i = vcat
      [ mkNamedNode id show i
      , vrule 1 # dashingG [0.05,0.05] 0
      , mkNamedNode sig ((:[]) . sig) i ]

dia = hcat' (with & sep .~ 3)
  [ drawSig 5 sig # centerXY # named "sig"
  , linkedTrees   # centerXY # named "trees"
  ]
  # connectOutside' (with & gap .~ Local 0.5) "sig" "trees"
  # frame 0.5
  # lwO 0.7
  \end{diagram}
  \end{center}

  \onslide<3->
  Relabelling must be \emph{functorial}.
\end{frame}

\begin{frame}[fragile]{Size}
  \note{Typically organize shapes by size (\emph{i.e.} number of
    labels).  Note relabelling preserves size.  Leads to the idea of
    \emph{unlabelled} species.}

  \begin{overprint}
    \onslide<1>

    \vspace{0.2in}
  \begin{center}
    \begin{diagram}[width=200]
import           Control.Arrow                  (first, second)
import           Data.List.Split                (chunksOf)
import           Data.Maybe                     (fromJust)
import           Data.Tree
import           Diagrams.TwoD.Layout.Tree
import           SpeciesDiagrams

dia =
  vcat' (with & sep .~ 2)
  (map treeStructures [0..2] ++ [dots])
  # centerXY
  # pad 1.1
  # lwO 0.7

dots = vcat' (with & sep .~ 0.2) (replicate 3 (circle 0.1 # fc black))

nil = square 0.2 # fc black

treeStructures n
  = centerXY
  . vcat' (with & sep .~ 0.5)
  . map (centerX . hcat' (with & sep .~ 0.5))
  . chunksOf 10
  . map (drawBinTreeWide . fmap labT)
  . enumTrees
  $ [0..n]  -- $
    \end{diagram}

    \vspace{0.2in}
  \emph{Size} (\ie number of labels) is preserved by relabelling.
  \end{center}

%   \onslide<2>

%   \vspace{0.5in}
%   \begin{center}
%   \begin{diagram}[width=300]
% import           Data.Function                  (on)
% import           Data.List                      (partition, sortBy)
% import           Data.Ord                       (comparing)
% import qualified Math.Combinatorics.Multiset    as MS
% import           SpeciesDiagrams

% permForms
%   = centerXY
%   . vcat' (with & sep .~ 1)
%   . map drawPermRow
%   . (map . map) lenSort
%   . groupBy' sameForm
%   . perms
%   $ [0 .. 3 :: Int]  -- $

% parts' :: Ord a => [a] -> [[[a]]]
% parts' = map (map MS.toList . MS.toList) . MS.partitions . MS.fromList

% sameForm :: [[a]] -> [[a]] -> Bool
% sameForm xs ys = eqLen xs ys && (and $ zipWith eqLen (lenSort xs) (lenSort ys))
%   where
%     eqLen = (==) `on` length

% lenSort = sortBy (comparing length)

% groupBy' :: (a -> a -> Bool) -> [a] -> [[a]]
% groupBy' _    []     = []
% groupBy' comp (x:rest) = (x:xs) : groupBy' comp ys
%   where (xs,ys) = partition (x `comp`) rest

% drawPermForm
%   = hcat' (with & sep .~ 0.2)
%   . map ((\l -> cyc' l 0.8) . map (const dot))
%   where
%     dot = circle labR # fc black

% drawPermRow ps = hcat' (with & sep .~ 2)
%     [ (map . map . const) () (head ps) # drawPermForm # alignR
%     , lPerms
%     ]
%   where
%     lPerms = hcat' (with & sep .~ 1) . map drawPerm $ ps

% dia = permForms
%   # lwO 0.7
%   # frame 0.5
%   \end{diagram}

%   \vspace{0.5in}
%   Leads to idea of \emph{unlabelled} species.
%   \todo{Use listing of unlabelled binary tree shapes, to line up with
%     previous slide}
%   \end{center}
  \end{overprint}

\end{frame}

\begin{frame}{Algebraic operations on species}
  \todo{Examples of algebraic operations: sum, product.  Then explain
    algebraic expression for tree.}
\end{frame}

\begin{frame}{Species, formally}
  A species $F$ consists of
  \begin{itemize}[<+->]
  \item a function sending finite sets of labels $L$ to sets of shapes
    $F\ L$
  \item a function sending bijections $\sigma : L \bij L'$ to
    relabellings $F\ L \to F\ L'$ (satisfying laws)
  \end{itemize}
\end{frame}

\begin{frame}{Species, even more formally}
  A species $F$ is a functor $F : \B \to \Set$. \medskip

  \onslide<2->
  \begin{itemize}
  \item $\B$: category of finite sets and bijections
  \item $\Set$: category of sets and total functions
  \end{itemize}
\end{frame}

\begin{frame}{Generalized species}
  \note{Idea: enumerate properties needed for each operation on
    species.  See dissertation for such an enumeration, and an
    exploration of some variant species.}
  \begin{center}
  \dots a \emph{generalized species} is a functor $\Lab \to \Str$? \bigskip

  What properties must $\Lab$ and $\Str$ have? \bigskip

  \onslide<2->
  See Chapter 3!
  \end{center}
\end{frame}

\section{Porting species to type theory}
\label{sec:species-to-type-theory}

\begin{frame}
  \begin{minipage}{0.33\linewidth}
    \begin{center}
      \emph{Combinatorics}
      \begin{gather*}
        1, 2, 3, 4, 5, \dots \\
        \sum_{n \geq 0} f_n \frac{x^n}{n!}
      \end{gather*}
      \includegraphics[width=0.75in]{BinTree}
    \end{center}
  \end{minipage}
  \begin{minipage}{0.23\linewidth}
    \begin{center}
      \todo{bridge}
    \end{center}
  \end{minipage}
  \begin{minipage}{0.33\linewidth}
    \begin{center}
      \emph{Programming Languages}
      \begin{gather*}
        \lam {f : \tau \to \tau} {\lam {a : \tau} {f \; a}}
      \end{gather*}
\begin{verbatim}
data Tree a
  = Empty | ...
\end{verbatim}
      \includegraphics[width=0.75in]{BinTree}
    \end{center}
  \end{minipage}
\end{frame}

\begin{frame}{The problem}
  \note{Fundamental mismatch! This turns out to be quite interesting/subtle.  A whole
    chapter of my dissertation.}

  \onslide<1->
    Like most mathematics, the theory of species
    \begin{itemize}
    \item uses classical logic
    \item is based on set theory
    \item is untyped
    \end{itemize} \bigskip

  \onslide<2->
    \dots but PL World
    \begin{itemize}
    \item uses constructive logic
    \item is based on type theory
    \item is typed.
    \end{itemize} \bigskip

  \onslide<3->
    Goal: encode species into a constructive type theory.
\end{frame}

\begin{frame}{Homotopy type theory (HoTT)}
  \note{HoTT: new theory, last few years.  HoTT book makes the claim
    that it is a good foundation for mathematics.  This is a good
    test!  Spoiler alert: it works really, really well.  In fact, I
    would go so far as to say that HoTT is fundamentally \emph{the
      right} framework for species, even more right than set theory!}

  \begin{center}
    \onslide<1->
    Recent variant type theory developed by Voevodsky \textit{et al.} \bigskip

    \onslide<2->
    Claim: HoTT makes a good (constructive!) foundation for
    mathematics. \bigskip

    \onslide<3-> \dots Let's try it!
  \end{center}
\end{frame}

\begin{frame}[fragile]{Equality in HoTT}
  \note{See my dissertation or the HoTT book for details.  Main
    takeaway: topological intuition for equality, \ie \emph{paths}.
    Equality can have \emph{computational content}.  Can still
    substitute equals for equals, but it might involve some work.}

  \begin{center}
  \begin{diagram}[width=200]
p, q :: P2
p = (-1) ^& 1
q = 2 ^& (-1)

spline :: Located (Trail R2)
spline = cubicSpline False [p, 0 ^& 0.5, 0.5 ^& (-0.8), q]

dot = circle 0.05 # fc black

textOffset = 0.3

dia = mconcat
  [ dot # moveTo p
  , dot # moveTo q
  , text "p" # moveTo p # translateX (-textOffset)
  , text "q" # moveTo q # translateX textOffset
  , text "=" # moveTo (spline `atParam` 0.5) # translateX textOffset
  , strokeLocT spline
  ]
  # fontSizeG 0.3
  # frame 0.5
  # lwO 0.7
  \end{diagram} \bigskip

  Topological intuition: equality is like a path (homotopy) in a
  space.  Equality can have \emph{computational content}.
  \end{center}
\end{frame}

\begin{frame}{Univalence}
  \note{In particular, this richer idea of what equality means allows
    one to handle isomorphism and equality in the same way.  This is
    exactly what we need for species---lots of \emph{bijections}
    floating around etc.}

  \[ (A = B) \equiv (A \equiv B) \] \bigskip

  \begin{center}
    Allows unifying equality and isomorphism---just what the doctor ordered
    for species!
  \end{center}
\end{frame}

\begin{frame}[fragile]{Finiteness}
  \note{Recall that a species maps from \emph{finite} sets of labels
    to sets of shapes.  The finiteness plays an important and
    explicitly computational role.  So we need to model finiteness
    constructively---this involves some nontrivial choices.}

  \begin{center}
    Species map \emph{finite sets} of labels to sets of shapes.  How
    to model finite sets in constructive type theory?
  \end{center}

  \begin{center}
    \begin{diagram}[width=300]
import           SpeciesDiagrams

set1 = hcat' (with & sep .~ 0.5) (map labT [0..4])
set2 = hcat' (with & sep .~ 0.5) (map labT [0..6] ++ [ellipsis])

ellipsis = hcat' (with & sep .~ 0.2) (replicate 3 (circle 0.1 # fc black))

noAngle = 30 @@@@ deg
noLen = 3
no = (hrule noLen # rotate noAngle <> hrule noLen # rotate (negateV noAngle))
   # lc red # lw (3 *^ veryThick)

dia =
  [ set1
  , no <> set2 # centerX
  ]
  # map centerX
  # vcat' (with & sep .~ 1)
  # frame 0.5 # lwO 0.7
    \end{diagram}
  \end{center}
\end{frame}

\begin{frame}{Cardinal-finiteness: first try}
    \begin{center}
      A set $A$ is \emph{cardinal-finite} if there exists some $n \in
      \N$ and a bijection $\{0, 1, \dots, n-1\} \bij A$.
    \end{center}

    \note{Define $\Fin{}$.  Define first stab at finiteness.}
    \todo{Picture of equivalence between $A$ and $\Fin n$.}

    \onslide<2->
    \[ \FinType \hdefeq (A : \Type) \times (n : \N) \times (\Fin n
    \equiv A) \]
\end{frame}

\begin{frame}[fragile]{Cardinal-finiteness: first try}
  \note{However, this doesn't work out the way we expect---it's too
    strong.  Having an isomorphism with $\Fin n$ actually gives you a
    lot more than just finiteness: it actually induces a linear order
    on the elements of $A$.  There's at most one path/equality between
    any two of these, because the linear order must be preserved.}

  \begin{center}
    But this is too strong!  There is \emph{at most one} isomorphism
    between two finite types.
  \begin{diagram}[width=150]
import           Data.Bits                      (xor)
import           SpeciesDiagrams

mkList n d f = hcat' (with & sep .~ 2 & catMethod .~ Distrib)
  (zipWith named (map f [0::Int ..]) (replicate n d))

n :: Int
n = 8

dia = decorateLocatedTrail (triangle (fromIntegral (n+2)) # rotateBy (1/2))
      [ "l1"  ||> (l1 # rotateBy (-1/3))
      , "fin" ||> fin
      , "l2"  ||> (l2 # rotateBy (1/3))
      ]
      # mkConnections
      # centerXY # pad 1.2
      # flip appends
        [ (unit_Y                  , text' 4 "Fin n")
        , (unit_Y # rotateBy (-1/3), text' 4 "A₁"   )
        , (unit_Y # rotateBy (1/3) , text' 4 "A₂"   )
        ]
      # lwO 0.7
  where
    fin = mkList n dot (`xor` 1) # centerXY
    l1  = mkList n dot id # centerXY
    l2  = mkList n dot ((n-1) -) # centerXY
    dot = circle 0.5 # fc grey
    mkConnections = applyAll
      [  withNames [a .> i, b .> i] $ \[p,q] -> atop (location p ~~ location q)
      || (a,b) <- take 3 . (zip <*> tail) . cycle $ ["l1", "fin", "l2"]
      ,  i <- [0 .. (n-1)]
      ]
  \end{diagram}
  \end{center}
\end{frame}

\begin{frame}{Propositional truncation to the rescue}
  \note{Define \emph{propositional truncation}. Note the enhanced
    notion of equality makes this possible.  Simple example of
    ``higher inductive type''.  We can then define a variant of
    cardinal-finiteness using it.  Now an isomorphism between two of
    these no longer has the problem.  Akin to existential: once we
    ``seal up'' the existential package it's OK to consider them equal
    since we can't get the info back out again.  But we still need it
    sometimes!  The induction principle gives us a principled way to
    make this all work.}

  Given a type $A$, its \emph{propositional truncation} $\ptrunc{A}$
  is like $A$, except (by fiat) all inhabitants are considered equal.

  \onslide<2->
  \[ \FinTypeT \hdefeq (A : \Type) \times \ptrunc{(n : \N) \times
    (\Fin n \equiv A)} \]

  \onslide<3->
  Akin to using an existential type:
  \[ (A : \Type) \times (\exist {n : \N} \Fin n \equiv A) \]

  \onslide<4-> \dots but the \emph{induction principle} for
  $\ptrunc{A}$ still allows the contents to be used in ways that do
  not ``leak'' information.
\end{frame}

\begin{frame}{Propositional truncation to the rescue}
  \note{HoTT is an ideal type system for species.  Anything with the
    right type is automatically valid!  By contrast, in set theory it
    is possible to write down functions which are not functorial; all
    definable functions of the right type are automatically functorial
    in HoTT.}

  We can use $\FinTypeT$ to make a HoTT analogue of $\B$, which
  \begin{itemize}
  \item seems to have all the right properties
  \item yields insight into the mathematics (equipotence, $\L$-species).
  \end{itemize} \bigskip

  In HoTT, it is \emph{impossible to write down invalid species}.
\end{frame}

\begin{frame}{More\dots}
  See dissertation for:
  \begin{itemize}
  \item How HoTT solves other issues (\eg axiom of choice)
  \item \todo{What else?}
  \end{itemize}
\end{frame}

% \begin{frame}
%   \todo{Should I put something in here about framework for categorical
%     properties and species variants?}
% \end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Labelled structures}
\label{sec:labelled}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}[fragile]{Data structure = shape + data}
  \begin{center}
    A species gives us \emph{labelled shapes}.  To make a \emph{data
      structure} we pair a shape with a mapping from labels to data
    values. \bigskip

\begin{diagram}[width=300]
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
  \end{center}
  \[ F\ L \times (L \to A) \]
\end{frame}

\begin{frame}{Analytic functors}
  The labels ``shouldn't matter'' so we quotient by relabelling:
  \[ \analytic F\ A \defeq \coend L F\ L \times (L \to A) \]

  \onslide<2->
  $\analytic F$ is an \emph{analytic functor} (Joyal, 1986). \medskip

  \onslide<3-> Analytic functors:
  \begin{itemize}
  \item<4-> correspond to generating functions
  \item<5-> are closed under many operations of interest (sum,
    product, fixed point \dots)
  \item<6-> can be defined via \emph{Kan extensions}
  \item<7-> correspond to $\Sigma$-types in HoTT
  \end{itemize}
\end{frame}

\begin{frame}{Labels as memory addresses}
  \todo{Make a slide about this.}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusions and future work}
\label{sec:future}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}
  \todo{My proposal turned out to be a 5- or 10-year research
    program!  This is a good start.}
\end{frame}

\begin{frame}{Future work}
  \begin{itemize}
  \item Future thing!
  \item Other future thing!
  \end{itemize}
  \todo{finish}
\end{frame}

\end{document}
