% -*- mode: LaTeX; compile-command: "mk" -*-

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Haskell typesetting

%include thesis.fmt

% Use 'arrayhs' mode, so code blocks will not be split across page breaks.
\arrayhs

\renewcommand{\Conid}[1]{\mathsf{#1}}

\newcommand{\mappend}{\diamond}
\newcommand{\mempty}{\varepsilon}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Package imports

\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{stmaryrd}
\usepackage[all,cmtip]{xy}
\usepackage{xcolor}
\usepackage{prettyref}
\usepackage{xspace}

% \usepackage{breakurl}
\usepackage{natbib}

\usepackage{graphicx}
\usepackage[outputdir=diagrams,backend=ps,extension=eps]{diagrams-latex}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Declarative formatting

\newcommand{\term}[1]{\emph{#1}}
\newcommand{\latin}[1]{\textit{#1}\ }
\newcommand{\foreign}[1]{\emph{#1}}

\newcommand{\ie}{\latin{i.e.}}
\newcommand{\eg}{\latin{e.g.}}
\newcommand{\etal}{\latin{et al.}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Math typesetting

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% General math

\newcommand{\bbb}[1]{\ensuremath{\mathbb{#1}}}
\providecommand{\N}{\bbb{N}}
\providecommand{\Z}{\bbb{Z}}
\providecommand{\Q}{\bbb{Q}}
\providecommand{\R}{\bbb{R}}
\providecommand{\C}{\bbb{C}}

\newcommand{\mcal}[1]{\ensuremath{\mathcal{#1}}}
\let\Sect\S
\renewcommand{\S}{\mcal S}
\renewcommand{\H}{\mcal H}
\newcommand{\I}{\mcal I}
\newcommand{\Sym}{\mcal S}

\newcommand{\msf}[1]{\ensuremath{\mathsf{#1}}\xspace}

\newcommand{\param}{\mathord{-}}

\newcommand{\comp}{\mathbin{\circ}}
\newcommand{\union}{\cup}
\newcommand{\Union}{\bigcup}
\newcommand{\intersect}{\cap}
\newcommand{\Intersect}{\bigcap}

\newcommand{\floor}[1]{\left\lfloor #1 \right\rfloor}
\newcommand{\ceil}[1]{\left\lceil #1 \right\rceil}

\newcommand{\bij}{\stackrel{\sim}{\longrightarrow}}
\newcommand{\iso}{\simeq}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Theorems etc.

\newtheorem{thm}{Theorem}[section]
\newtheorem{prop}[thm]{Proposition}
\newtheorem{lem}[thm]{Lemma}
\newtheorem{cor}[thm]{Corollary}

\theoremstyle{definition}
\newtheorem{defn}[thm]{Definition}

\theoremstyle{remark}
\newtheorem*{rem}{Remark}
\newtheorem*{ex}{Example}
\newtheorem*{nota}{Notation}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Type theory

\newcommand{\universe}{\mcal{U}}
\newcommand{\defeq}{\mathrel{:\equiv}}
\newcommand{\dep}[1]{\prod_{#1}}
\newcommand{\fun}[1]{\lambda #1.\ }

\newcommand{\cons}[1]{\mathsf{#1}}

\renewcommand{\False}{\cons{F}}
\renewcommand{\True}{\cons{T}}

\newcommand{\Type}{\ensuremath{\mathcal{U}}}
\newcommand{\FinType}{\ensuremath{\Type_{\text{Fin}}}}
\newcommand{\FinTypeT}{\ensuremath{\Type_{\||\text{Fin}\||}}}
\newcommand{\size}[1]{\ensuremath{\##1}}

\newcommand{\Fin}[1]{\ensuremath{\cons{Fin}\ #1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% HoTT

\newcommand{\ptrunc}[1]{\ensuremath{\||#1\||}}
\newcommand{\id}{\cons{id}}

\newcommand{\tygrpd}[1]{\ensuremath{\mathbf{G}(#1)}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Category theory

\newcommand{\cat}[1]{\ensuremath{\mathbf{#1}}\xspace}
\newcommand{\Set}{\cat{Set}}

\newcommand{\mor}[2]{\ensuremath{#1 \longrightarrow #2}}
\newcommand{\nat}[2]{\ensuremath{#1 \stackrel{\bullet}{\longrightarrow} #2}}

\newcommand{\then}{\mathbin{;}}

\providecommand{\B}{\bbb{B}}
\renewcommand{\P}{\bbb{P}}
\providecommand{\FinSet}{\bbb{E}}

\newcommand{\BT}{\B_H}
\newcommand{\PT}{\P_H}

\newcommand{\fin}[1]{\ensuremath{[#1]}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Species

\renewcommand{\Sp}{\msf}
\newcommand{\X}{\Sp{X}}
\newcommand{\Y}{\Sp{Y}}
\newcommand{\E}{\Sp{E}}
\newcommand{\F}{\Sp{F}}
\newcommand{\G}{\Sp{G}}
\renewcommand{\L}{\Sp{L}}
\newcommand{\T}{\Sp{T}}
\newcommand{\Par}{\Sp{Par}}
\newcommand{\Bag}{\Sp{E}}
\newcommand{\Cyc}{\Sp{C}}

\newcommand{\Zero}{\msf{0}}
\newcommand{\One}{\msf{1}}

\newcommand{\sprod}{\cdot}
\newcommand{\fcomp}{\mathbin{\square}}

\providecommand{\comp}{\circ}

\newcommand{\usum}{\boxplus}
\newcommand{\uprod}{\boxtimes}
\newcommand{\ucomp}{\boxcircle}

\newcommand{\unl}[1]{\widetilde{#1}}

\newcommand{\Lab}{\bbb{L}}
\newcommand{\Str}{\bbb{S}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Comments

\newif\ifcomments\commentstrue

\ifcomments
\newcommand{\authornote}[3]{\textcolor{#1}{[#3 ---#2]}}
\newcommand{\todo}[1]{\textcolor{red}{[TODO: #1]}}
\else
\newcommand{\authornote}[3]{}
\newcommand{\todo}[1]{}
\fi

\newcommand{\bay}[1]{\authornote{blue}{BAY}{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Prettyref

\newrefformat{fig}{Figure~\ref{#1}}
\newrefformat{sec}{\Sect\ref{#1}}
\newrefformat{eq}{equation~\eqref{#1}}
\newrefformat{prob}{Problem~\ref{#1}}
\newrefformat{tab}{Table~\ref{#1}}
\newrefformat{thm}{Theorem~\ref{#1}}
\newrefformat{lem}{Lemma~\ref{#1}}
\newrefformat{prop}{Proposition~\ref{#1}}
\newrefformat{defn}{Definition~\ref{#1}}
\newrefformat{cor}{Corollary~\ref{#1}}

% memoir defines pref and Pref as 'pageref'
\providecommand{\pref}{}
\renewcommand{\pref}[1]{\prettyref{#1}}

% \Pref is just like \pref but it uppercases the first letter; for use
% at the beginning of a sentence.
\providecommand{\Pref}{}
\renewcommand{\Pref}[1]{%
  \expandafter\ifx\csname r@@#1\endcsname\relax {\scriptsize[ref]}
    \else
    \edef\reftext{\prettyref{#1}}\expandafter\MakeUppercase\reftext
    \fi
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Proofs

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Structured proofs

\newenvironment{sproof}{%
    \begin{tabbing}
    \phantom{$\equiv$} \= \qquad\qquad\qquad\qquad\qquad \= \kill
}{
    \end{tabbing}
}
\newcommand{\stmt}[1]{\> \ensuremath{#1} \\}
\newcommand{\lstmt}[1]{\> \ensuremath{#1} }
\newcommand{\reason}[2]{\ensuremath{#1} \>\> \{ \quad #2 \quad \} \\}

\newcommand{\subpart}[1]{\llcorner #1 \lrcorner}
\newcommand{\suppart}[1]{\ulcorner #1 \urcorner}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% SDG qed symbol

\font\tinyfont=cmss10 scaled 375
\let\oldqedsymbol\qedsymbol
\renewcommand{\qedsymbol}{\rlap\oldqedsymbol{}\raise
  .5ex\hbox{\tinyfont \hskip .3em S\kern-.15em D\kern -.15em G}}
