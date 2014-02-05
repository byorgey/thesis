% -*- mode: LaTeX; compile-command: "mk" -*-

%include polycode.fmt

% Use 'arrayhs' mode, so code blocks will not be split across page breaks.
\arrayhs

\renewcommand{\Conid}[1]{\mathsf{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Package imports

\usepackage{amsmath}
\usepackage{brent}
\usepackage[all,cmtip]{xy}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Math typesetting

\renewcommand{\False}{\cons{F}}
\renewcommand{\True}{\cons{T}}

\newcommand{\FinSet}{\ensuremath{\mathbf{FinSet}}}
\newcommand{\I}{\ensuremath{\mathcal{I}}}

\newcommand{\universe}{\ensuremath{\mathcal{U}}}
\newcommand{\defeq}{\mathrel{:\equiv}}
\newcommand{\dep}[1]{\prod_{#1}}
\newcommand{\fun}[1]{\lambda #1.\ }

\newcommand{\param}{\mathord{-}}

\newcommand{\unl}[1]{\widetilde{#1}}
