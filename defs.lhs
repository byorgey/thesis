% -*- mode: LaTeX; compile-command: "mk" -*-

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Haskell typesetting

%include thesis.fmt

% Use 'arrayhs' mode, so code blocks will not be split across page breaks.
\arrayhs

\renewcommand{\Conid}[1]{\mathsf{#1}}

\newcommand{\mappend}{\diamond}
\newcommand{\mempty}{\varepsilon}

\renewcommand{\onelinecomment}[1]{--- {#1}}

\newcommand{\pkg}[1]{\texttt{#1}}

\newcommand{\Int}{\cons{Int}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Package imports

\usepackage{amsmath}
\usepackage{amssymb}
%\usepackage{amsthm}
\usepackage[amsmath,amsthm,thmmarks]{ntheorem}
\usepackage{mathtools}
\usepackage{stmaryrd}
\usepackage[all,cmtip,2cell]{xy}
\UseAllTwocells
\usepackage{xcolor}
\usepackage{prettyref}
\usepackage{xspace}
\usepackage{url}
\usepackage{footmisc}
\usepackage{enumitem}
\usepackage{verse}

\usepackage[final]{showkeys}

% \usepackage{breakurl}
\usepackage{natbib}

\usepackage{graphicx}
\graphicspath{{images/}}
\usepackage[outputdir=diagrams,backend=cairo,extension=pdf]{diagrams-latex}

\usepackage[top=1in, bottom=1in, left=1.5in, right=1in,includefoot,paperwidth=8.5in,paperheight=11in]{geometry}
\usepackage{setspace}

\usepackage[pdftex]{hyperref}
\hypersetup{
    pdftitle={\Title},
    pdfauthor={Brent Yorgey},
    bookmarksnumbered=true,
    bookmarksopen=true,
    bookmarksopenlevel=1,
    hidelinks,
    naturalnames=true,
    pdfstartview=Fit,
    pdfpagemode=UseOutlines,
    pdfpagelayout=TwoPageRight
}

\usepackage{doi}

\usepackage{fancyhdr}
\lfoot[\fancyplain{}{}]{\fancyplain{}{}}
\rfoot[\fancyplain{}{}]{\fancyplain{}{}}
\cfoot[\fancyplain{}{\footnotesize\thepage}]{\fancyplain{}{\footnotesize\thepage}}
\lhead[\fancyplain{}{}]{\fancyplain{}{}}
\rhead[\fancyplain{}{}]{\fancyplain{}{}}
\ifdraft
\chead[\fancyplain{}{\textbf{DRAFT ---
    \today}}]{\fancyplain{}{\textbf{DRAFT --- \today}}}
\fi
\renewcommand{\headrulewidth}{0pt}
\setlength{\headheight}{15pt}

\newcommand{\signature}{~ \\ \underline{\hspace{20em}}}

\newenvironment{pagecentered}{%
\vspace*{\stretch{2}}%
\begin{center}%
\begin{minipage}{.8\textwidth}%
}{%
\end{minipage}%
\end{center}%
\vspace*{\stretch{3}}\clearpage}

\newcommand{\nochapter}[1]{%
  \refstepcounter{chapter}%
  \addcontentsline{toc}{chapter}{#1}%
  \markright{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage[utf8x]{inputenx}
\ifgreek
\usepackage[polutonikogreek,english]{babel}
\fi

\usepackage{defs}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% SDG qed symbol

\font\tinyfont=cmss10 scaled 375

% This is for the amsthm package
% \let\oldqedsymbol\qedsymbol
% \renewcommand{\qedsymbol}{\rlap\oldqedsymbol{}\raise
%   .5ex\hbox{\tinyfont \hskip .3em S\kern-.15em D\kern -.15em G}}

% Now I'm using the ntheorem package with amsthm option
\let\oldproofSymbol\proofSymbol
\renewcommand{\proofSymbol}{\rlap\oldproofSymbol{}\raise
  .5ex\hbox{\tinyfont \hskip .3em S\kern-.15em D\kern -.15em G}}
