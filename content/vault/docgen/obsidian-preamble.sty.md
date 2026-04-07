\newcommand{\of}{\text{ }}
\newcommand{\cat}[1]{\mathcal{#1}}
\usepackage{stmaryrd}
\usepackage[utf8]{inputenc}
\usepackage{mathabx}
\usepackage{tikz}
\usepackage{amsmath}
\usepackage{pgfkeys}
\usepackage{stmaryrd}
\usepackage{mathtools}


% `tikz-cd` is necessary to draw commutative diagrams.
\RequirePackage{tikz-cd}
% `amssymb` is necessary for `\lrcorner` and `\ulcorner`.
\RequirePackage{amssymb}
% `calc` is necessary to draw curved arrows.
\usetikzlibrary{calc}
% `pathmorphing` is necessary to draw squiggly arrows.
\usetikzlibrary{decorations.pathmorphing}
% \definecolor{amethyst}{rgb}{0.6, 0.4, 0.8}

\newcommand{\aaa}{a}

%bind operator for haskell-like programs >>=
\newcommand{\bind}{\mathbin{\gg\!\!=}}
\newcommand{\kleisli}{\mathbin{\gt\!\!=\!\!\gt}}

\newcommand{\Poly}{\cat{Poly}}
\newcommand{\Cont}{\cat{Cont}}
\newcommand{\Set}{\cat{Set}}
\newcommand{\ContCart}{\cat{Cont}^{\#}}
\DeclareUnicodeCharacter{25CB}{$\circ$}
\newcommand{\mor}[3]{\mathcal{#1}(#2, #3)}  % morphisms
\newcommand{\comp}{\mathbin{;}}
\newcommand{\ncomp}[1]{\mathbin{;_#1}}
\newcommand{\vcomp}{\mathbin{;_v}}
\newcommand{\hcomp}{\

% The traditional composition
\newcommand{\compose}{\rhd}
% The "universal composition" monoidal action
\newcommand{\forallSeq}{\mathbin{\blacktriangleright}}
\newcommand{\UnivComp}{\forallSeq}
% lenses


% \NeedsTeXFormat{LaTeX2e}
% \ProvidesPackage{quiver}[2021/01/11 quiver]

\usetikzlibrary{graphs}
\usetikzlibrary{arrows.meta}

\makeatletter

\newcommand{\thickarrow}{\mathrel{\Rightarrow\mkern-14mu\Rightarrow}}

\newcommand*{\RightArrow}{\mathrel{\mathpalette{\@RightArrow}{}}}
\newcommand*{\@RightArrow}[1]{%
    % Get the line width for this math style
    \edef\@LineWidth{%
        \the\fontdimen8
        \ifx#1\displaystyle\textfont
        \else\ifx#1\textstyle\textfont
        \else\ifx#1\scriptstyle\scriptfont
        \else\scriptscriptfont
        \fi\fi\fi
        3}
    \edef\@ScaleWidth{%
        \ifx#1\displaystyle0.39
        \else\ifx#1\textstyle0.39
        \else\ifx#1\scriptstyle0.35
        \else0.31
        \fi\fi\fi}
    \text{$\tikz
    \draw[double equal sign distance, line width=\@LineWidth,
    -{Implies[sep=-0.5ex] . Computer Modern Rightarrow[scale width=\@ScaleWidth, scale length=0.8]}]
    (0,0) -- (1.5em,0);$}}
\newcommand*{\Implies}{\DOTSB\;\RightArrow\;}

\pgfkeys{
  /pentagon/.cd,
  node top left/.code={\def\penttopleft{#1}},
  node top right/.code={\def\penttopright{#1}},
  node mid left/.code={\def\pentmidleft{#1}},
  node bottom left/.code={\def\pentbottomleft{#1}},
  node bottom right/.code={\def\pentbottomright{#1}},
  arrow top/.code={\def\penttop{#1}},
  arrow left/.code={\def\pentleft{#1}},
  arrow right/.code={\def\pentright{#1}},
  arrow bottom left/.code={\def\pentbottomleftarrow{#1}},
  arrow bottom right/.code={\def\pentbottomrightarrow{#1}},
}

% Initialize all macros to avoid undefined errors
\def\penttopleft{}
\def\penttopright{}
\def\pentmidleft{}
\def\pentbottomleft{}
\def\pentbottomright{}
\def\penttop{}
\def\pentleft{}
\def\pentright{}
\def\pentbottomleftarrow{}
\def\pentbottomrightarrow{}

\newcommand{\pentagondiagram}[1]{%
  \pgfkeys{/pentagon/.cd, #1}%
  \begin{tikzcd}[ampersand replacement=\&]
    {\penttopleft} \& \& {\penttopright} \\
    {\pentmidleft} \& \& {} \\
    {\pentbottomleft} \& \& {\pentbottomright}
    \arrow[from=1-1, to=1-3, "\penttop"]
    \arrow[from=1-1, to=2-1, "\pentleft"]
    \arrow[from=1-3, to=3-3, "\pentright"]
    \arrow[from=2-1, to=3-1, "\pentbottomleftarrow"]
    \arrow[from=3-1, to=3-3, "\pentbottomrightarrow"]
  \end{tikzcd}
}

\newcommand{\unitordiagram}[6]{
    {#1}
    \\ \\
    {#2} \&\& {#3}
    \arrow["{#4}"', from=1-1, to=3-1]
    \arrow["{#5}", from=1-1, to=3-3]
    \arrow["{#6}"', from=3-1, to=3-3]
}

\newcommand{\biglens}[4]{
\draw (0,0) rectangle (5, 3);
\draw [->] (5,0.5) -- (6, 0.5);
\node [anchor=west] at (6,0.5)  {#1}; % sub-solution
\draw [<-](5,2.5) -- (6, 2.5);
\node [anchor=west] at (6,2.5)  {#2}; % sub-problem
\draw [->](-1, 0.5) -- (0, 0.5);
\node [anchor=east] at (-1,0.5)  {#3}; % overall solution
\draw [<-](-1, 2.5) -- (0, 2.5) ;
\node [anchor=east] at (-1,2.5)  {#4}; % original problem
}

% A TikZ style for curved arrows of a fixed height, due to André.
\tikzset{curve/.style={settings={#1},to path={(\tikztostart)
    .. controls ($(\tikztostart)!\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
    and ($(\tikztostart)!1-\pv{pos}!(\tikztotarget)!\pv{height}!270:(\tikztotarget)$)
    .. (\tikztotarget)\tikztonodes}},
    settings/.code={\tikzset{quiver/.cd,#1}
        \def\pv##1{\pgfkeysvalueof{/tikz/quiver/##1}}},
    quiver/.cd,pos/.initial=0.35,height/.initial=0}

% TikZ arrowhead/tail styles.
\tikzset{tail reversed/.code={\pgfsetarrowsstart{tikzcd to}}}
\tikzset{2tail/.code={\pgfsetarrowsstart{Implies[reversed]}}}
\tikzset{2tail reversed/.code={\pgfsetarrowsstart{Implies}}}
% TikZ arrow styles.
\tikzset{no body/.style={/tikz/dash pattern=on 0 off 1mm}}

% \endinput