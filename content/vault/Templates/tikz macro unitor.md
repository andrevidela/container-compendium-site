```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\providecommand{\unitordiagram}[6]{
  \begin{tikzcd}[ampersand replacement=\&]
    {#1}
    \\ \\
    {#2} \&\& {#3}
    \arrow["{#4}"', from=1-1, to=3-1]
    \arrow["{#5}", from=1-1, to=3-3]
    \arrow["{#6}"', from=3-1, to=3-3]
  \end{tikzcd}
} 
\begin{document}
\unitordiagram
{topnode} % top node
{cornernode} % bottom left corner node
{rightnode} % right node
{leftarrow} % left arrow
{diagarrow} % diagonal arrow
{botarrow} % bottom arrow
\end{document}
```