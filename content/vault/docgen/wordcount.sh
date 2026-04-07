sed '/\\begin{Verbatim}/,/\\end{Verbatim}/d' $1 | detex | wc -w
