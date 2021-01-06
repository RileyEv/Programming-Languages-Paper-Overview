lhs2tex main.lhs > main.tex

xelatex main
biber main
xelatex main
