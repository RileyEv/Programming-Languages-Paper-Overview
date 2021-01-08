lhs2TeX main.lhs > main.tex
texfot --no-stderr latexmk -interaction=nonstopmode -pdf -no-shell-escape -bibtex -jobname=main main.tex
