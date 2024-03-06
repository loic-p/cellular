.PHONY: all latexmk clean

all: abstract.tex refs.bib
	rubber -d abstract.tex

latexmk: abstract.tex refs.bib
	latexmk -pdfxe abstract.tex

# pdflatex: abstract.tex refs.bib
# 	latexmk -pdf abstract.tex

# quick: abstract.tex
# 	xelatex $<

clean:
	rubber --clean abstract.tex
	rm paper.pdf paper.ptb paper.vtc 2> /dev/null || true
	find . -type f -name '*.agdai' -delete
	rm -rf agda/latex/
