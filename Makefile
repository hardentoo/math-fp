PYTHON	 = /usr/bin/python
PRESENT	 = /Applications/Misc/Présentation.app/Contents/MacOS/presentation.py
PDF	 = math-abstractions.pdf
IMAGES	 = images/Codomain2.pdf
COQFLAGS = "-I $(HOME)/src/category-theory/Endo"

all: $(IMAGES) $(PDF) Makefile.coq html
	make -f Makefile.coq COQFLAGS=$(COQFLAGS)

open: $(PDF)
	open $<

present: all
	$(PYTHON) $(PRESENT) $(PDF)

html: Makefile.coq
	make -f Makefile.coq COQFLAGS=$(COQFLAGS) html

Makefile.coq: src/*.v
	coq_makefile  . src/*.v > Makefile.coq
	sed -i '149,150d' Makefile.coq

images/%.png: images/%.svg
	rsvg-convert -f png -w 800 -h 600 -o $@ $<

images/%.pdf: images/%.svg
	rsvg-convert -f pdf -o $@ $<

%.tex: %.org
	emacs -batch -L ~/.emacs.d \
	    -l init -l settings -l org-settings -l ox-beamer \
	    --eval="(progn (find-file \"$<\") (org-beamer-export-to-latex))"

%.pdf: %.tex
	pdflatex $<
	pdflatex $<
	pdflatex $<

clean:
	rm -fr html
	rm -f *.tex *.pdf *.vrb *.aux *.log *.nav *.out *.snm *.toc *.upa
	rm -f src/*.d src/*.vo src/*.glob Makefile.coq
