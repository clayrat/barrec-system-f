COQC ?= coqc
DUNE ?= dune

.PHONY: all core extract audit run clean
all: run

core:
	$(MAKE) -C .. rocq

extract: core
	$(COQC) -Q ../theories SystemF Extract.v

audit: extract
	python3 audit.py

run: audit
	$(DUNE) exec ./main.exe

clean:
	rm -f systemf.ml systemf.mli *.vo *.vos *.vok *.glob .*.aux
	$(DUNE) clean
