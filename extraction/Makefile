COQC ?= coqc
DUNE ?= dune

.PHONY: all core extract run clean
all: run

core:
	$(MAKE) -C .. rocq

extract: core
	$(COQC) -Q ../theories SystemF Extract.v

run: extract
	$(DUNE) exec ./main.exe

clean:
	rm -f systemf.ml systemf.mli *.vo *.vos *.vok *.glob .*.aux
	$(DUNE) clean
