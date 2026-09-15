COQMAKEFILE ?= coq_makefile

.PHONY: all rocq extract demo hm church brec-demo reference check normalization-oracle hm-evil bench-help clean
all: rocq

Makefile.coq: _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o $@

rocq: Makefile.coq
	$(MAKE) -f Makefile.coq

extract:
	$(MAKE) -C extraction extract

demo:
	$(MAKE) -C extraction run

hm:
	$(MAKE) -C extraction hm

church:
	$(MAKE) -C extraction church

brec-demo:
	$(MAKE) -C extraction brec-demo

reference:
	ocaml reference/systemf_native.ml

check: demo reference

normalization-oracle:
	$(MAKE) -C extraction normalization-oracle

hm-evil:
	$(MAKE) -C extraction hm-evil

bench-help:
	python3 bench/run.py --help

clean:
	@if test -f Makefile.coq; then $(MAKE) -f Makefile.coq clean; fi
	$(MAKE) -C extraction clean
