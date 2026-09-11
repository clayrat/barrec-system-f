COQMAKEFILE ?= coq_makefile

.PHONY: all rocq extract demo check bench-help clean
all: rocq

Makefile.coq: _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o $@

rocq: Makefile.coq
	$(MAKE) -f Makefile.coq

extract:
	$(MAKE) -C extraction extract

demo:
	$(MAKE) -C extraction run

check: demo

bench-help:
	python3 bench/run.py --help

clean:
	@if test -f Makefile.coq; then $(MAKE) -f Makefile.coq clean; fi
	$(MAKE) -C extraction clean
