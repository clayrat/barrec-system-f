COQC ?= coqc
DUNE ?= dune

.PHONY: all core extract audit run hm church brec-demo normalization-oracle hm-evil clean
all: run

core:
	$(MAKE) -C .. rocq

extract: core
	$(COQC) -Q ../theories SystemF Extract.v

audit: extract
	python3 audit.py
	$(DUNE) build ./normalization_oracle.exe ./hm_evil.exe ./main.exe

run: audit
	$(DUNE) exec ./main.exe

HM_SOURCE ?= let id = fun x -> x in id id
hm: audit
	$(DUNE) exec ./main.exe -- --hm "$(HM_SOURCE)"

CHURCH_SOURCE ?= Lambda X. fun (x : X) -> x
church: audit
	$(DUNE) exec ./main.exe -- --church "$(CHURCH_SOURCE)"

brec-demo: audit
	$(DUNE) exec ./main.exe -- --brec-only

ORACLE_ARGS ?= --case term1 --eval-cap 100
normalization-oracle: audit
	$(DUNE) exec ./normalization_oracle.exe -- $(ORACLE_ARGS)

HM_EVIL_ARGS ?= --variant poly --depth 3
hm-evil: audit
	$(DUNE) exec ./hm_evil.exe -- $(HM_EVIL_ARGS)

clean:
	rm -f systemf.ml systemf.mli *.vo *.vos *.vok *.glob .*.aux
	$(DUNE) clean
