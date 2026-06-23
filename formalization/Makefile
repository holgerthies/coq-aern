# Build driver for the Rocq project (Rocq 9.0+).
# Override on the command line for older Coq, e.g. `make ROCQMAKEFILE=coq_makefile`.
ROCQMAKEFILE ?= rocq makefile

%: Makefile.coq

Makefile.coq: _CoqProject
	$(ROCQMAKEFILE) -f _CoqProject -o Makefile.coq

tests: all
	@$(MAKE) -C tests -s clean
	@$(MAKE) -C tests -s all

-include Makefile.coq
