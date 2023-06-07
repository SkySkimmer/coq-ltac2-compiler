MAKE_OPTS:= --no-builtin-rules

TEST_GOALS:=$(filter test%, $(MAKECMDGOALS))

.PHONY: submake
submake: Makefile.coq
	$(MAKE) $(MAKE_OPTS) -f Makefile.coq $(filter-out test%, $(MAKECMDGOALS))
	+$(if $(TEST_GOALS),$(MAKE) $(MAKE_OPTS) -C tests $(patsubst tests/%,%,$(filter-out test, $(TEST_GOALS))))

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@

%:: submake ;

# known sources

Makefile: ;

_CoqProject: ;
