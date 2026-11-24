# SPDX-License-Identifier: Apache-2.0 OR MIT

MAKEFILE_COQ := Makefile.coq

ifneq ($(shell command -v $(COQBIN)rocq 2>/dev/null),)
  COQMAKEFILE := $(COQBIN)rocq makefile
else
  COQMAKEFILE := $(COQBIN)coq_makefile
endif

.PHONY: submake

.DEFAULT_GOAL := submake

submake: $(MAKEFILE_COQ)
	$(MAKE) --no-print-directory -f $(MAKEFILE_COQ) $(filter-out $(MAKEFILE_COQ),$(MAKECMDGOALS))

$(MAKEFILE_COQ): Makefile _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o $(MAKEFILE_COQ)

Makefile: ;
_CoqProject: ;

%: submake
	@:
