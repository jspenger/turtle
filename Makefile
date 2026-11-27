# SPDX-License-Identifier: Apache-2.0 OR MIT

SUBDIRS := \
	turtle-tla \
	turtle-tla-lib \
	turtle-compat/sail-riscv \
	turtle-gen \
	examples/01-turtle-tla-hour-clock \
	examples/02-turtle-tla-proof-rules \
	examples/03-turtle-compat-sail-riscv-print32 \
	examples/04-turtle-compat-sail-riscv-fibonacci

.PHONY: subdirs $(SUBDIRS)

.DEFAULT_GOAL := subdirs

subdirs: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@ $(MAKECMDGOALS)

turtle-tla-lib : turtle-tla turtle-gen
turtle-compat/sail-riscv : turtle-tla
turtle-gen : turtle-compat/sail-riscv
examples/01-turtle-tla-hour-clock : turtle-tla-lib turtle-gen
examples/02-turtle-tla-proof-rules : turtle-tla-lib turtle-gen
examples/03-turtle-compat-sail-riscv-print32 : turtle-compat/sail-riscv turtle-gen
examples/04-turtle-compat-sail-riscv-fibonacci : turtle-compat/sail-riscv turtle-gen

Makefile: ;

%: subdirs
	@:
