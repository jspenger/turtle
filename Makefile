# SPDX-License-Identifier: Apache-2.0 OR MIT

SUBDIRS := \
	turtle-tla \
	turtle-tla-lib \
	turtle-compat/sail-riscv \
	examples/01-turtle-tla-hour-clock \
	examples/02-turtle-tla-proof-rules \
	examples/03-turtle-compat-sail-riscv-print32 \
	examples/04-turtle-compat-sail-riscv-fibonacci

.PHONY: subdirs $(SUBDIRS)

.DEFAULT_GOAL := subdirs

subdirs: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@ $(MAKECMDGOALS)

turtle-tla-lib : turtle-tla
turtle-compat/sail-riscv : turtle-tla
examples/01-turtle-tla-hour-clock : turtle-tla-lib
examples/02-turtle-tla-proof-rules : turtle-tla-lib
examples/03-turtle-compat-sail-riscv-print32 : turtle-compat/sail-riscv
examples/04-turtle-compat-sail-riscv-fibonacci : turtle-compat/sail-riscv

Makefile: ;

%: subdirs
	@:
