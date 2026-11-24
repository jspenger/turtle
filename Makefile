# SPDX-License-Identifier: Apache-2.0 OR MIT

SUBDIRS := \
	turtle-tla \
	turtle-tla-lib \
	examples/01-hour-clock \
	examples/02-proof-rules

.PHONY: subdirs $(SUBDIRS)

.DEFAULT_GOAL := subdirs

subdirs: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@ $(MAKECMDGOALS)

turtle-tla-lib : turtle-tla
examples/01-hour-clock : turtle-tla-lib
examples/02-proof-rules : turtle-tla-lib

Makefile: ;

%: subdirs
	@:
