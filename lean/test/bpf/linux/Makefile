CURDIR := $(abspath .)
TOOLSDIR := $(abspath ./tools)
LIBDIR := $(TOOLSDIR)/lib
TOOLSINCDIR := $(TOOLSDIR)/include
APIDIR := $(TOOLSINCDIR)/uapi
GENDIR := $(abspath ./include/generated)
INCLUDE_DIR := $(abspath ./usr/include)

ARCHMOD=

ifeq ($(shell uname),Darwin)
ifeq ($(shell uname -p),arm)
ARCHMOD=arch -x86_64
endif
endif

gen-tests: make_verifier_tests
	./make_verifier_tests

verifier/tests.h: FORCE
	$(shell ( cd verifier/; \
		  echo '/* Generated header, do not edit */'; \
		  echo '#ifdef FILL_ARRAY'; \
		  ls *.c 2> /dev/null | sed -e 's@\(.*\)@#include \"\1\"@'; \
		  echo '#endif' \
		) > verifier/tests.h)

make_verifier_tests: make_verifier_tests.c verifier/tests.h FORCE
	$(ARCHMOD) $(CC) -Wall -I$(CURDIR) -I$(GENDIR) -I$(LIBDIR) -I$(TOOLSINCDIR) -I$(APIDIR) -I$(INCLUDE_DIR) $< -o $@

.PHONY: FORCE
FORCE: