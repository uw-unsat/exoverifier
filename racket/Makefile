include ../scripts/Makefile.lib

SERVAL_LLVM := raco serval-llvm

KERNEL_LLS  := $(call rwildcard,kernel,*.ll) kernel/bpf/main.ll
KERNEL_RKTS := $(patsubst %.ll,%.rkt,$(KERNEL_LLS))
RACO_JOBS   ?= $(shell nproc)

all: $(KERNEL_RKTS)

clean:
	find ./kernel -name '*.rkt' -delete

verify-all: $(KERNEL_RKTS)
	raco test --jobs "$(RACO_JOBS)" -- test

%.rkt: %.ll
	$(SERVAL_LLVM) < "$<" > "$@"

kernel/bpf/main.ll: FORCE
	$(MAKE) -C kernel/bpf

FORCE:

.PHONY: all clean verify-all FORCE
