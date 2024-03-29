include ../scripts/Makefile.lib

UBPF_DISASSEMBLER ?= ./pkgs/ubpf/bin/ubpf-disassembler
PROOF_GENERATOR := ./scripts/make_proof.py
NANODA := nanoda
LEAN_SRCS := $(call rwildcard,src/,*.lean) $(call rwildcard,test/,*.lean)

all:

clean:
	@find ./src -name '*.olean' -print -delete
	@find ./test \( -name '*.bin' -or -name '*.asm' -or -name '*.llvmasm' -or -name '*.lef' -or -name '*.lef.nanoda.out' -or -name '*.lef.leanchecker.out' \) -print -delete

clean-deps:
	@find . -name '*.olean' -print -delete

%-absint.lef: %.bin $(LEAN_SRCS)
	$(PROOF_GENERATOR) --verifier 'absint' "$<" "$@"

%-symeval.lef: %.bin $(LEAN_SRCS)
	$(PROOF_GENERATOR) --verifier 'se+sat' "$<" "$@"

%.lef.nanoda.out: %.lef
	$(NANODA) $(shell nproc) "$<" > "$@"

%.lef.leanchecker.out: %.lef
	leanchecker "$<" > "$@"

bin: \
	pkgs/aiger/aigtoaig \
	pkgs/aiger/aigtodot \
	pkgs/drat-trim/drat-trim \
	pkgs/lingeling/lingeling

pkgs/drat-trim/drat-trim:
	cd pkgs/drat-trim && make drat-trim

pkgs/lingeling/lingeling: pkgs/druplig/libdruplig.a
	cd pkgs/lingeling && ./configure.sh && make lingeling

pkgs/druplig/libdruplig.a:
	cd pkgs/druplig && ./configure.sh && make libdruplig.a

pkgs/picosat/libpicosat.a pkgs/picosat/picosat:
	cd pkgs/picosat && ./configure.sh --trace && make libpicosat.a picosat

pkgs/aiger/aigtoaig pkgs/aiger/aigtodot: pkgs/picosat/libpicosat.a
	cd pkgs/aiger && ./configure.sh && make aigtoaig aigtodot

pkgs/c32sat/c32sat: pkgs/picosat/libpicosat.a
	cd pkgs/c32sat && ./configure && make

C32SAT_FLAGS := -t -dump-aig -overflow -no-two-level-opt
C32SAT_TESTS := $(wildcard test/aig/c32sat/*.c32sat)

%_04.aag: %.c32sat pkgs/c32sat/c32sat
	-pkgs/c32sat/c32sat $(C32SAT_FLAGS) -4bits $< > $@

%_08.aag: %.c32sat pkgs/c32sat/c32sat
	-pkgs/c32sat/c32sat $(C32SAT_FLAGS) -8bits $< > $@

%_16.aag: %.c32sat pkgs/c32sat/c32sat
	-pkgs/c32sat/c32sat $(C32SAT_FLAGS) -16bits $< > $@

%_32.aag: %.c32sat pkgs/c32sat/c32sat
	-pkgs/c32sat/c32sat $(C32SAT_FLAGS) -32bits $< > $@

%_64.aag: %.c32sat pkgs/c32sat/c32sat
	-pkgs/c32sat/c32sat $(C32SAT_FLAGS) -64bits $< > $@

%.aig: %.aag pkgs/aiger/aigtoaig
	pkgs/aiger/aigtoaig $< $@

test/aig/c32sat: \
	$(patsubst %.c32sat,%_04.aig,$(C32SAT_TESTS)) \
	$(patsubst %.c32sat,%_08.aig,$(C32SAT_TESTS)) \
	$(patsubst %.c32sat,%_16.aig,$(C32SAT_TESTS)) \
	$(patsubst %.c32sat,%_32.aig,$(C32SAT_TESTS)) \
	$(patsubst %.c32sat,%_64.aig,$(C32SAT_TESTS)) \

BPF_BINS := \
    $(patsubst %.S,%.bin,$(call rwildcard,test/bpf/examples/,*.S)) \
    $(patsubst %.c,%.bin,$(call rwildcard,test/bpf/examples/ebpf-samples/src/,*.c)) \
    $(patsubst %.c,%.bin,$(call rwildcard,test/bpf/examples/absint/,*.c)) \
    $(patsubst %.c,%.bin,$(call rwildcard,test/bpf/examples/symeval/,*.c)) \
    $(patsubst %.o,%.bin,$(call rwildcard,test/bpf/examples/,*.o)) \
    $(call rwildcard,test/bpf/examples/test_verifier/bin/,*.bin) \

FILTER_OUT = $(foreach v,$(2),$(if $(findstring $(1),$(v)),,$(v)))

BPF_PROOFS := $(call FILTER_OUT,fail, \
    $(patsubst %.S,%-absint.lef,$(call rwildcard,test/bpf/examples/absint/,*.S)) \
    $(patsubst %.S,%-symeval.lef,$(call rwildcard,test/bpf/examples/symeval/,*.S)) \
    $(patsubst %.c,%-absint.lef,$(call rwildcard,test/bpf/examples/absint/,*.c)) \
    $(patsubst %.c,%-symeval.lef,$(call rwildcard,test/bpf/examples/symeval/,*.c)) \
    )

proofs: $(BPF_PROOFS)

check-proofs: \
	$(patsubst %.lef,%.lef.leanchecker.out,$(BPF_PROOFS)) \
	$(patsubst %.lef,%.lef.nanoda.out,$(BPF_PROOFS)) \

bpf-examples: $(BPF_BINS) $(patsubst %.bin,%.asm,$(BPF_BINS)) $(patsubst %.o,%.llvmasm,$(call rwildcard,test/bpf/examples/,*.o))

%.o: %.S
	$(QUIET_GEN)$(LLVM_CC) -Itest/bpf/examples/common -c -target bpf -o "$@" "$<"

%.o: %.c
	$(QUIET_CC)$(LLVM_CC) -Itest/bpf/examples/common -target bpf -Wall -O2 -c "$<" -o "$@"

%.bin: %.o
	$(QUIET_GEN)$(LLVM_OBJCOPY) -I bpf -O binary "$<" "$@"

%.llvmasm: %.o
	$(QUIET_GEN)$(LLVM_OBJDUMP) --triple bpf -d "$<" > "$@"

%.asm: %.bin
	$(QUIET_GEN)$(UBPF_DISASSEMBLER) "$<" "$@"

.PRECIOUS: %.o %.bin %.llvmasm %.asm

.PHONY: bin clean clean-deps bpf-examples test/aig/c32sat proofs check-proofs
