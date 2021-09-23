include Makefile.lib

UBPF_DISASSEMBLER ?= ./pkgs/ubpf/bin/ubpf-disassembler

all:

clean:
	@find ./src -name '*.olean' -print -delete
	@rm -f test/bpf/examples/*.o test/bpf/examples/*.bin

clean-deps:
	@find . -name '*.olean' -print -delete

certificates: test/bpf/se.lef

%.lef: %.lean
	lean --only-export=progbits_safe --export=$@ $<

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
	$(patsubst %.c32sat,%_64.aig,$(C32SAT_TESTS))

BPF_BINS := \
  $(patsubst %.S,%.bin,$(call rwildcard,test/bpf/examples/,*.S)) \
  $(patsubst %.c,%.bin,$(call rwildcard,test/bpf/examples/ebpf-samples/src/,*.c)) \
  $(patsubst %.o,%.bin,$(call rwildcard,test/bpf/examples/,*.o))

gen-bpf-tests: bpf-examples

bpf-examples: $(BPF_BINS) $(patsubst %.bin,%.asm,$(BPF_BINS)) $(patsubst %.o,%.llvmasm,$(call rwildcard,test/bpf/examples/,*.o))

%.o: %.S
	$(QUIET_GEN)$(LLVM_MC) -triple bpf -filetype=obj -o "$@" "$<"

%.o: %.c
	$(QUIET_CC)$(LLVM_CC) -target bpf -Wall -O2 -c "$<" -o "$@"

%.bin: %.o
	$(QUIET_GEN)$(LLVM_OBJCOPY) -I bpf -O binary "$<" "$@"

%.llvmasm: %.o
	$(QUIET_GEN)$(LLVM_OBJDUMP) --triple bpf -d "$<" > "$@"

%.asm: %.bin
	$(QUIET_GEN)$(UBPF_DISASSEMBLER) "$<" "$@"

.PRECIOUS: %.o %.bin

.PHONY: bin clean clean-deps bpf-examples gen-bpf-tests test/aig/c32sat certificates
