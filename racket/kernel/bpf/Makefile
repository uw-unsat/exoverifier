include ../../../scripts/Makefile.lib


main.ll: driver.ll tnum.ll
	$(QUIET_GEN)$(LLVM_LINK) -S $^ -o $@

%.ll: %.c
	$(QUIET_CC)$(LLVM_CC) -O3 -S -emit-llvm -fshort-wchar -target 'x86_64-unknown-linux-gnu' "$<" -o "$@"
