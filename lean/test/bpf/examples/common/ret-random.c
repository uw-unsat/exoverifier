#include <helpers.h>

int main(void) {
    int x = bpf_get_prandom_u32();
    return x;
}
