// SPDX-License-Identifier: NoAssertionLicense

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/random.h>

#include "tl_fib.h"

int main(void)
{
        uint64_t buf;
        uint64_t n;
        uint64_t r;
        if (getrandom(&buf, 8, 0) != 8)
        {
                exit(1);
        }
        n = buf & 31;
        r = tl_fib(n);
        printf("%lu\n", n);
        printf("%lu\n", r);
        exit(0);
}
