# Examples: Turtle-Compat Sail-RISC-V Fibonacci

## Contents

* `conf_default.v`: execution configuration, memory regions, etc.
* `spec_tla.v`: `turtle-tla` specification of a Fibonacci procedure
* `spec.v`: lifting the `spec_tla` specification to a behavior of a program in `turtle.compat.sail.riscv` instructions
* `impl.v`: implementation of a Fibonacci procedure in `turtle.compat.sail.riscv` instructions
* `out/tl_fib_impl.s`: RISC-V assembly transcribed from `impl.v`
* `main.v`: implementation of a main program in `turtle.compat.sail.riscv` instructions that generates a random number from `unsafe_libc`'s `getrandom` and calls the `impl`'s Fibonacci procedure with that number and prints the result
* `out/main.s`: RISC-V assembly transcribed from `main.v`
* `thm_1`: theorem that states that `impl.v` implements `spec.v` under an environment assumption that the "caller" (e.g., `main.v`) is OK and under a refinement relation that hides its internal state 
* `thm_2`-`thm_4`: a series of theorems to prove that the `impl`ementation linked with the `main` program implements the `spec`ification linked with the `main` program under a refinement relation that hides the internal state of the `impl`ementation
* `thm_5_source_ok.v`, `thm_6_stack_ok.v`: theorems that state that the implementation does not have an unintended behavior
* `thm_7_non_trivial.v`: the linked implementation is not trivial and the linked implementation always terminates
* `*_proof_x.v`: proofs of each of the theorems above available on the `x-proof-main` branch
* `aux/tl_fib.h`: a `C` header file for the verified Fibonacci implementation 
* `aux/main.c`: an unverified `C` main program that mimics the `main.v` program and calls the verified Fibonacci implementation

## How to build

```bash
make
```

## How to run

Run the verified fibonacci function with the verified main on RISC-V:

```bash
gcc -static out/main.s out/tl_fib_impl.s -o out/a.out
./out/a.out
```

or, run it with QEMU:

```bash
apt-get install qemu-user gcc-riscv64-linux-gnu
```

```bash
riscv64-linux-gnu-gcc -static out/main.s out/tl_fib_impl.s -o out/a.out
./out/a.out
```

or, run it with an unverified main linked with the verified fibonacci function on RISC-V:

```bash
gcc -static aux/main.c out/tl_fib_impl.s -o out/a.out
./out/a.out
```

or, run it with QEMU:

```bash
riscv64-linux-gnu-gcc -static aux/main.c out/tl_fib_impl.s -o out/a.out
./out/a.out
```
