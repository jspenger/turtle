# Examples: Turtle-Compat Sail-RISC-V Print32

## Contents

* `conf_default.v`: execution configuration, memory regions, etc.
* `main_1.v`: program written in `turtle.compat.sail.riscv` instructions that loops and prints the numbers 4, 8, 16, 32
* `main_2.v`: program that prints the number 32
* `out/main_1.s`: RISC-V assembly transcribed from `main_1.v`
* `out/main_2.s`: RISC-V assembly transcribed from `main_2.v`
* `thm.v`:
    * `thm_1`: theorem that states that `main_2.v` linked with `turtle.compat.sail.riscv.lib.unsafe.libc.libc.unsafe_libc` eventually prints `32`
    * `thm_2`: theorem that states that `main_1.v` implements `main_2.v` under a refinement relation that hides state except for when `printf` is called with argument `32`
* `thm_proof_x.v`: proof of `thm_1` and `thm_2` available on the `x-proof-main` branch

## How to build

```bash
make
```

## How to run

Run it on RISC-V:

```bash
gcc -static out/main_1.s -o out/a.out
./out/a.out
```

```bash
gcc -static out/main_2.s -o out/a.out
./out/a.out
```

or, run it with QEMU:

```bash
apt-get install qemu-user gcc-riscv64-linux-gnu
```

```bash
riscv64-linux-gnu-gcc -static out/main_1.s -o out/a.out
./out/a.out
```

```bash
riscv64-linux-gnu-gcc -static out/main_2.s -o out/a.out
./out/a.out
```
