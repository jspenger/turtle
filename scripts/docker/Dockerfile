FROM ubuntu:24.04

ARG OCAML_VERSION=5.2.1
ARG ROCQ_CORE_VERSION=9.1.1
ARG ROCQ_STDLIB_VERSION=9.0.0
ARG ROCQ_STDPP_BITVECTOR_VERSION=1.13.0
ARG ROCQ_SAIL_STDPP_VERSION=0.20.2
ARG SAIL_VERSION=0.20.2

RUN apt-get update \
        && apt-get install -y --no-install-recommends \
                bzip2 \
                ca-certificates \
                cmake \
                curl \
                g++ \
                gcc \
                gcc-riscv64-linux-gnu \
                libc6-dev \
                libc6-dev-riscv64-cross \
                libgmp-dev \
                make \
                opam \
                pkg-config \
                qemu-user \
                time \
                unzip \
                z3

RUN opam init --no-setup --disable-sandboxing --compiler=${OCAML_VERSION}

RUN opam repo add rocq-released https://rocq-prover.org/opam/released \
        && opam install -y \
                rocq-core.${ROCQ_CORE_VERSION} \
                rocq-stdlib.${ROCQ_STDLIB_VERSION} \
                rocq-stdpp-bitvector.${ROCQ_STDPP_BITVECTOR_VERSION} \
                rocq-sail-stdpp.${ROCQ_SAIL_STDPP_VERSION} \
                sail.${SAIL_VERSION}

WORKDIR /turtle

# TODO: Clone turtle from repo instead
COPY . .

RUN /usr/bin/time -v opam exec -- turtle-compat/sail-riscv/deps/build.sh

RUN /usr/bin/time -v opam exec -- make

ENTRYPOINT ["opam", "exec", "--"]
CMD ["bash"]
