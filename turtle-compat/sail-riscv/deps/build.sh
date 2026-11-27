#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0 OR MIT

# =========================================================================== #
# Builds: sail-riscv version 0.14.1                                           #
# =========================================================================== #
# See [scripts/docker/Dockerfile] for further information on environment      #
# dependencies and installation information.                                  #
# =========================================================================== #

# Useful links:
# > https://github.com/riscv/sail-riscv/blob/0.14.1/build_simulator.sh
# > https://github.com/riscv/sail-riscv/blob/0.14.1/rocq-sail-riscv.opam.in
# > https://github.com/riscv/sail-riscv/blob/0.14.1/.github/workflows/rocq.yml

set -euo pipefail

: "${CMAKE_BUILD_TYPE:=RelWithDebInfo}"
: "${DOWNLOAD_GMP:=FALSE}"
: "${ENABLE_RISCV_TESTS:=FALSE}"
: "${DOWNLOAD_JSONCONS:=FALSE}"
: "${DOWNLOAD_CLI11:=FALSE}"
: "${DOWNLOAD_ASIO:=FALSE}"
: "${DOWNLOAD_SOFTFLOAT:=FALSE}"

HERE="$(cd "$(dirname "$0")" && pwd)"
VER="0.14.1"
URL="https://github.com/riscv/sail-riscv/archive/refs/tags/$VER.tar.gz"
TAR="$HERE/sail-riscv-$VER.tar.gz"
DIR="$HERE/sail-riscv"
SHA256="e006f984da1a8cf8d135f66eaaae99e6b3ed8932b847cf9fc0493d2f835910bc"

if [ -d "$DIR" ];
then
        echo "ERROR - dir $DIR already exists, remove and retry" >&2
        exit 1
fi

echo "DOWNLOADING $URL"
curl -fsSL -o "$TAR" "$URL"
echo "$SHA256  $TAR" | sha256sum -c -
mkdir "$DIR"
tar -xzf "$TAR" -C "$DIR" --strip-components=1
echo "$VER" > "$DIR/.ver"

# TODO: Remove this line once https://github.com/rems-project/sail/pull/1751 is
# merged into a Sail release
sed -i 's/rocq: \("[^"]*"\)/rocq: \1, coq: \1/' "$DIR/model/prelude/prelude.sail"

cmake -S "$DIR" -B "$DIR/build" \
        -DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE} \
        -DDOWNLOAD_GMP="${DOWNLOAD_GMP}" \
        -DENABLE_RISCV_TESTS="${ENABLE_RISCV_TESTS}" \
        -DDOWNLOAD_JSONCONS="${DOWNLOAD_JSONCONS}" \
        -DDOWNLOAD_CLI11="${DOWNLOAD_CLI11}" \
        -DDOWNLOAD_ASIO="${DOWNLOAD_ASIO}" \
        -DDOWNLOAD_SOFTFLOAT="${DOWNLOAD_SOFTFLOAT}"

cmake --build "$DIR/build" --target build_rocq_rv64d -j1
# cmake --build "$DIR/build" --target build_rocq_rv32d -j1 # skip

echo "SUCCESS - build complete, sail-riscv version $VER at $DIR"
