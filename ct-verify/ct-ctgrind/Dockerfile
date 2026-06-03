# Dev image for iterating on ct-ctgrind locally.
#
# Build once:
#   docker build -t ct-ctgrind-dev -f ct-verify/ct-ctgrind/Dockerfile .
#
# Then run from the repo root:
#   docker run --rm -v "$PWD:/work" -w /work \
#       -e CARGO_TARGET_DIR=/work/target/docker \
#       ct-ctgrind-dev \
#       bash -c "cargo build --release -p ct-ctgrind && \
#                valgrind --tool=memcheck --error-exitcode=0 -q \
#                  target/docker/release/ct-ctgrind"
#
# Matches the CI image (ubuntu-latest = 24.04) so Valgrind versions and
# crabgrind's C header dependencies line up.

FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive \
    RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    PATH=/usr/local/cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin

RUN apt-get update -qq && \
    apt-get install -y -qq --no-install-recommends \
        build-essential curl valgrind ca-certificates pkg-config && \
    rm -rf /var/lib/apt/lists/*

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | \
        sh -s -- -y --default-toolchain 1.86 --profile minimal --no-modify-path && \
    rustup --version && cargo --version

WORKDIR /work
