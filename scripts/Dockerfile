FROM alpine:3.13

ARG LEAN_VERSION=v3.33.0

RUN apk add --no-cache \
    bash \
    cargo \
    clang \
    cmake \
    g++ \
    git \
    gmp-dev \
    linux-headers \
    llvm \
    make \
    ninja \
    patch \
    py3-lxml \
    py3-pip \
    python2 \
    python3 \
    rust

RUN pip3 install green

ADD ./lean/pkgs /pkgs

# Build nanoda_lib, aiger, druplig, lingeling, drat-trim
RUN cd /pkgs/nanoda_lib && \
    cargo build --release --example basic && \
	cp ./target/release/examples/basic /usr/bin/nanoda && \
    cd /pkgs && patch -p0 < lingeling.patch && \
	cd /pkgs/aiger && ./configure.sh && make -B -j "$(nproc)" && \
    cd /pkgs/druplig && ./configure.sh && make -B -j "$(nproc)" && \
    cd /pkgs/lingeling && ./configure.sh && make -B -j "$(nproc)" && \
    cd /pkgs/drat-trim && make -B drat-trim && \
    cp /pkgs/lingeling/lingeling /usr/local/bin && \
    cp /pkgs/drat-trim/drat-trim /usr/local/bin && \
    cd / && rm -rfv /pkgs

# Install Lean for proof checking
RUN git clone 'https://github.com/leanprover-community/lean' && \
    cd lean && \
    git checkout ${LEAN_VERSION} && \
    mkdir -p build/release && \
    cd build/release && \
    cmake -G Ninja -DCMAKE_INSTALL_PREFIX=/usr/local ../../src && \
    ninja && ninja install && \
    cd ../../../ && rm -rf lean
