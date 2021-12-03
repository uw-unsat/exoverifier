FROM alpine:3.15

ARG BOOLECTOR_VERSION=3.2.1
ARG LEAN_VERSION=v3.35.1
ARG RACKET_VERSION=8.3
ARG ROSETTE_VERSION=dbfd8476d970c7fd110a7d8f0a91464f4b155e18
ARG SERVAL_VERSION=5443b56d5a8255ba6f6e3a585098db72692d5170
ARG Z3_VERSION=4.8.9

RUN apk add --no-cache \
    bash \
    cargo \
    clang \
    cmake \
    curl \
    g++ \
    gcompat \
    git \
    gmp-dev \
    libffi \
    linux-headers \
    llvm \
    llvm-dev \
    make \
    musl-dev \
    ninja \
    patch \
    py3-lxml \
    py3-pip \
    python2 \
    python3 \
    readline \
    rust \
    sqlite

# Install Racket
RUN wget "https://mirror.racket-lang.org/installers/${RACKET_VERSION}/racket-${RACKET_VERSION}-x86_64-linux-cs.sh" && \
    chmod +x ./racket-${RACKET_VERSION}-x86_64-linux-cs.sh && \
    echo 'yes\n1' | ./racket-${RACKET_VERSION}-x86_64-linux-cs.sh && \
    rm -f racket-${RACKET_VERSION}-x86_64-linux-cs.sh

# Install Rosette
RUN git clone 'https://github.com/emina/rosette.git' && \
    cd rosette && git checkout ${ROSETTE_VERSION} && \
    raco pkg install --auto -i --no-setup && raco setup -Dl rosette

# Install Serval
RUN git clone 'https://github.com/uw-unsat/serval.git' && \
    cd serval && git checkout ${SERVAL_VERSION} && \
    raco pkg install --auto -i --no-setup && raco setup -Dl serval

# Install Boolector twice with CaDiCal and Lingeling backends
RUN git clone 'https://github.com/boolector/boolector.git' && \
    cd boolector && git checkout ${BOOLECTOR_VERSION} && \
    ./contrib/setup-cadical.sh && \
    ./contrib/setup-btor2tools.sh && \
    ./configure.sh --prefix /opt/boolector/${BOOLECTOR_VERSION}-cadical && cd build && make -j $(nproc) && make install && \
    cd .. && git clean -xffd \
    ./contrib/setup-lingeling.sh && \
    ./contrib/setup-btor2tools.sh && \
    ./configure.sh --prefix /opt/boolector/${BOOLECTOR_VERSION}-lingeling && cd build && make -j $(nproc) && make install && \
    cd ../.. && rm -rfv ./boolector

# Install Z3
RUN git clone 'https://github.com/Z3Prover/z3.git' && \
    cd z3 && git checkout z3-${Z3_VERSION} && \
    python3 scripts/mk_make.py --prefix /opt/z3/${Z3_VERSION} && \
    cd build && \
    make -j $(nproc) && make install && \
    cd .. && rm -rfv z3

RUN pip3 install green

ADD ./lean/pkgs /pkgs

# Fix for unistd include path for musl
RUN if [ ! -f /usr/include/sys/unistd.h ]; then echo "#include <unistd.h>" > /usr/include/sys/unistd.h; fi;

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
