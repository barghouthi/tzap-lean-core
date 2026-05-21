# syntax=docker/dockerfile:1.6
#
# Image for running scripts/compare.py against external T-count optimizers.
# Bundles: tzap (this repo), quizx (Rust), feynopt (Haskell),
#          voqc (OCaml, ORNL-QCI fork), pyzx.
#
# Build:   docker build -t tzap-compare .
# Run:     docker run --rm -v "$PWD/qasm":/data tzap-compare \
#              python3 scripts/compare.py /data
# (qasm/ is not copied into the image — mount your circuits at runtime.)

FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive \
    LANG=C.UTF-8 \
    LC_ALL=C.UTF-8

RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates curl git \
        build-essential pkg-config m4 \
        libgmp-dev zlib1g-dev libffi-dev \
        python3 python3-pip python3-venv \
        ocaml opam \
        ghc cabal-install \
 && rm -rf /var/lib/apt/lists/*

# ---- Rust toolchain (for quizx) --------------------------------------------
ENV CARGO_HOME=/opt/cargo \
    RUSTUP_HOME=/opt/rustup \
    PATH=/opt/cargo/bin:$PATH
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
      | sh -s -- -y --default-toolchain stable --profile minimal \
 && chmod -R a+rX /opt/cargo /opt/rustup

# ---- quizx (Quantomatic/quizx) ---------------------------------------------
# The `quizx` CLI binary used by compare.py lives in the published crates.io
# release; the GitHub HEAD no longer ships a bin target. Install the binary
# from crates.io and keep a source clone under /root/git/ for reference.
RUN git clone --depth 1 https://github.com/Quantomatic/quizx /root/git/quizx \
 && cargo install quizx --locked

# ---- feynopt (meamy/feynman) -----------------------------------------------
RUN git clone --depth 1 https://github.com/meamy/feynman /root/git/feynman \
 && cd /root/git/feynman \
 && cabal update \
 && cabal install --installdir=/usr/local/bin --install-method=copy --overwrite-policy=always \
 && rm -rf /root/.cabal/store /root/git/feynman/dist-newstyle

# ---- voqc (ORNL-QCI/VOQC — uses pre-extracted OCaml, no Coq needed) --------
ENV OPAMROOT=/opt/opam
RUN opam init -y --disable-sandboxing --bare \
 && opam switch create default --packages=ocaml-system \
 && opam install -y dune menhir zarith openQASM ctypes ctypes-foreign ctypes-zarith ppx_deriving
ENV PATH=/opt/opam/default/bin:$PATH \
    OPAM_SWITCH_PREFIX=/opt/opam/default \
    OCAML_TOPLEVEL_PATH=/opt/opam/default/lib/toplevel \
    CAML_LD_LIBRARY_PATH=/opt/opam/default/lib/stublibs:/opt/opam/default/lib/ocaml/stublibs:/opt/opam/default/lib/ocaml

RUN git clone --depth 1 --recurse-submodules https://github.com/ORNL-QCI/VOQC /root/git/VOQC \
 && cd /root/git/VOQC \
 && opam exec -- dune build voqc.exe --root VOQC \
 && install -m 0755 VOQC/_build/default/voqc.exe /usr/local/bin/voqc \
 && rm -rf VOQC/_build

# ---- pyzx (optional tool in compare.py) ------------------------------------
RUN pip3 install --break-system-packages pyzx

# ---- tzap (qqq-wisc/tzap) --------------------------------------------------
ARG TZAP_REF=main
RUN git clone https://github.com/qqq-wisc/tzap /root/git/tzap \
 && cd /root/git/tzap \
 && git checkout "${TZAP_REF}" \
 && cargo build --release \
 && install -m 0755 target/release/tzap /usr/local/bin/tzap \
 && rm -rf target
WORKDIR /root/git/tzap

CMD ["/bin/bash"]
