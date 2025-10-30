FROM mcr.microsoft.com/devcontainers/base:jammy

RUN apt-get update && \
    apt-get install -y \
        curl \
        python3-pip \
        graphviz \
        libgraphviz-dev \
    && rm -rf /var/lib/apt/lists/*

# install elan and pick a Lean right away
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain stable

# install leanblueprint globally
RUN pip install --no-cache-dir leanblueprint

# make sure lean + pip binaries are on PATH for root
ENV PATH="/root/.elan/bin:/root/.local/bin:${PATH}"

WORKDIR /workspaces
