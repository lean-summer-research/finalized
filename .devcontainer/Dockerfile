FROM mcr.microsoft.com/devcontainers/base:jammy

# Set up PATH for both root and vscode user
ENV PATH="/root/.elan/bin:/root/.local/bin:${PATH}"

# Install system packages
RUN apt-get update && \
    apt-get install -y \
        curl
        # Below are commented out because they are required for the blueprint
        # but were taking up too much space.
        # python3-pip \  
        # graphviz \
        # libgraphviz-dev \
        # texlive-xetex \
        # texlive-latex-extra \
        # texlive-fonts-extra \
        # latexmk

# Install elan and configure default Lean toolchain
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain stable

# Install leanblueprint (requires python3-pip, graphviz, libgraphviz-dev)
# RUN pip install --no-cache-dir leanblueprint

# Set up PATH for vscode user
USER vscode
ENV PATH="/home/vscode/.elan/bin:/home/vscode/.local/bin:${PATH}"

USER root
WORKDIR /workspaces

