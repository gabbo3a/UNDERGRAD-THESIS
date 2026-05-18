FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
    tree \
    curl \
    ca-certificates \
    git \
    libgmp-dev \
    gcc \
    texlive-latex-base \
    texlive-latex-extra \
    texlive-science \
    texlive-fonts-recommended \
    texlive-lang-italian \
    texlive-bibtex-extra \
    texlive-extra-utils \
    biber \
    latexmk \
    lmodern \
    && apt-get clean && rm -rf /var/lib/apt/lists/*

RUN useradd -m -s /bin/bash luser
USER luser
WORKDIR /home/luser

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
ENV PATH="/home/luser/.elan/bin:${PATH}"

RUN elan default leanprover/lean4:stable