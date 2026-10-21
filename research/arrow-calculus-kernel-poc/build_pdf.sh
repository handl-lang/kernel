#!/bin/bash
# Build direct-bind-impossibility.md → direct-bind-impossibility.pdf via pandoc
set -e
cd "$(dirname "$0")"

pandoc direct-bind-impossibility.md \
  -o direct-bind-impossibility.pdf \
  --pdf-engine=pdflatex \
  --citeproc \
  --bibliography=direct-bind-impossibility.bib \
  --lua-filter=theorems.lua \
  --include-in-header=header.tex \
  -V geometry:margin=1in

echo "Built direct-bind-impossibility.pdf"
