#!/usr/bin/env bash
# Build the PDFs of the paper (to ../pdf) from the LaTeX sources in this folder.
#
#   ./build.sh
#
# Needs python3 and Tectonic (https://tectonic-typesetting.github.io/).
# Environment:
#   GITREF=<commit>       point the code links at that commit instead of branch main
#   TECTONIC_OFFLINE=1    build from Tectonic's cache only (tectonic -C)
set -euo pipefail
cd "$(dirname "$0")"

python3 gen_codelinks.py

if [ -n "${GITREF:-}" ]; then
  printf '\\newcommand{\\gitref}{%s}\n' "$GITREF" > gitref.tex
  trap 'rm -f gitref.tex' EXIT
fi

mkdir -p ../pdf
for p in en zh; do
  tectonic ${TECTONIC_OFFLINE:+-C} --outdir ../pdf "dest-inconsistency.$p.tex"
done
