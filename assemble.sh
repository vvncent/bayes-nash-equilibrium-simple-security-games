#!/usr/bin/env bash
# Assemble the submission folder from its sources. Run from anywhere.
#   main.pdf  <- book/readable/main.pdf   (rebuild the book first)
#   tex/      <- book/readable LaTeX sources (main.tex, preamble.tex, refs.tex, chapters/)
#   code/     <- artifact/                (copied; logs kept, caches dropped)
#   lean/     <- BssgProofs/ sources      (when the formalization exists; Mathlib cache excluded)
set -eu
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/submission"
cp "$ROOT/book/readable/main.pdf" "$OUT/main.pdf"
cp "$ROOT/LICENSE" "$OUT/LICENSE"
mkdir -p "$OUT/tex"
rsync -a --delete --include 'main.tex' --include 'preamble.tex' --include 'refs.tex' --include 'chapters/' --include 'chapters/*.tex' --exclude '*' "$ROOT/book/readable/" "$OUT/tex/"
rsync -a --delete --exclude '__pycache__' --exclude '.build' --exclude '.venv' "$ROOT/artifact/" "$OUT/code/"
if [ -f "$ROOT/BssgProofs/lakefile.toml" ]; then
  rsync -a --delete --delete-excluded --exclude '.lake' --exclude '.git' --exclude '.github' \
    --exclude 'PROGRESS.md' --exclude 'PROVER-BRIEF.md' --exclude '/README.md' \
    "$ROOT/BssgProofs/" "$OUT/lean/project/"
  printf '%s\n' "# BssgProofs (Lean 4 + Mathlib)" \
    "Machine-checked ARRIVAL-hardness of exact BNE in Bayesian simple security games, and parts of Chapters 3 and 5 of main.pdf." \
    "See ../README.md for the theorem list, build instructions and scope." > "$OUT/lean/project/README.md"
fi
echo "assembled: $(ls "$OUT")"
