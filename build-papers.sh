#!/bin/sh
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build=$(mktemp -d "${TMPDIR:-/tmp}/bne-papers.XXXXXXXX")
trap 'rm -rf "$build"' EXIT
mkdir -p "$build/chapters"
(cd "$root/tex" && tectonic --outdir "$build" main.tex)
for paper in traffic-matching-security-games equilibrium-reductions; do
    (cd "$root/paper" && tectonic --outdir "$build" "$paper.tex")
done
cp "$build/main.pdf" "$root/main.pdf"
for paper in traffic-matching-security-games equilibrium-reductions; do
    cp "$build/$paper.pdf" "$root/paper/$paper.pdf"
done
