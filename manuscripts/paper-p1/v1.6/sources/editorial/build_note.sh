#!/bin/sh
set -eu
note_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$note_dir"
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build note_revision_fr.tex
