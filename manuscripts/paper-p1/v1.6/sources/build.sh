#!/bin/sh
set -eu
paper_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$paper_dir"
python3 build.py
