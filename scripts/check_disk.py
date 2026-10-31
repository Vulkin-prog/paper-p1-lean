#!/usr/bin/env python3
"""Check the project's Ubuntu device and available disk budget."""

import argparse
from pathlib import Path
import shutil
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--warn-gib", type=float, default=10)
    parser.add_argument("--stop-gib", type=float, default=5)
    args = parser.parse_args()
    if not 0 <= args.stop_gib <= args.warn_gib:
        parser.error("Require 0 <= stop-gib <= warn-gib")
    root = Path(__file__).resolve().parents[1]
    same_device = root.stat().st_dev == Path("/").stat().st_dev
    free = shutil.disk_usage(root).free / 1024**3
    print(f"Available: {free:.2f} GiB; repository on Ubuntu root device: {same_device}")
    if not same_device:
        print("ERROR: project is outside the Ubuntu root device; check the location.", file=sys.stderr)
        return 2
    if free < args.stop_gib:
        print("STOP: less than the minimum reserve; suspend large operations.", file=sys.stderr)
        return 2
    if free < args.warn_gib:
        print("WARNING: disk space is becoming tight; alert the user.", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
