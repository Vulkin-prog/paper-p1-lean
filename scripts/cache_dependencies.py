#!/usr/bin/env python3
"""Fetch only the Mathlib imports used by this project and their dependencies."""

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="List direct imports without downloading")
    args = parser.parse_args()
    modules = sorted({
        module
        for source in (ROOT / "PaperP1").rglob("*.lean")
        for module in re.findall(r"^(?:public )?import (Mathlib\.[A-Za-z0-9_.]+)$", source.read_text(), re.M)
    })
    if not modules:
        raise SystemExit("No Mathlib imports discovered")
    if args.list:
        print("\n".join(modules))
        return
    disk_check = [sys.executable, str(ROOT / "scripts/check_disk.py")]
    env = os.environ.copy()
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    print(f"Fetching the cache for {len(modules)} direct imports and their dependencies.", flush=True)
    command = ["lake", "exe", "cache", "get", *modules]
    for attempt in range(1, 4):
        subprocess.run(disk_check, check=True)
        result = subprocess.run(command, cwd=ROOT, env=env, check=False)
        subprocess.run(disk_check, check=True)
        if result.returncode == 0:
            return
        if attempt == 3:
            result.check_returncode()
        print(f"Cache download failed; retrying the same selective request ({attempt}/3).", flush=True)
        time.sleep(5 * attempt)


if __name__ == "__main__":
    main()
