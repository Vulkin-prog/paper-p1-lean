#!/usr/bin/env python3
"""Build both associated articles and resolve their cross-document references."""
from pathlib import Path
import hashlib
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / "build"
BUILD.mkdir(exist_ok=True)
DOCUMENTS = ("main", "companion")
OUTPUT_NAMES = {
    "main": "P1_V1_6_Main_Article_2026-10-31_EN.pdf",
    "companion": "P1_V1_6_Technical_Companion_2026-10-31_EN.pdf",
}


def signature():
    digest = hashlib.sha256()
    for name in DOCUMENTS:
        for suffix in ("aux", "toc", "out"):
            path = BUILD / f"{name}.{suffix}"
            if path.exists():
                digest.update(path.read_bytes())
    return digest.hexdigest()


previous = None
completed = {}
# Restart from a complete reference state if an earlier TeX run was interrupted.
for name in DOCUMENTS:
    auxiliary = BUILD / f"{name}.aux"
    if auxiliary.exists() and b"\\@abspage@last" not in auxiliary.read_bytes():
        for suffix in ("aux", "toc", "out"):
            (BUILD / f"{name}.{suffix}").unlink(missing_ok=True)
for cycle in range(1, 9):
    for name in DOCUMENTS:
        result = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
             "-file-line-error", "-output-directory=build", f"{name}.tex"],
            cwd=ROOT, capture_output=True, text=True, errors="replace", timeout=120,
        )
        (BUILD / f"{name}.stdout.txt").write_text(result.stdout + result.stderr)
        if result.returncode:
            print(result.stdout[-12000:])
            sys.exit(result.returncode)
        for suffix in ("aux", "toc", "out", "log", "pdf"):
            path = BUILD / f"{name}.{suffix}"
            if path.exists():
                completed[path] = path.read_bytes()
    current = signature()
    print(f"Reference cycle {cycle} completed.", flush=True)
    if cycle >= 3 and current == previous:
        break
    previous = current
else:
    sys.exit("Cross-document references did not stabilize in eight cycles.")

# Publish completed files atomically: readers must not see a partially
# rewritten auxiliary file or PDF while TeX is producing its next pass.
for name in DOCUMENTS:
    if b"%%EOF" not in completed[BUILD / f"{name}.pdf"][-1024:]:
        sys.exit(f"Incomplete PDF after building {name}.")
    if b"\\@abspage@last" not in completed[BUILD / f"{name}.aux"]:
        sys.exit(f"Incomplete auxiliary file after building {name}.")
for path, contents in completed.items():
    staged = path.with_name(path.name + ".complete")
    with staged.open("wb") as stream:
        stream.write(contents)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(staged, path)

for name in DOCUMENTS:
    log = completed[BUILD / f"{name}.log"].decode(errors="replace")
    failures = [line for line in log.splitlines()
                if "undefined" in line.lower() or "multiply defined" in line.lower()]
    if failures:
        print("\n".join(failures))
        sys.exit(f"Unresolved references remain in {name}.")
    # The audit reads these completed snapshots rather than TeX's mutable files.
    publications = {
        BUILD / OUTPUT_NAMES[name]: completed[BUILD / f"{name}.pdf"],
        BUILD / f"resolved_{name}.aux.txt": completed[BUILD / f"{name}.aux"],
        BUILD / f"resolved_{name}.log.txt": completed[BUILD / f"{name}.log"],
    }
    for destination, contents in publications.items():
        staged = destination.with_name(destination.name + ".complete")
        with staged.open("wb") as stream:
            stream.write(contents)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(staged, destination)
    print(f"Built {OUTPUT_NAMES[name]}")
