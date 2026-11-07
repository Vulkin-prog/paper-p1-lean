#!/usr/bin/env python3
"""Build the separate v1.8 draft with shell escape disabled and disk checks."""

from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "manuscripts/paper-p1/v1.8/sources"
BUILD = SOURCE / "build"
PDFS = SOURCE.parent / "pdf"
NAMES = {
    "main": "P1_V1_8_Main_Article_2026-11-07_EN.pdf",
    "companion": "P1_V1_8_Technical_Companion_2026-11-07_EN.pdf",
}


def disk():
    subprocess.run([sys.executable, str(ROOT / "scripts/check_disk.py")], check=True)


def auxiliary_digest():
    h = hashlib.sha256()
    for name in ["main.aux", "main.toc", "companion.aux", "companion.toc"]:
        p = BUILD / name
        h.update(name.encode() + b"\0" + (p.read_bytes() if p.exists() else b""))
    return h.hexdigest()


def check_numbered_labels():
    """Verify the actual typeset numbers against the preserved 167-label ledger."""
    rows = json.loads((ROOT / "docs/manuscript-results-v1.7.json").read_text())["results"]
    for document in NAMES:
        labels = dict((label, number) for label, number in re.findall(
            r"\\newlabel\{([^}]+)\}\{\{([^}]+)\}\{[^}]+\}",
            (BUILD / f"{document}.aux").read_text()))
        for row in rows:
            if row["document"] == document and labels.get(row["label"]) != row["number"]:
                raise ValueError(f"Typeset result number changed: {row['label']}")
    print("All 167 actual typeset result numbers match the preserved ledger.", flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--max-rounds", type=int, default=6)
    args = parser.parse_args()
    BUILD.mkdir(parents=True, exist_ok=True)
    previous = None
    for round_number in range(1, args.max_rounds + 1):
        for document in ["main", "companion"]:
            log = BUILD / f"{document}-pass-{round_number}.stdout.log"
            disk()
            try:
                with log.open("w") as out:
                    result = subprocess.run(
                        [
                            "pdflatex",
                            "-no-shell-escape",
                            "-interaction=nonstopmode",
                            "-halt-on-error",
                            "-file-line-error",
                            "-output-directory=build",
                            f"{document}.tex",
                        ],
                        cwd=SOURCE,
                        stdout=out,
                        stderr=subprocess.STDOUT,
                        timeout=60,
                    )
            finally:
                disk()
            if result.returncode:
                print("\n".join(log.read_text(errors="replace").splitlines()[-65:]))
                raise SystemExit(result.returncode)
            print(f"{document}: round {round_number} passed", flush=True)
        current = auxiliary_digest()
        if current == previous:
            print("Both auxiliary files and contents tables are stable.", flush=True)
            break
        previous = current
    else:
        raise SystemExit("Cross-references did not stabilize within the requested rounds.")
    check_numbered_labels()
    for document in NAMES:
        text = (BUILD / f"{document}.log").read_text(errors="replace")
        forbidden = [
            "There were undefined references.",
            "There were multiply-defined labels.",
            "Rerun to get cross-references right.",
            "LaTeX Warning: Citation",
            "LaTeX Error:",
        ]
        if any(item in text for item in forbidden):
            raise SystemExit(f"Unresolved TeX references or errors in {document}.log")
    PDFS.mkdir(parents=True, exist_ok=True)
    if args.output_dir:
        args.output_dir.mkdir(parents=True, exist_ok=True)
    disk()
    for document, filename in NAMES.items():
        shutil.copy2(BUILD / f"{document}.pdf", PDFS / filename)
        if args.output_dir:
            shutil.copy2(BUILD / f"{document}.pdf", args.output_dir / filename)
    disk()
    print("Built both v1.8 draft PDFs with stable cross-references.", flush=True)


if __name__ == "__main__":
    main()
