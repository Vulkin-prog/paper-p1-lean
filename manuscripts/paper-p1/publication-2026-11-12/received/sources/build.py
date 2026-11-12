#!/usr/bin/env python3
"""Build both linked papers and their document-specific bibliographies."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / "build"
OUTPUTS = {"main": "P1_Main_EN.pdf", "companion": "P1_Companion_EN.pdf"}


def expanded_source(path: Path, seen: set[Path] | None = None) -> str:
    seen = set() if seen is None else seen
    if path in seen:
        return ""
    seen.add(path)
    source = path.read_text(encoding="utf-8")
    source = re.sub(r"(?<!\\)%[^\n]*", "", source)
    chunks = [source]
    for name in re.findall(r"\\input\{([^}]+)\}", source):
        if name.startswith("bibliography"):
            continue
        chunks.append(expanded_source(ROOT / (name + ".tex"), seen))
    return "\n".join(chunks)


def local_bibliographies() -> dict[str, list[str]]:
    master = (ROOT / "bibliography.tex").read_text(encoding="utf-8")
    matches = list(re.finditer(r"\\bibitem\{([^}]+)\}", master))
    entries: dict[str, str] = {}
    end = master.index(r"\end{thebibliography}")
    for index, match in enumerate(matches):
        key = match.group(1)
        if key in entries:
            raise RuntimeError(f"Duplicate bibliography key: {key}")
        stop = matches[index + 1].start() if index + 1 < len(matches) else end
        entries[key] = master[match.start():stop].strip()

    inventory: dict[str, list[str]] = {}
    for name in OUTPUTS:
        source = expanded_source(ROOT / (name + ".tex"))
        groups = re.findall(r"\\cite(?:\[[^]]*\])*\{([^}]+)\}", source)
        cited = {key.strip() for group in groups for key in group.split(",")}
        missing = cited - entries.keys()
        if missing:
            raise RuntimeError(f"Missing references in {name}: {sorted(missing)}")
        selected = [key for key in entries if key in cited]
        inventory[name] = selected
        content = (
            "% Generated from bibliography.tex by build.py.\n"
            "\\begin{thebibliography}{99}\n"
            "\\addcontentsline{toc}{section}{References}\n\n"
            + "\n\n".join(entries[key] for key in selected)
            + "\n\n\\end{thebibliography}\n"
        )
        (ROOT / f"bibliography_{name}.tex").write_text(content, encoding="utf-8")
    return inventory


def cross_reference_state() -> str:
    digest = hashlib.sha256()
    for name in OUTPUTS:
        for extension in ("aux", "toc", "out"):
            path = BUILD / f"{name}.{extension}"
            if path.exists():
                digest.update(path.read_bytes())
    return digest.hexdigest()


def main() -> None:
    if not shutil.which("pdflatex"):
        raise SystemExit("pdfLaTeX is required; install TeX Live with the packages in preamble.tex.")
    BUILD.mkdir(exist_ok=True)
    inventory = local_bibliographies()
    previous = None
    rounds = 0
    for rounds in range(1, 7):
        for name in OUTPUTS:
            command = [
                "pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                "-file-line-error", "-output-directory=build", name + ".tex",
            ]
            result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            (BUILD / f"{name}.console.txt").write_text(result.stdout + result.stderr)
            if result.returncode:
                raise SystemExit(f"{name}: pdfLaTeX failed. See build/{name}.console.txt")
        current = cross_reference_state()
        if current == previous:
            break
        previous = current
    else:
        raise SystemExit("Cross-references did not stabilize after six paired passes.")

    report = {"paired_passes": rounds, "bibliography": inventory, "documents": {}}
    fatal_patterns = (
        r"LaTeX Warning: (?:Reference|Citation).+undefined",
        r"LaTeX Warning: There were undefined references",
        r"LaTeX Warning: Label.+multiply defined",
        r"Overfull \\[hv]box",
    )
    for name, filename in OUTPUTS.items():
        log = (BUILD / f"{name}.log").read_text(errors="replace")
        issues = [line for line in log.splitlines() if any(re.search(p, line) for p in fatal_patterns)]
        if issues:
            raise SystemExit(f"{name}: unresolved typesetting issues: " + " | ".join(issues))
        pdf = BUILD / f"{name}.pdf"
        target = ROOT / filename
        shutil.copy2(pdf, target)
        report["documents"][name] = {
            "filename": filename,
            "sha256": hashlib.sha256(target.read_bytes()).hexdigest(),
            "bytes": target.stat().st_size,
        }
    (BUILD / "build-report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
