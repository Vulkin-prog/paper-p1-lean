#!/usr/bin/env python3
"""Build both P1 documents and their cross-references with pdfLaTeX.

Run from any working directory: python3 sources/build.py
Requires a standard TeX Live installation with the packages in preamble.tex.
No shell escape, network download, Lean invocation, or repository mutation.
"""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / 'build'
DEST = ROOT.parent
DOCS = {'main': 'P1_V2_0_Main_EN.pdf', 'companion': 'P1_V2_0_Companion_EN.pdf'}

def fingerprint():
    h = hashlib.sha256()
    for doc in DOCS:
        for ext in ('aux', 'toc'):
            p = BUILD / f'{doc}.{ext}'
            h.update(p.read_bytes() if p.exists() else b'')
    return h.hexdigest()

def main():
    if shutil.which('pdflatex') is None:
        sys.exit('pdfLaTeX is required. Install TeX Live and the packages in preamble.tex.')
    BUILD.mkdir(exist_ok=True)
    previous = None
    records = []
    for round_no in range(1, 7):
        for doc in DOCS:
            command = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                       '-halt-on-error', '-file-line-error', '-output-directory=build',
                       f'{doc}.tex']
            with (BUILD / f'{doc}-round-{round_no}.txt').open('wb') as log:
                run = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
            records.append({'document': doc, 'round': round_no, 'exit_code': run.returncode})
            if run.returncode:
                sys.exit(f'{doc} failed; see build/{doc}-round-{round_no}.txt')
        current = fingerprint()
        if previous == current:
            break
        previous = current
    else:
        sys.exit('Cross-references did not stabilize within six rounds.')

    for doc, filename in DOCS.items():
        log = (BUILD / f'{doc}.log').read_text(errors='replace')
        bad = [line for line in log.splitlines()
               if re.search(r'Overfull|undefined|multiply defined|Fatal|LaTeX Error', line)]
        if bad:
            sys.exit(f'{doc} still has layout/reference diagnostics: ' + '\n'.join(bad))
        shutil.copy2(BUILD / f'{doc}.pdf', DEST / filename)
    (BUILD / 'build-validation.json').write_text(json.dumps({
        'commands': records, 'cross_references_stable': True,
        'final_reference_and_overfull_diagnostics': [],
        'outputs': list(DOCS.values()),
        'lean_replayed': False
    }, indent=2))
    print('Built ' + ', '.join(DOCS.values()))

if __name__ == '__main__':
    main()
