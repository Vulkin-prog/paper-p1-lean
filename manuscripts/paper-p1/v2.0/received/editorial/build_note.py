#!/usr/bin/env python3
"""Build the French revision note with a standard TeX Live installation."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / 'build'
OUTPUT = ROOT.parent / 'P1_V2_0_Revision_FR.pdf'

def main():
    if shutil.which('pdflatex') is None:
        sys.exit('pdfLaTeX is required.')
    BUILD.mkdir(exist_ok=True)
    previous = None
    rounds = []
    for n in range(1, 5):
        command = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                   '-halt-on-error', '-file-line-error', '-output-directory=build',
                   'revision_note.tex']
        with (BUILD / f'revision-note-round-{n}.txt').open('wb') as log:
            run = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        rounds.append({'round': n, 'exit_code': run.returncode})
        if run.returncode:
            sys.exit(f'Compilation failed; see editorial/build/revision-note-round-{n}.txt')
        current = hashlib.sha256((BUILD / 'revision_note.aux').read_bytes()).hexdigest()
        if current == previous:
            break
        previous = current
    else:
        sys.exit('Revision note references did not stabilize.')
    log = (BUILD / 'revision_note.log').read_text(errors='replace')
    diagnostics = [line for line in log.splitlines()
                   if re.search(r'Overfull|undefined|multiply defined|Fatal|LaTeX Error', line)]
    if diagnostics:
        sys.exit('\n'.join(diagnostics))
    shutil.copy2(BUILD / 'revision_note.pdf', OUTPUT)
    (ROOT / 'note_build_validation.json').write_text(json.dumps({
        'rounds': rounds, 'cross_references_stable': True,
        'final_reference_and_overfull_diagnostics': [], 'output': OUTPUT.name,
        'lean_replayed': False
    }, indent=2))
    print(f'Built {OUTPUT.name}')

if __name__ == '__main__':
    main()
