#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Standalone P1 article/companion build helper, copied as build.py in the ZIP.

Requires Python >= 3.9 and pdflatex with the packages named in sources/preamble.tex.
Run both documents together: each imports the other's cross-reference data.
The default output is rebuilt-pdf/, leaving the supplied canonical PDFs intact.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
NAMES = {'main': 'P1_Main_EN.pdf', 'companion': 'P1_Companion_EN.pdf'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(source, destination, evidence):
    source, destination, evidence = map(lambda p: Path(p).resolve(), (source, destination, evidence))
    if not source.is_dir():
        raise ValueError('Source directory not found: ' + str(source))
    if destination == source or destination.is_relative_to(source):
        raise ValueError('Choose an output directory outside sources/')
    if evidence == source or evidence.is_relative_to(source):
        raise ValueError('Choose an evidence directory outside sources/')
    files = sorted(source.rglob('*.tex'))
    if len(files) != 34:
        raise ValueError('Expected the complete set of 34 shared article/companion TeX files')
    for path in files:
        if path.is_symlink():
            raise ValueError('Source symlinks are not supported')
        text = path.read_text(encoding='utf-8')
        if re.search(r'\\(?:write18|openout|read|catcode|immediate|directlua)\b', text):
            raise ValueError('Unsupported TeX IO in ' + str(path))
        for name in re.findall(r'\\input\{([^}]+)\}', text):
            target = (source / (name + '.tex')).resolve()
            if not target.is_relative_to(source) or not target.is_file():
                raise ValueError('Nonlocal TeX input: ' + name)
    destination.mkdir(parents=True, exist_ok=True)
    evidence.mkdir(parents=True, exist_ok=True)
    commands = []
    with tempfile.TemporaryDirectory(prefix='p1-paper-build-', dir=evidence) as temporary:
        work = Path(temporary)
        for path in files:
            target = work / path.relative_to(source)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, target)
        (work / 'build').mkdir()
        previous = None
        for round_number in range(1, 7):
            for document in NAMES:
                args = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                        '-halt-on-error', '-file-line-error', '-output-directory=build', document + '.tex']
                logfile = evidence / f'{document}-round-{round_number}.log'
                with logfile.open('wb') as stream:
                    result = subprocess.run(args, cwd=work, stdout=stream, stderr=subprocess.STDOUT)
                commands.append({'document': document, 'round': round_number,
                                 'actual_exit_code': result.returncode, 'command': args,
                                 'log': logfile.name, 'log_sha256': sha(logfile)})
                if result.returncode:
                    raise RuntimeError('LaTeX failed; inspect ' + str(logfile))
            state = b''.join((work / 'build' / f'{d}.{ext}').read_bytes()
                             for d in NAMES for ext in ['aux', 'toc'])
            if previous == state:
                break
            previous = state
        else:
            raise RuntimeError('Cross-references did not stabilize after six rounds')
        pdfs = []
        for document, filename in NAMES.items():
            log = (work / 'build' / (document + '.log')).read_text(errors='replace')
            bad = [line for line in log.splitlines()
                   if re.search(r'Overfull|undefined|multiply defined|Fatal|LaTeX Error', line)]
            if bad:
                raise RuntimeError(f'{document}: remaining layout/reference diagnostics: {bad}')
            pages = int(re.search(r'Output written on .*?\((\d+) pages?', log, re.S)[1])
            shutil.copy2(work / 'build' / (document + '.pdf'), destination / filename)
            shutil.copy2(work / 'build' / (document + '.aux'), evidence / (document + '.aux'))
            shutil.copy2(work / 'build' / (document + '.log'), evidence / (document + '.final.log'))
            pdfs.append({'document': document, 'filename': filename, 'pages': pages,
                         'sha256': sha(destination / filename)})
    receipt = {
        'status': 'passed', 'cross_references_stable': True,
        'unresolved_or_overfull_diagnostics': [], 'shell_escape': False,
        'commands': commands,
        'source_files': {p.relative_to(source).as_posix(): sha(p) for p in files},
        'pdfs': pdfs,
        'note': 'PDF timestamps/identifiers may vary; compare page counts and extracted text with the canonical PDFs.'
    }
    (evidence / 'build-validation.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': 'passed', 'latex_executions': len(commands), 'pdfs': pdfs}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir', type=Path, default=ROOT / 'sources')
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'rebuilt-pdf')
    parser.add_argument('--evidence-dir', type=Path, default=ROOT / 'build-evidence')
    args = parser.parse_args()
    build(args.source_dir, args.output_dir, args.evidence_dir)
