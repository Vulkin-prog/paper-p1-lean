#!/usr/bin/env python3
"""Build the active V2 sources in an isolated directory, without shell escape.

Uses only the repository's TeX sources, not scripts supplied in the archive.
The received dossier and all prior editions remain unchanged.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'manuscripts/paper-p1/v2.0/sources'
NAMES = {'main': 'P1_V2_0_Main_EN.pdf', 'companion': 'P1_V2_0_Companion_EN.pdf'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(destination, evidence, *, source=None, names=None, expected_tex_files=32):
    source = SOURCE if source is None else source
    names = NAMES if names is None else names
    destination.mkdir(parents=True, exist_ok=True)
    evidence.mkdir(parents=True, exist_ok=True)
    files = sorted(source.rglob('*.tex'))
    if len(files) != expected_tex_files:
        raise ValueError('Unexpected manuscript source set')
    # All authored input commands are local names in the supplied source set.
    for path in files:
        text = path.read_text()
        if re.search(r'\\(?:write18|openout|read|catcode|immediate|directlua)\b', text):
            raise ValueError(f'Unsupported TeX IO in {path}')
        for name in re.findall(r'\\input\{([^}]+)\}', text):
            target = (source / (name + '.tex')).resolve()
            if not target.is_relative_to(source.resolve()) or not target.is_file():
                raise ValueError(f'Nonlocal TeX input: {name}')
    commands = []
    with tempfile.TemporaryDirectory(prefix='p1-v20-build-', dir=evidence) as temporary:
        work = Path(temporary)
        for path in files:
            target = work / path.relative_to(source)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, target)
        (work / 'build').mkdir()
        previous = None
        for round_number in range(1, 7):
            for document in names:
                args = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                        '-halt-on-error', '-file-line-error', '-output-directory=build', document + '.tex']
                logfile = evidence / f'{document}-round-{round_number}.log'
                with logfile.open('wb') as stream:
                    result = subprocess.run(args, cwd=work, stdout=stream, stderr=subprocess.STDOUT)
                commands.append({'document': document, 'round': round_number, 'actual_exit_code': result.returncode,
                                 'log': logfile.name, 'log_sha256': sha(logfile)})
                if result.returncode:
                    raise RuntimeError(f'LaTeX failed; inspect {logfile}')
            state = b''.join((work / 'build' / f'{d}.{ext}').read_bytes()
                             for d in names for ext in ['aux', 'toc'])
            if previous == state:
                break
            previous = state
        else:
            raise RuntimeError('Cross-references did not stabilize')
        pdfs = []
        for document, name in names.items():
            log = (work / 'build' / (document + '.log')).read_text(errors='replace')
            bad = [line for line in log.splitlines()
                   if re.search(r'Overfull|undefined|multiply defined|Fatal|LaTeX Error', line)]
            if bad:
                raise RuntimeError(f'{document}: remaining layout/reference diagnostics: {bad}')
            pages = int(re.search(r'Output written on .*?\((\d+) pages?', log, re.S)[1])
            shutil.copy2(work / 'build' / (document + '.pdf'), destination / name)
            shutil.copy2(work / 'build' / (document + '.aux'), evidence / (document + '.aux'))
            shutil.copy2(work / 'build' / (document + '.log'), evidence / (document + '.final.log'))
            pdfs.append({'document': document, 'filename': name, 'pages': pages, 'sha256': sha(destination / name)})
    receipt = {'status': 'passed', 'commands': commands, 'cross_references_stable': True,
               'unresolved_or_overfull_diagnostics': [], 'shell_escape': False,
               'source_files': [{'path': str(p.relative_to(source)), 'sha256': sha(p)} for p in files],
               'pdfs': pdfs, 'visual_review': 'pending_separate_render_and_inspection'}
    (evidence / 'build-validation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'latex_executions': len(commands), 'pdfs': pdfs}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'manuscripts/paper-p1/v2.0/pdf')
    parser.add_argument('--evidence-dir', type=Path, required=True)
    args = parser.parse_args()
    build(args.output_dir.resolve(), args.evidence_dir.resolve())
