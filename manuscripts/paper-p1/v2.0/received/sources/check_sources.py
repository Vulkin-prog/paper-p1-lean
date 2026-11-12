#!/usr/bin/env python3
"""Check active TeX inputs, references and control characters in this edition."""
from pathlib import Path
import collections
import json
import re
import sys

ROOT = Path(__file__).resolve().parent

def visit(name, files):
    p = ROOT / name
    if p in files:
        return
    text = p.read_text()
    files[p] = text
    for child in re.findall(r'\\input\{([^}]+)\}', text):
        visit(child if child.endswith('.tex') else child + '.tex', files)

def main():
    files = {}
    visit('main.tex', files)
    visit('companion.tex', files)
    labels = collections.defaultdict(list)
    refs = collections.defaultdict(list)
    errors = []
    for path, text in files.items():
        name = str(path.relative_to(ROOT))
        for label in re.findall(r'\\label\{([^}]+)\}', text):
            labels[label].append(name)
        for label in re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}', text):
            refs[label].append(name)
        if any(ord(c) < 32 and c not in '\n\t' for c in text):
            errors.append(f'Unexpected control character: {name}')
    errors.extend(f'Duplicate label {key}: {values}' for key, values in labels.items() if len(values) > 1)
    errors.extend(f'Undefined label {key}: {values}' for key, values in refs.items() if key not in labels)
    result = {'active_tex_files': len(files), 'labels': len(labels),
              'reference_targets': len(refs), 'errors': errors,
              'scope': 'Source integrity only; not a mathematical proof or Lean replay.'}
    print(json.dumps(result, indent=2))
    return bool(errors)

if __name__ == '__main__':
    sys.exit(main())
