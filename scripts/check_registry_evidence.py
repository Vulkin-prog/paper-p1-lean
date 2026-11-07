#!/usr/bin/env python3
"""Verify preserved local registry evidence against each immutable source commit.

This checks local receipts, not Palomar's complete workflow or registration.
Historical receipts stay bound to their original source and audit inventory.
"""

import argparse
from functools import lru_cache
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

from update_audit import lean_code
from registry_plan import all_entries, load_plan, receipt_paths

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
AXIOMS = re.compile(
    r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$", re.M
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def validate_audit(text, names):
    require(names and len(names) == len(set(names)), 'Empty or duplicate source inventory')
    found = []
    for match in AXIOMS.finditer(text):
        name, axioms = match.groups()
        actual = {a.strip() for a in (axioms or '').split(',') if a.strip()}
        require(not actual - ALLOWED, f'Forbidden axioms for {name}: {actual - ALLOWED}')
        found.append(name)
    require(len(found) == len(set(found)), 'Repeated theorem output in preserved audit')
    require(set(found) == set(names), 'Preserved audit does not match its source inventory')
    return len(found)


@lru_cache(maxsize=None)
def source_blob(commit, relative):
    path = PurePosixPath(relative)
    require(not path.is_absolute() and '..' not in path.parts, 'Unsafe source-relative path')
    return subprocess.check_output(['git', 'show', f'{commit}:{relative}'], cwd=ROOT)


@lru_cache(maxsize=None)
def changed_sources(commit):
    return set(subprocess.check_output(
        ['git', 'diff', '--name-only', commit, '--', 'PaperP1', 'PaperP1.lean',
         ':(glob)SolutionP1*.lean'],
        cwd=ROOT, text=True,
    ).splitlines())


def check_current_proof_closure(commit, module):
    """Detect changes in actual project imports without blocking unrelated additions."""
    pending = [module]
    seen = set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        relative = name.replace('.', '/') + '.lean'
        require(relative not in changed_sources(commit),
                f'Imported proof source differs from local evidence: {relative}')
        code = lean_code((ROOT / relative).read_text())
        imports = re.findall(r'^(?:(?:public|private)\s+)?import\s+'
                            r'(PaperP1(?:\.[A-Za-z0-9_]+)*|SolutionP1[A-Za-z0-9_]+)\s*$',
                             code, re.M)
        pending.extend(imports)


def check_receipt(path):
    receipt = json.loads(path.read_text())
    source = receipt['source_commit']
    require(re.fullmatch('[0-9a-f]{40}', source), 'Source commit is not immutable')
    require(receipt['status'] == 'local_dual_kernel_passed', 'Unsupported local evidence status')
    checks = receipt['checks']
    for check in [
        'challenge_build', 'solution_build', 'statement_comparison',
        'permitted_axioms_only', 'lean_default_kernel', 'nanoda_kernel', 'bubblewrap_enabled',
    ]:
        require(checks[check] is True, f'Missing passed check: {check}')
    require(type(checks['actual_process_exit_code']) is int and
            checks['actual_process_exit_code'] == 0, 'Comparator did not exit successfully')
    for relative, expected in receipt['files'].items():
        actual = hashlib.sha256(source_blob(source, relative)).hexdigest()
        require(actual == expected, f'Source hash mismatch: {source}:{relative}')
    config = json.loads(source_blob(source, receipt['configuration']))
    require(config['theorem_names'] == receipt['declarations'], 'Declaration selection mismatch')
    require(set(config['permitted_axioms']) == ALLOWED, 'Permitted axiom selection mismatch')
    for module in ['challenge_module', 'solution_module']:
        relative = config[module] + '.lean'
        require((ROOT / relative).read_bytes() == source_blob(source, relative),
                f'Current statement/proof differs from local evidence: {relative}')
    check_current_proof_closure(source, config['solution_module'])
    for relative in ['lean-toolchain', 'lake-manifest.json']:
        require((ROOT / relative).read_bytes() == source_blob(source, relative),
                f'Current compiler/dependency pin differs from local evidence: {relative}')
    require((ROOT / receipt['configuration']).read_bytes() ==
            source_blob(source, receipt['configuration']), 'Current configuration differs from evidence')
    logs = {}
    for item in receipt['logs']:
        relative = PurePosixPath(item['path'])
        require(not relative.is_absolute() and '..' not in relative.parts, 'Unsafe evidence path')
        raw = (ROOT / relative).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == item['sha256'], f'Log hash mismatch: {relative}')
        require(item['kind'] not in logs, 'Duplicate evidence log kind')
        logs[item['kind']] = gzip.decompress(raw).decode('utf-8')
    require(set(logs) == {'comparator', 'full_build', 'axiom_audit'}, 'Incomplete evidence logs')
    comparator = logs['comparator']
    for marker in [
        'nanoda kernel accepts the solution',
        'Lean default kernel accepts the solution', 'Your solution is okay!',
    ]:
        require(marker in comparator, f'Missing actual success marker: {marker}')
    for module in ['challenge_module', 'solution_module']:
        exported = [line for line in comparator.splitlines()
                    if line.startswith('Exporting #[') and line.endswith(' from ' + config[module])]
        require(len(exported) == 1 and all(name in exported[0] for name in receipt['declarations']),
                f'Incomplete actual export: {module}')
    built = re.search(r'Build completed successfully \((\d+) jobs\)', logs['full_build'])
    require(built and int(built[1]) == receipt['full_build_jobs'], 'Full-build job count mismatch')
    inventory = json.loads(source_blob(source, 'docs/axiom-audit-declarations.json'))
    count = validate_audit(logs['axiom_audit'], inventory)
    require(count == receipt['all_audited_theorems'], 'Audit theorem count mismatch')
    require(set(receipt['declarations']) <= set(inventory), 'Selected theorem omitted from source audit')
    return len(receipt['declarations'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--require-all', action='store_true', help='Require a receipt for every candidate')
    args = parser.parse_args()
    total = 0
    receipts = receipt_paths()
    for path in receipts:
        count = check_receipt(path)
        total += count
        print(f'{path.parent.name}: source identities, preserved logs and {count} selections verified.')
    entries = all_entries()
    candidates = [entry['configuration'] for entry in entries]
    if args.require_all:
        expected = {json.loads(p.read_text())['solution_module'] for p in candidates}
        actual = {json.loads(source_blob(json.loads(p.read_text())['source_commit'],
                                       json.loads(p.read_text())['configuration']))['solution_module']
                  for p in receipts}
        require(actual == expected, 'Not every candidate has complete local qualification evidence')
    if load_plan() is not None:
        for kind in ['registration', 'component']:
            expected = {str(entry['metadata'].with_name('qualification.json'))
                        for entry in entries if entry['kind'] == kind}
            found = [path for path in receipts if str(path) in expected]
            declarations = sum(len(json.loads(path.read_text())['declarations']) for path in found)
            print(f'Verified {len(found)}/{len(expected)} local {kind} receipts and {declarations} selected declarations.')
        print('Only the six consolidated registrations are planned for submission; the seventeen component receipts remain proof evidence.')
    else:
        print(f'Verified {len(receipts)}/{len(candidates)} local component receipts and {total} selected declarations.')
    print('Scope: local evidence integrity; complete Palomar workflow and registration remain separate.')


if __name__ == '__main__':
    main()
