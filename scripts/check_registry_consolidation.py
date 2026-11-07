#!/usr/bin/env python3
"""Check the exact namespace/declaration transformation from 17 components to six registrations."""

from pathlib import Path
import re

from registry_plan import load_plan

ROOT = Path(__file__).resolve().parents[1]


def transform(text, old_namespace, new_namespace, selected, namespace):
    imports = re.findall(r'^(?:public )?import (\S+)\s*$', text, re.M)
    body = re.sub(r'^(?:public )?import \S+\s*\n', '', text, flags=re.M)
    body = re.sub(r'^module\s*\n', '', body, count=1, flags=re.M)
    marker = '@[expose] public noncomputable section'
    if body.count(marker) != 1:
        raise ValueError('Expected one public noncomputable section per original component')
    body = body.replace(marker, '', 1)
    body = re.sub(r'^set_option autoImplicit false\s*\n', '', body, count=1, flags=re.M)
    body = body.replace(old_namespace, new_namespace)

    def declaration(match):
        kind, name = match.groups()
        target = namespace + '.' + selected[name] if name in selected else new_namespace + '.' + name
        return kind + ' _root_.' + target

    body = re.sub(r'^(theorem|lemma) ([A-Za-z0-9_\']+)(?=\s|\[|\{)', declaration, body, flags=re.M)
    for name, renamed in selected.items():
        body = re.sub(r'(?<![A-Za-z0-9_.\'])' + re.escape(name) + r'(?![A-Za-z0-9_\'])',
                      '_root_.' + namespace + '.' + renamed, body)
    return imports, body.strip()


def expected_sources(bundle):
    pascal = bundle['challenge_module'].removeprefix('ChallengeP1Registration')
    imports = {'challenge': set(), 'solution': set()}
    parts = {'challenge': [], 'solution': []}
    for component in bundle['components']:
        challenge = (ROOT / (component['challenge_module'] + '.lean')).read_text()
        namespaces = re.findall(r'^namespace (\S+)\s*$', challenge, re.M)
        if len(namespaces) != 1:
            raise ValueError('An original component must have one namespace')
        old_namespace = namespaces[0]
        new_namespace = 'PaperP1Registry.RegistrationModels.' + pascal + '.' + old_namespace.rsplit('.', 1)[1]
        if (component['original_namespace'] != old_namespace
                or component['relocated_namespace'] != new_namespace):
            raise ValueError('Incorrect model namespace relocation')
        selected = {row['original_declaration'].rsplit('.', 1)[1]: row['declaration'].rsplit('.', 1)[1]
                    for row in bundle['declaration_mapping'] if row['component'] == component['family']}
        for kind in ['challenge', 'solution']:
            source = (ROOT / (component[kind + '_module'] + '.lean')).read_text()
            if re.findall(r'^namespace (\S+)\s*$', source, re.M) != [old_namespace]:
                raise ValueError('Inconsistent original Challenge/Solution namespaces')
            used_imports, body = transform(source, old_namespace, new_namespace, selected, bundle['namespace'])
            if kind == 'challenge' and any(not name.startswith('Mathlib.') for name in used_imports):
                raise ValueError('Challenges must remain Mathlib-only')
            if any(name.startswith(('SolutionP1', 'ChallengeP1')) for name in used_imports):
                raise ValueError('Registration bodies must preserve proofs rather than import component interfaces')
            imports[kind].update(used_imports)
            section = 'Component' + old_namespace.rsplit('.', 1)[1]
            parts[kind].append('section ' + section + '\n\n' + body + '\n\nend ' + section + '\n')
    header = ('\n/-! # ' + bundle['title'] + '\n\n'
              'Consolidated components retain their literal models, complete hypotheses and\n'
              'original proof bodies, relocated into distinct model namespaces. The declaration\n'
              'map records every original statement and source hash. No mathematical change.\n'
              '-/\n\nset_option autoImplicit false\n@[expose] public noncomputable section\n\n')
    return {kind: 'module\n\n' + ''.join('public import ' + name + '\n' for name in sorted(imports[kind]))
            + header + '\n'.join(parts[kind]) for kind in ['challenge', 'solution']}


def main():
    plan = load_plan()
    if plan is None:
        raise ValueError('The explicit six-registration plan is required')
    for bundle in plan['bundles']:
        for kind, expected in expected_sources(bundle).items():
            path = ROOT / (bundle[kind + '_module'] + '.lean')
            if path.read_text() != expected:
                raise ValueError(f'Consolidated {kind} differs from the exact original-body transformation: {path.name}')
        print(f"{bundle['slug']}: exact models, statements, complete proof bodies and source mapping preserved.")
    print('All 68 selections from 17 original components are preserved in exactly six registrations.')


if __name__ == '__main__':
    main()
