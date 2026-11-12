#!/usr/bin/env python3
"""Read-only integrity and clause checks for the aligned P1 V2 edition.

Checks recorded proof/source/type bindings, not a formal translation of TeX.
No Lean process, PDF authoring, network access or Palomar submission occurs.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json
import re
import zipfile

from check_manuscript_endpoints import source_locations

ROOT = Path(__file__).resolve().parents[1]
INDEX = 'docs/manuscript-results-v2.0.json'
PACKAGE = 'manuscripts/paper-p1/v2.0'
EVIDENCE = 'docs/validation/v2.0'
PATTERN = re.compile(r'\\begin\{(theorem|proposition|lemma|corollary)\}.*?\\end\{\1\}', re.S)
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
ARCHIVE_SHA = '60a6a2557750ee96e280714d826bbcaf60e430f9a234e04c9e01124a7f30012d'
OVERRIDES = {
    'p2:homogeneous:envelope': ['PaperP1.V2HomogeneousEnvelope.finite_domination', 'PaperP1.V2HomogeneousEnvelope.uniform_nominal_comparison'],
    'p13:transfer:primitive': ['PaperP1.FixedArityHomogeneousMass.uniform_all_bounds'],
    'p13:transfer:independent-tail': ['PaperP1.FixedCutoffIndependentTail.uniform_tail', 'PaperP1.CompressedBlockIndependentTail.uniform_channel'],
    'p1:arith:palm': ['PaperP1.AllTargetGoodEdgePalm.companion_T10_5', 'PaperP1.AllTargetGoodEdgePalm.principal_channels', 'PaperP1.GoodEdgePositivePalm.mass_eq_excess_sum'],
    'p1:fixed:primitive': ['PaperP1.SharpOrderedPrimitiveMass.companion_T4_7'],
    'p1:uniform:full-support': ['PaperP1.UniformFullSupportCount.companion_T13_1'],
    'p1:arith:fixed-homogeneous-seeds': ['PaperP1.V2FixedHomogeneousSeeds.companion_T1_12'],
    'p13:rig:local-square': ['PaperP1.LocalSquareThreshold.companion_T9_1', 'PaperP1.LocalSquareThreshold.local_square_threshold_power_five'],
    'p1:arith:fixed-support': ['PaperP1.BlockSupportCount.companion_T1_14', 'PaperP1.BlockSupportParameters.companion_T1_14', 'PaperP1.SeveralWindowProjectionCount.companion_T1_14', 'PaperP1.BlockSupportCount.critical_interval_count', 'PaperP1.BlockSupportParameters.critical_count'],
    'p1:fixed:compressed': ['PaperP1.FixedCompressedPrimitiveTheorem.companion_T4_4', 'PaperP1.EffectiveCompressedPrimitiveMass.uniform_mass', 'PaperP1.HomogeneousEffectiveGoodPairExtensions.uniform_mass', 'PaperP1.HomogeneousEffectiveConnectedChannel.uniform_mass', 'PaperP1.HomogeneousRunMass.actual_joint_le', 'PaperP1.HomogeneousRunMass.probability_rank'],
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def local(name):
    path = ROOT / name
    require(not Path(name).is_absolute() and path.resolve().is_relative_to(ROOT.resolve()), 'Nonlocal evidence path')
    return path


def read_json(name):
    return json.loads(local(name).read_text())


def binding(record, key='sha256'):
    require(digest(local(record['path']).read_bytes()) == record[key], f"Changed evidence: {record['path']}")


def statements(directory):
    rows = {}
    for path in sorted(local(directory).rglob('*.tex')):
        text = path.read_text()
        for match in PATTERN.finditer(text):
            labels = re.findall(r'\\label\{([^}]+)\}', match[0])
            require(bool(labels) and labels[0] not in rows, 'Missing/duplicate result label')
            rows[labels[0]] = {'path': str(path.relative_to(ROOT)), 'line': text[:match.start()].count('\n') + 1,
                               'file_sha256': digest(path.read_bytes()), 'statement_sha256': digest(match[0].encode()),
                               'statement': match[0], 'aliases': labels[1:]}
    return rows


def normalized(types, name, binders=None):
    row = types[name]
    require(row['kind'] == 'theorem' and row['is_proposition'] is True, f'An object is not proof evidence: {name}')
    if binders is not None:
        require([b['name'] for b in row['binders']] == binders, f'Changed leading assumptions: {name}')
    return ' '.join(row['type'].split())


def check_semantics(types):
    """Guard the critical quantifiers/weights against known weaker substitutes."""
    palm = normalized(types, 'PaperP1.AllTargetGoodEdgePalm.companion_T10_5',
                      ['a', 'b', 'D', 'ha', 'hab', 'hb2a', 'hcop', 'C', 'ε', 'hε'])
    require('RegularStarts' not in palm and '∀ G ⊆ PaperP1.Model.dyadicBlock N' in palm, 'Palm targets must include every dyadic window')
    require(palm.index('∃ N₀') < palm.index('∀ G'), 'Palm threshold must precede target choice')
    for term in ['6 * b * (L + 1) ≤ H', 'H ≤ D * (L + 1)', '0 < PaperP1.GoodEdgePositivePalm.beta',
                 'AllTargetGoodEdgePalm.combinedMass', 'AllTargetGoodEdgePalm.normalized', '-41 / 30 + ε', '-11 / 30 - 1 / ↑b + ε']:
        require(term in palm, 'Missing all-target Palm clause: ' + term)
    support = normalized(types, 'PaperP1.UniformFullSupportCount.companion_T13_1', ['C', 'u', 'ε', 'hu', 'hε'])
    require(support.index('∃ N₀') < support.index('∀ G') < support.index('∀ (s : ℕ)'), 'Support threshold must be uniform in s and G')
    for term in ['-Min.min (↑s / 2) 2 + ε', 'u ^ r / ↑r.factorial', 'FullSupportOrderedLists.manuscriptLists', '(2 ^ L)⁻¹ ^ r']:
        require(term in support, 'Changed independent count or exponent: ' + term)
    ordered = normalized(types, 'PaperP1.SharpOrderedPrimitiveMass.companion_T4_7', ['r', 'hr', 'C', 'ε', 'hε'])
    require(ordered.count('↑N ^ (-↑r / 2 + ε)') == 3, 'All three ordered primitive weights need the sharp exponent')
    for term in ['PrimitiveOrderedMass.mass', 'infiniteJointMoment', '|PaperP1.Model.InfiniteStarts.infiniteCenteredCoefficient']:
        require(term in ordered, 'Missing ordered primitive weight')
    cap = normalized(types, 'PaperP1.V2HomogeneousEnvelope.uniform_nominal_comparison', ['C'])
    require('2 ^ I.card * PaperP1.PrimitiveNominalMass.weight' in cap, 'Growing-order factor 2^|I| was dropped')
    require(cap.index('∃ N₀') < cap.index('∀ I'), 'Nominal comparison must hold for all families after one threshold')
    envelope = normalized(types, 'PaperP1.V2HomogeneousEnvelope.finite_domination', ['L', 'hL', 'I', 'hne'])
    for term in ['Module.finrank', 'relativeNullityOn', 'PrimitiveWindowMass.weight', 'infiniteJointMoment', 'infiniteCenteredCoefficient']:
        require(term in envelope, 'Missing finite envelope conclusion')
    fixed = normalized(types, 'PaperP1.FixedArityHomogeneousMass.uniform_all_bounds', ['r', 'hr', 'C', 'η', 'ε', 'hη', 'hε'])
    require(fixed.index('∃ N₀') < fixed.index('∀ (F :'), 'Fixed-arity subfamilies must follow the threshold')
    require(fixed.count('↑N ^ (-↑r / 2 + ε)') == 4 and fixed.count('↑N ^ (1 - ↑r + ε)') == 4 and '↑F.card ≤ ↑N ^ ε' in fixed,
            'Missing global/dense four-weight or dense-host clause')
    tail = normalized(types, 'PaperP1.FixedCutoffIndependentTail.uniform_tail')
    require(tail.index('∃ s') < tail.index('∃ N₀') < tail.index('∀ N'), 'Tail cutoff/threshold order changed')
    require(tail.count('↑N ^ (-a)') == 2 and 'a < 2' in tail and '∀ (U : ℕ → Finset ℕ)' in tail, 'The independent tail must retain both pure subcritical bounds')
    seeds = normalized(types, 'PaperP1.V2FixedHomogeneousSeeds.companion_T1_12', ['C', 'D'])
    require(seeds.index('∃ A') < seeds.index('∀ (ε :') < seeds.index('∃ N₀') < seeds.index('∀ G'), 'The fixed raw/two-edge constant must precede epsilon')
    require(seeds.count('↑N ^ (-41 / 30 + ε)') == 2 and 'TwoGoodPairMass.nominalSecond' in seeds, 'The raw seed clauses must retain41/30 and the two-edge scale')
    transfer = normalized(types, 'PaperP1.FiniteCompleteLawTransfer.article_15_13')
    require('FiniteConnectedActivity254.Hypothesis C β → ∃ N₀' in transfer, 'The printed finite-transfer premise must remain explicit')


def check_partition(index, old):
    rows, retired = index['results'], index['retired_historical_results']
    require(len(rows) == 118 and Counter(r['document'] for r in rows) == {'main': 26, 'companion': 92}, 'V2 must contain26+92 results')
    labels = [r['label'] for r in rows]
    gone = [r['label'] for r in retired]
    require(len(set(labels)) == 118 and len(gone) == len(set(gone)) == 50, 'Duplicate/missing current or retired result')
    require(set(labels) - set(old) == {'p2:homogeneous:envelope'}, 'The unique new result identity changed')
    require(set(gone) == set(old) - set(labels) and not set(gone) & set(labels), 'Current/historical partition changed')
    require(all(r['invalidated_by_v2'] is False and r['disposition'] == 'outside_v2_scalar_count_scope_preserved_historically' for r in retired),
            'Retired results were removed from scope, not invalidated')
    for row in rows:
        label = row['label']
        names = [e['name'] for e in row['entry_points']]
        expected = OVERRIDES.get(label, [e['name'] for e in old[label]['entry_points']] if label in old else [])
        require(names == expected and len(set(names)) == len(names), 'Incomplete clause bundle: ' + label)
        require(row['printed_conditional_clause'] is (label == 'p13:transfer:finite'), 'Changed printed conditional disposition')
        require(row['status'] == 'proved_as_printed_with_recorded_context', 'Result is not aligned and replayed')
    require(index['palomar_status'] == 'on_hold_at_user_request', 'Palomar hold changed')
    require(len(index['auxiliary_claims']) == 9 and len({r['id'] for r in index['auxiliary_claims']}) == 9, 'Missing retained auxiliary claim')
    require(index['counts'] == {'main': 26, 'companion': 92, 'total': 118, 'retained': 117, 'new': 1, 'retired_historical': 50, 'unchanged_from_unified': 107, 'changed_from_unified': 10}, 'V2 accounting changed')


def verify():
    index = read_json(INDEX)
    old = {r['label']: r for r in read_json('docs/manuscript-endpoints-v1.8.json')['results']}
    check_partition(index, old)
    actual = statements(PACKAGE + '/sources')
    require(set(actual) == {r['label'] for r in index['results']}, 'Source labels/index differ')
    raw = read_json(PACKAGE + '/RECEIVED_PROVENANCE.json')
    for name, expected in raw['received_files_sha256'].items():
        require(digest(local(PACKAGE + '/received/' + name).read_bytes()) == expected, 'Received dossier changed: ' + name)
    received = {str(p.relative_to(local(PACKAGE + '/received'))) for p in local(PACKAGE + '/received').rglob('*') if p.is_file()}
    require(received == set(raw['received_files_sha256']) and len(received) == 55, 'Received dossier file set changed')
    archive = local(PACKAGE + '/' + raw['archive']['path'])
    require(digest(archive.read_bytes()) == index['received_archive_sha256'] == raw['archive']['sha256'] == ARCHIVE_SHA, 'Original V2 archive changed')
    with zipfile.ZipFile(archive) as z:
        require(z.testzip() is None and len([r for r in z.infolist() if not r.is_dir()]) == 55, 'Original archive integrity failed')
        zipped = {'/'.join(r.filename.split('/')[1:]): digest(z.read(r)) for r in z.infolist() if not r.is_dir()}
        require(zipped == raw['received_files_sha256'], 'Received bytes differ from the original archive')
    build = read_json(EVIDENCE + '/pdf/build-validation.json')
    for f in build['source_files']:
        require(digest(local(PACKAGE + '/sources/' + f['path']).read_bytes()) == f['sha256'], 'Active source differs from built source')
    active = {str(p.relative_to(local(PACKAGE + '/sources'))) for p in local(PACKAGE + '/sources').rglob('*.tex')}
    require(active == {r['path'] for r in build['source_files']} and len(active) == 32, 'Active TeX set changed')
    changed = {name for name in active if local(PACKAGE + '/sources/' + name).read_bytes() != local(PACKAGE + '/received/sources/' + name).read_bytes()}
    require(changed == {'formalization.tex'}, 'Unexpected scientific/editorial source change after received V2')
    validation = read_json(EVIDENCE + '/validation.json')
    require(validation['status'] == 'passed' and validation['actual_process_exit_codes'] == {'build': 0, 'audit': 0, 'references': 0}, 'Complete actual Lean replay did not pass')
    require(validation['source_commit'] == index['proof_source_commit'], 'Index/replay proof source differs')
    for log in validation['logs']:
        binding(log, 'sha256_gzip')
    binding(index['proof_source_manifest'])
    manifest = read_json(index['proof_source_manifest']['path'])
    require(manifest['validated_source_commit'] == index['proof_source_commit'], 'Proof manifest source differs')
    expected_proofs = set((ROOT / 'PaperP1').rglob('*.lean')) | set(ROOT.glob('*.lean')) | {ROOT / p for p in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']}
    current = sorted([{'path': str(p.relative_to(ROOT)), 'sha256': digest(p.read_bytes())} for p in expected_proofs], key=lambda r: r['path'])
    require(manifest['files'] == current, 'Proof source/pin snapshot differs')
    require((ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.36.0-rc2', 'Compiler pin changed')
    binding(index['compiled_scope'])
    types = {r['name']: r for r in read_json(index['compiled_scope']['path'])}
    scope = read_json(EVIDENCE + '/v2-scope/compiled-types-validation.json')
    require(scope['actual_exit_code'] == 0 and scope['all_propositions_standard_axioms_only'] is True and scope['compiled_types_sha256'] == index['compiled_scope']['sha256'], 'V2 compiled-type replay failed')
    require(digest(local(EVIDENCE + '/v2-scope/compiled-types.log').read_bytes()) == scope['log_sha256'] and local(EVIDENCE + '/v2-scope/compiled-types.exit').read_text().strip() == '0', 'Compiled-type log/exit differs')
    allrows = index['results'] + index['auxiliary_claims']
    names = sorted({e['name'] for r in allrows for e in r['entry_points']})
    require(names == read_json(EVIDENCE + '/v2-scope-declarations.json') and set(names) == set(types) and scope['compiled_types'] == scope['propositions_audited'] == len(names) == 212, 'V2 must bind its complete 212 proposition endpoints')
    audit = set(read_json('docs/axiom-audit-declarations.json'))
    locations = source_locations()
    aux = {}
    for document in ['main', 'companion']:
        aux[document] = {
            label: (number, page) for label, number, page in re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]*)\}\{([^}]*)\}', local(EVIDENCE + '/pdf/' + document + '.aux').read_text())}
    for row in index['results']:
        require(row['source'] == actual[row['label']], 'Statement bytes/locator changed: ' + row['label'])
        require(aux[row['document']][row['label']] == (row['number'], row['page']), 'Compiled PDF number/page mismatch')
        for e in row['entry_points']:
            name = e['name']
            require(name in audit and types[name]['kind'] == 'theorem' and types[name]['is_proposition'] is True, 'A definition/unaudited declaration is being counted as proof')
            require(all(e[k] == locations[name][k] for k in ['source', 'line', 'source_sha256']), 'Proof source binding changed: ' + name)
            require(e['compiled_type_sha256'] == digest(types[name]['type'].encode()), 'Compiled type binding changed: ' + name)
    for row in index['auxiliary_claims']:
        source = row['source']
        text = local(source['path']).read_text()
        require(digest(text.encode()) == source['file_sha256'] and text[:text.index(source['anchor'])].count('\n') + 1 == source['line'], 'Auxiliary source anchor differs')
        require(row['semantic_alignment_status'] == 'passed', 'Auxiliary scope is incomplete')
        for e in row['entry_points']:
            name = e['name']
            require(name in audit and types[name]['kind'] == 'theorem' and types[name]['is_proposition'] is True, 'Auxiliary object is not a theorem')
            require(all(e[k] == locations[name][k] for k in ['source', 'line', 'source_sha256']), 'Auxiliary proof source changed')
            require(e['compiled_type_sha256'] == digest(types[name]['type'].encode()), 'Auxiliary type changed')
    check_semantics(types)
    require(build['status'] == 'passed' and build['cross_references_stable'] is True and build['unresolved_or_overfull_diagnostics'] == [] and len(build['commands']) == 6 and all(c['actual_exit_code'] == 0 for c in build['commands']), 'PDF build did not pass')
    for record in build['pdfs']:
        require(digest(local(PACKAGE + '/pdf/' + record['filename']).read_bytes()) == record['sha256'], 'Built PDF changed')
    visual = read_json(EVIDENCE + '/pdf/visual-review.json')
    require(visual['status'] == 'passed' and visual['all_pages_inspected_in_contact_sheets'] is True and visual['pages'] == {'main': 32, 'companion': 84}, 'Visual review is incomplete')
    for record in visual['pdfs']:
        require(record in build['pdfs'], 'Visual review uses a different PDF')
    for record in visual['images']:
        binding(record)
    for document in ['main', 'companion']:
        record = visual['aux'][document]
        binding(record)
    print('P1 V2 integrity passed:118 results, 212 proposition endpoints, 50 historical results preserved; Palomar on hold.')


if __name__ == '__main__':
    verify()
