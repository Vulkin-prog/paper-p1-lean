#!/usr/bin/env python3
"""Read-only integrity of the common-seed preview and its four prior capsules.

Reconstructs the reviewed TeX diff and binds all167 result identities, proof
roles, actual compiled snapshots and delivered PDFs. This does not infer
semantic correctness from hashes or perform a new Lean/LaTeX/Palomar run.
"""
from collections import Counter
from pathlib import PurePosixPath
import argparse
import json
import re
import sys

sys.dont_write_bytecode = True
import check_editorial_previews as prior
import check_scientific_preview as previous

PROPOSAL = prior.PROPOSALS + '/common-seed-simplification'
PACKAGE = 'manuscripts/paper-p1/editorial-unified-preview-2026-11-07'
BASE_PACKAGE = previous.PACKAGE
RECEIPT_SHA256 = 'ccac94dee42d9dea6f925bb59b5583934cfc780334ee9f7429e9a613d7cf1aa5'
PROOF_SOURCE = 'd342b507332315c67b1463009061c03f14b5be9b'
SEED = 'p1:arith:fixed-homogeneous-seeds'
STRONG = {'PaperP1.HomogeneousEffectiveGoodPairExtensions.uniform_mass',
          'PaperP1.HomogeneousTwoEdgeScale.uniform_second',
          'PaperP1.TwoGoodPairMass.nominal_second_eq',
          'PaperP1.FixedHomogeneousSeedTheorem.companion_T1_12'}
require = prior.require


def reviewed_scope(files, record, review):
    bound = review['compiled_scope']
    require(bound['sha256'] == files.sha(record['path'])
            and bound['validation_sha256'] == files.sha(record['validation_path'])
            and bound['types'] == bound['propositions'] == len(review['compiled_entries_read']) == 21,
            'Independent common-seed scope differs')
    require(all(r['verdict'] == 'conforme_au_role_exact_attribue' and r['body_comparison']
                and r['source_commit'] == PROOF_SOURCE for r in review['compiled_entries_read']),
            'Independent common-seed body or proof source differs')
    return prior.scope_snapshot(files, record,
        {'inputs': review['inputs'], 'compiled_entries_read': review['compiled_entries_read']}, 21)


def result_map(files, sources, compiled):
    data = files.json(PROPOSAL + '/preview-result-map.json')
    old = {r['label']: r for r in files.json(previous.PROPOSAL + '/preview-result-map.json')['results']}
    actual = prior.statements(sources)
    base = prior.statements(files.tex(BASE_PACKAGE + '/sources'))
    frozen = prior.statements(files.tex(prior.BASE))
    rows = data['results']
    require(data['package'] == PACKAGE and len(rows) == len({r['label'] for r in rows}) == 167
            and {r['label'] for r in rows} == set(old) == set(actual), 'Unified result map is incomplete')
    require(Counter(r['document'] for r in rows) == {'main': 73, 'companion': 94}, 'Unified result partition differs')
    roles = {SEED: ['FS01'], 'p1:arith:twogoodpositive': ['FS01'],
             'p1:fixed:compressed': ['FS02'], 'p1:arith:palm': ['FS03']}
    for row in rows:
        label = row['label']; before = old[label]
        for key in ['document', 'number', 'proof_source_commit', 'existing_proof_bundle',
                    'scientific_amendments', 'strengthened_or_additional_entry_points']:
            require(row[key] == before[key], 'An inherited proof bundle or scientific amendment changed')
        require(row['source'] == {'path': PACKAGE + '/sources/' + actual[label]['path'],
            'line': actual[label]['line'], 'file_sha256': files.sha(PACKAGE + '/sources/' + actual[label]['path']),
            'statement_sha256': prior.digest(actual[label]['text'].encode())}, 'Unified result locator differs')
        require(row['frozen_v18_statement_unchanged'] == (actual[label]['text'] == frozen[label]['text'])
                and row['strengthened_stage_statement_unchanged'] == (actual[label]['text'] == base[label]['text']),
                'Unified statement disposition differs')
        expected = STRONG if label == SEED else set()
        names = row['common_seed_entry_points']
        require(len(names) == len(set(names)) and set(names) == expected and set(names) <= compiled,
                'Unified strengthened clause lacks its actual strong theorem')
        require(row['common_seed_entry_points_proof_source_commit'] == PROOF_SOURCE
                and row['common_seed_dispositions'] == roles.get(label, []), 'Unified current proof snapshot/role differs')


def verify(files=None):
    files = files or prior.Files()
    previous.verify(files)
    receipt = PROPOSAL + '/final-validation.json'
    require(files.sha(receipt) == RECEIPT_SHA256, 'Published unified receipt changed')
    final = files.json(receipt)
    require(final['package'] == PACKAGE and final['base_package'] == BASE_PACKAGE
            and final['proof_source_commit'] == PROOF_SOURCE
            and final['new_lean_theorems'] == final['new_ledger_entries'] == 0
            and final['historical_mathematical_ledger_entries'] == 1005,
            'Unified preview was counted as a new mathematical replay')
    require(final['palomar_status'] == 'on_hold_at_user_request' and final['registry_scopes_changed'] is False,
            'Registry hold/scope differs')
    review = files.json(files.binding(final['independent_concrete_diff_review']))
    require(review['status'] == 'complete_frozen' and review['proof_source_commit'] == PROOF_SOURCE
            and review['summary']['verdict'] == 'accepte_dans_le_perimetre_mathematique_et_editorial_relu'
            and review['summary']['mathematical_gaps_confirmed'] == review['summary']['necessary_corrections'] == 0
            and not review['necessary_corrections'], 'Unified independent review is not accepted')
    patch = files.binding(final['patch'])
    initial = files.binding(final['frozen_initial_patch_validation'])
    files.binding(final['preliminary_review'])
    manifest = PACKAGE + '/SCIENTIFIC_SOURCE_MANIFEST.json'
    inputs = {PurePosixPath(r['path']).name: r['sha256'] for r in review['inputs']}
    require(review['patch_sha256'] == inputs['common-seed-simplifications.patch'] == files.sha(patch)
            and inputs['patch-validation.json'] == files.sha(initial)
            and inputs['scientific-sources-manifest.json'] == files.sha(manifest), 'Reviewed unified inputs differ')
    before = files.tex(BASE_PACKAGE + '/sources')
    science = prior.apply_patch(before, files.text(patch))
    require(prior.source_hashes(science) == final['scientific_source_sha256'] == files.json(manifest),
            'Unified reviewed scientific source differs')
    pairs = review['mechanical_checks']['changed_file_pairs']
    changed = {p for p in science if science[p] != before[p]}
    require(len(pairs) == len({r['file'] for r in pairs}) == len(changed) == 4
            and {r['file'] for r in pairs} == changed, 'Unified reviewed before/after pairs differ')
    for row in pairs:
        require(row['before_sha256'] == prior.digest(before[row['file']].encode())
                and row['after_sha256'] == prior.digest(science[row['file']].encode()), 'Unified reviewed pair hash differs')
    actual = files.tex(PACKAGE + '/sources')
    require(len(actual) == 48 and actual == prior.presentation_copy(science, 'Unified', 'Strengthened')
            and prior.source_hashes(actual) == final['delivered_source_sha256'], 'Delivered unified manuscript differs')
    plain = ''.join(h + '  ' + p + '\n' for p, h in sorted(prior.source_hashes(actual).items()))
    require(files.text(PACKAGE + '/sources/MANIFEST_SHA256.txt') == plain, 'Unified source manifest differs')
    old, new = prior.statements(before), prior.statements(actual)
    require(old.keys() == new.keys() and {k for k in old if old[k]['text'] != new[k]['text']} == {SEED},
            'Unexpected unified numbered statement change')
    require(prior.labels(before) == prior.labels(actual) and sum(prior.labels(actual).values()) == 548,
            'Unified labels differ')
    for text in actual.values():
        require(all(k in prior.labels(actual) for k in re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}', text)),
                'Unified reference is unresolved')
    saved = sum(len(before[p].splitlines()) - len(science[p].splitlines()) for p in before)
    require(saved == final['net_source_lines_saved_this_pass'] == review['summary']['net_source_lines_saved'] == 51
            and final['net_proof_lines_saved_this_pass'] == 50, 'Unified line saving differs')
    accounting = files.json(PROPOSAL + '/line-accounting.json')
    source = prior.apply_patch(files.tex(prior.BASE),
        files.text(prior.PROPOSALS + '/clarifications-and-finite-examples.patch'))
    measured = []
    for row in accounting['stages']:
        delivered = files.tex(row['delivered_sources'])
        delta = sum(len(source[p].splitlines()) - len(delivered[p].splitlines()) for p in source)
        require(delta == row['physical_lines_saved_from_previous'], 'Cumulative physical line measurement differs')
        measured.append(delta)
        source = delivered
    require(measured == [116, 25, 132, -28, 51]
            and sum(measured) == accounting['net_delivered_physical_source_lines_saved'] == 296
            and accounting['preview_footer_physical_lines_added'] == 4
            and accounting['historical_first_three_scientific_savings'] == sum(measured[:3]) + 4 == 277
            and source == actual, 'Scientific and delivered-source line totals were conflated')
    count = reviewed_scope(files, final['compiled_scope'], review)
    compiled = {r['name'] for r in files.json(final['compiled_scope']['path'])}
    result_map(files, actual, compiled)
    dispositions = files.json(PROPOSAL + '/dispositions.json')
    require([(r['id'], r['status']) for r in dispositions['proposals']] ==
            [('FS01', 'applied'), ('FS02', 'applied'), ('FS03', 'applied'),
             ('FS04', 'retained_required_lemma'), ('FS05', 'retained_scope_guard')], 'Unified proposal disposition differs')
    prior.build_evidence(files, receipt, PACKAGE, (64, 101), 11, 23)
    require(final['actual_total_pages_saved_this_pass'] == 0 and final['actual_total_pages_saved_from_v18'] == 4,
            'Source pruning was counted as an unmeasured page saving')
    return {'status': 'passed', 'prior_capsules': 4, 'numbered_results': 167,
        'current_targeted_propositions': count, 'labels': 548, 'pages': 165,
        'source_lines_saved_this_pass': saved, 'pages_saved_this_pass': 0,
        'historical_full_proof_source': PROOF_SOURCE, 'new_full_replay_claimed': False,
        'palomar_status': final['palomar_status']}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', action='store_true')
    args = parser.parse_args()
    try:
        result = verify()
        print(json.dumps(result, ensure_ascii=False, indent=2) if args.json else
              'Verified unified preview: 167 results,21 existing audited propositions,51 source lines saved;165 pages. Palomar on hold.')
    except (ValueError, KeyError, OSError, UnicodeError, IndexError, TypeError) as error:
        print(f'Unified preview integrity failed: {error}', file=sys.stderr)
        sys.exit(1)
