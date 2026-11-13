#!/usr/bin/env python3
"""Check archived public Palomar records against the 26-result publication scope.

Offline integrity and correspondence audit, without credentials or network calls.
This does not rerun Lean, replace the editorial review, or redeliver private
review bytes. Frozen preparation receipts and manuscript indices stay unchanged.
"""
import argparse
import datetime
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PLAN = 'palomar/REGISTRATION_PLAN_PUBLICATION.json'
STATE = 'palomar/publication/CYCLE_STATE.json'
REPOSITORY = 'Vulkin-prog/paper-p1-lean'
TOOLCHAIN = 'leanprover/lean4:v4.36.0-rc2'
PERSON = {'name': 'Brice Pouly', 'github': 'Vulkin-prog',
          'orcid': '0009-0008-8491-2467'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def local(root, relative):
    path = (root / relative).resolve()
    require(path.is_relative_to(root.resolve()) and path.is_file(),
            'Missing or nonlocal evidence: ' + str(relative))
    return path


def load(root, relative):
    return json.loads(local(root, relative).read_text())


@lru_cache(maxsize=None)
def committed(root, commit, relative):
    require(re.fullmatch('[0-9a-f]{40}', commit), 'Invalid source commit')
    return subprocess.check_output(['git', 'show', commit + ':' + relative], cwd=root)


def validate_allocation(plan, index):
    count = plan.get('planned_registrations', 6)
    total = plan['selected_theorem_count']
    require(plan['maximum_registrations'] == 6 and plan['main_result_count'] == 26
            and (count, total) in {(6, 52), (5, 42)}, 'Unexpected publication scope')
    bundles = {item['slug']: item for item in plan['bundles']}
    sequence = plan['submission_sequence']
    require(len(bundles) == len(plan['bundles']) == len(sequence) == count
            and set(sequence) == set(bundles), 'Nonbijective dossier allocation')
    results = {item['label']: item for item in index['results'] if item['document'] == 'main'}
    require(len(results) == index['counts']['main'] == 26, 'Unexpected article index')
    labels, selections = [], []
    for bundle in bundles.values():
        names = bundle['selected_declarations']
        require(len(names) == len(set(names)), 'Duplicate selection in a dossier')
        selections.extend(names)
        for item in bundle['main_results']:
            label = item['label']
            require(label in results, 'Unindexed main result: ' + label)
            original = results[label]
            require(item['number'] == original['number']
                    and item['statement_sha256'] == original['source']['statement_sha256']
                    and item['source'] == original['source']['path'], 'Changed printed statement: ' + label)
            require(item['printed_conditional_clause'] == original['printed_conditional_clause'],
                    'Printed conditional scope changed: ' + label)
            require(item['selected_declarations'] and set(item['selected_declarations']) <= set(names),
                    'Unselected clause endpoint: ' + label)
            labels.append(label)
    require(len(labels) == len(set(labels)) == 26 and set(labels) == set(results),
            'The main article is not covered exactly once')
    require(len(selections) == len(set(selections)) == total,
            'The selected declaration allocation is not bijective')
    return bundles, results


def validate_public_entry(entry, versions, cycle, bundle, config):
    registration = cycle['registration']
    require(entry['schema_version'] == 5 and entry['status'] == 'registered',
            'Not an issued public registration')
    require(entry['id'] == registration['id']
            and re.fullmatch(r'PALOMAR-\d{4}-\d{2}-\d{2}-\d{6}', entry['id'])
            and entry['version'] == registration['version'], 'Wrong public identity/version')
    require(versions['id'] == entry['id'] and any(
        item.get('version') == entry['version'] and item.get('status') == 'registered'
        and item.get('path') == f"entries/{entry['id']}-v{entry['version']}.json"
        for item in versions['entries']), 'Public version index mismatch')
    source, formal = entry['source'], entry['formalization']
    require(source['repository'] == REPOSITORY and source['commit'] == cycle['source_commit']
            and source['project_path'] == cycle['project_path'], 'Wrong registered source')
    require(formal['comparator_config_path'] == cycle['comparator_config_path'] == bundle['configuration']
            and formal['formalization_metadata_path'] == cycle['formalization_metadata_path'],
            'Wrong registered configuration or metadata')
    require(formal['challenge_path'] == bundle['challenge']
            and formal['solution_path'] == bundle['solution'], 'Wrong registered statement/proof file')
    require(formal['theorem_names'] == config['theorem_names'] == bundle['selected_declarations']
            and formal['definition_names'] == config.get('definition_names', []) == [],
            'Registered declaration selection differs')
    require(formal['lean_toolchain'] == TOOLCHAIN
            and set(formal['permitted_axioms']) == set(config['permitted_axioms'])
            == {'propext', 'Quot.sound', 'Classical.choice'}, 'Wrong compiler or axioms')
    groups = [entry['authors'], entry['provenance']['responsible_maintainers']]
    groups += [item['authors'] for item in entry['provenance']['mathematical_sources']
               if item.get('relationship') == 'formalizes']
    require(len(groups) >= 3 and all(len(group) == 1 and all(
        group[0].get(key) == value for key, value in PERSON.items()) for group in groups),
            'Author, maintainer or mathematical-source ORCID mismatch')
    require(entry['submission']['authorization']['relationship'] == 'maintainer',
            'Wrong recorded authorization relationship')


def mechanical_evidence(root, cycle, field, profile):
    reference = cycle[field]
    receipt = load(root, reference['validation_receipt'])
    require(receipt['status'] == 'pass' and receipt['source_commit'] == cycle['source_commit']
            and receipt['run_id'] == reference['workflow_run_id'], 'Wrong mechanical receipt')
    path = local(root, receipt['report_path'])
    require(sha(path.read_bytes()) == receipt['report_sha256'], 'Mechanical report bytes changed')
    report = json.loads(path.read_text())
    require(report['schema_version'] == 2 and report['status'] == 'pass'
            and report['phase'] == 'verification' and report['stage'] == 'complete'
            and report['errors'] == [], 'Incomplete mechanical verification')
    require(report['source']['repository'] == REPOSITORY
            and report['source']['commit'] == cycle['source_commit']
            and report['source']['project_path'] == cycle['project_path']
            and report['execution_profile'] == profile
            and report['lean_toolchain'] == TOOLCHAIN
            and report['workflow_url'] == receipt['workflow_url'], 'Mechanical source/profile mismatch')
    require(report['submission']['requested_paths'] == {key: cycle[key] for key in
            ['project_path', 'comparator_config_path', 'formalization_metadata_path']},
            'Mechanical report is for another dossier')
    require(report['submission']['authorization']['relationship'] == 'maintainer'
            and 'nanoda' in {item['name'] for item in report['kernels']},
            'Missing full native verification evidence')
    require(report['challenge']['untrusted_sources'] == []
            and report['challenge']['transitive_source_count'] > 0, 'Noncanonical Challenge provenance')
    for item in ['comparator', 'formalization', 'challenge', 'solution', 'lakefile', 'lake_manifest']:
        evidence = report[item]
        require(sha(committed(str(root), cycle['source_commit'], evidence['path'])) == evidence['sha256'],
                'Mechanical source bytes differ: ' + item)
    if receipt.get('artifact_path'):
        require(sha(local(root, receipt['artifact_path']).read_bytes()) == receipt['artifact_sha256'],
                'Archived mechanical ZIP changed')
    return receipt, report


def validate_render_report(root, report, receipt, cycle, bundle, config):
    require(report['schema_version'] == 3 and report['status'] == 'pass'
            and report['stage'] == 'complete' and report['errors'] == [], 'Incomplete Challenge rendering')
    source = report['source']
    require(source['repository'] == REPOSITORY and source['commit'] == cycle['source_commit']
            and source['project_path'] == cycle['project_path']
            and source['comparator_config_path'] == bundle['configuration']
            and source['challenge_path'] == bundle['challenge']
            and source['solution_path'] == bundle['solution'], 'Another rendered dossier')
    require(source['challenge_sha256'] == sha(committed(str(root), cycle['source_commit'], bundle['challenge']))
            and report['lean_toolchain'] == TOOLCHAIN
            and report['renderer_commit'] == receipt['renderer_commit']
            and report['workflow_url'] == receipt['workflow_url']
            and report['artifact_tree_sha256'] == receipt['artifact_tree_sha256'], 'Rendered source/producer mismatch')
    names = config['theorem_names']
    require(sorted(report['surface']['declarations']) == sorted(names)
            and sorted(item['name'] for item in report['surface']['audit_declarations']) == sorted(names),
            'Rendered selected declarations differ')


def inspect(root=ROOT, require_all=False):
    root = root.resolve()
    state = load(root, STATE)
    active_plan = state.get('active_plan', PLAN)
    require(active_plan in {PLAN, 'palomar/REGISTRATION_PLAN_FINAL.json'}, 'Unsupported active allocation')
    plan = load(root, active_plan)
    index = load(root, plan['source_index'])
    baseline = state.get('allocation_source_commit', state['preparation_snapshot_commit'])
    for path in [active_plan, plan['source_index']]:
        require(sha(local(root, path).read_bytes()) == sha(committed(str(root), baseline, path)),
                'Frozen publication allocation/index changed: ' + path)
    bundles, _ = validate_allocation(plan, index)
    require(state['repository'] == REPOSITORY and state['maximum_registrations'] == 6
            and [item['slug'] for item in state['cycles']] == plan['submission_sequence'],
            'Live cycle sequence differs from the publication allocation')
    rows, records, selected = [], [], []
    pending_seen = False
    for cycle in state['cycles']:
        bundle = bundles[cycle['slug']]
        require(cycle['selected_theorem_count'] == len(bundle['selected_declarations']),
                'Live selection count differs')
        registration = cycle.get('registration')
        if registration is None:
            pending_seen = True
        else:
            require(not pending_seen and registration['status'] == 'registered_and_publicly_verified',
                    'Completed registrations do not form the successive prefix')
            receipt = load(root, registration['public_data_receipt'])
            require(receipt['status'] == 'verified_registered'
                    and receipt['source_commit'] == cycle['source_commit'], 'Missing public readback')
            entry_path = local(root, receipt['entry_path'])
            require(sha(entry_path.read_bytes()) == receipt['entry_sha256'], 'Public entry bytes changed')
            entry = json.loads(entry_path.read_text())
            versions = json.loads((entry_path.parent / 'versions.json').read_text())
            config = json.loads(committed(str(root), cycle['source_commit'], bundle['configuration']))
            validate_public_entry(entry, versions, cycle, bundle, config)
            url = f"https://palomar-registry.org/entry.html?id={entry['id']}&version={entry['version']}"
            require(registration['url'] == receipt['registry_url'] == url, 'Wrong public URL')
            _, full_report = mechanical_evidence(root, cycle, 'preflight', 'palomar-standard-v1')
            mechanical, server_report = mechanical_evidence(root, cycle, 'palomar_verification',
                                                           'palomar-namespace-16x32-v1')
            require(full_report['comparator']['theorem_names'] == server_report['comparator']['theorem_names']
                    == config['theorem_names'], 'Mechanical selection mismatch')
            for report in [full_report, server_report]:
                require(report['comparator']['path'] == bundle['configuration']
                        and report['formalization']['path'] == cycle['formalization_metadata_path']
                        and report['challenge']['path'] == bundle['challenge']
                        and report['solution']['path'] == bundle['solution']
                        and report['comparator']['definition_names'] == config.get('definition_names', [])
                        and set(report['comparator']['permitted_axioms']) == set(config['permitted_axioms']),
                        'Mechanical statement/proof interface differs')
            require(entry['verification']['mechanical_report_sha256'] == mechanical['report_sha256']
                    and entry['verification']['run_id'] == mechanical['run_id']
                    and entry['verification']['workflow_commit'] == state['cycles'][0]['preflight']['pipeline_commit'],
                    'Registry did not accept these mechanical bytes')
            render = load(root, cycle['palomar_rendering']['validation_receipt'])
            require(render['status'] == 'pass' and render['source_commit'] == cycle['source_commit']
                    and render['comparator_config_path'] == bundle['configuration']
                    and render['selected_theorem_count'] == len(config['theorem_names'])
                    and render['all_selected_compiler_anchors_present'] is True, 'Wrong rendered scope')
            require(sha(local(root, render['report_path']).read_bytes()) == render['report_sha256']
                    and sha(local(root, render['artifact_path']).read_bytes()) == render['artifact_sha256'],
                    'Rendering artifact/report changed')
            validate_render_report(root, load(root, render['report_path']), render, cycle, bundle, config)
            require(entry['challenge_render']['artifact_tree_sha256'] == render['artifact_tree_sha256']
                    and entry['challenge_render']['renderer_commit'] == render['renderer_commit'],
                    'Registry rendering differs')
            pins = {(item['source_repository'].lower(), item['commit'])
                    for item in entry['preservation']['repositories']}
            dependencies = json.loads(committed(str(root), cycle['source_commit'], cycle['project_path']+'/lake-manifest.json'))
            expected_pins = {(REPOSITORY.lower(), cycle['source_commit'])}
            expected_pins.update((item['url'].removeprefix('https://github.com/').removesuffix('.git').lower(), item['rev'])
                                 for item in dependencies['packages'] if item['type'] == 'git')
            require(expected_pins <= pins, 'Missing source or dependency preservation pin')
            selected.extend(config['theorem_names'])
            mapped = {name for result in bundle['main_results'] for name in result['selected_declarations']}
            records.append({'slug': cycle['slug'], 'id': entry['id'], 'version': entry['version'], 'url': url,
                            'source_commit': cycle['source_commit'], 'public_entry_sha256': receipt['entry_sha256'],
                            'selected_declarations': config['theorem_names'],
                            'supplementary_selected_declarations': [name for name in config['theorem_names'] if name not in mapped],
                            'published_warning_count': len(entry['review']['warnings']),
                            'source_and_git_dependency_pins_checked': len(expected_pins)})
        for item in bundle['main_results']:
            rows.append({key: item[key] for key in ['number', 'label', 'title', 'statement_sha256',
                         'printed_conditional_clause', 'selected_declarations']} | {
                         'dossier': cycle['slug'], 'registered': registration is not None,
                         'registration_id': registration['id'] if registration else None,
                         'registry_url': registration['url'] if registration else None,
                         **({'selected_conjunction_clauses': item['selected_conjunction_clauses']}
                            if 'selected_conjunction_clauses' in item else {})})
    require(len(records) == state['registered_count'], 'Live registration count mismatch')
    if require_all:
        require(len(records) == len(plan['submission_sequence']) and all(item['registered'] for item in rows),
                'The planned public registrations are not complete')
    companion_rows = []
    for cycle in state['cycles']:
        for item in bundles[cycle['slug']].get('companion_results', []):
            original = next(r for r in index['results'] if r['label'] == item['label'])
            require(original['document'] == 'companion' and item['number'] == original['number']
                    and item['statement_sha256'] == original['source']['statement_sha256']
                    and item['source'] == original['source']['path'], 'Companion scope differs')
            require(set(item['selected_declarations']) <= set(bundles[cycle['slug']]['selected_declarations']),
                    'Companion endpoint is not selected')
            companion_rows.append({'number': item['number'], 'label': item['label'],
                'selected_declarations': item['selected_declarations'],
                'registered': cycle.get('registration') is not None,
                'additional_displayed_corollary': item.get('additional_displayed_corollary')})
    return {'schema_version': 1, 'status': 'verified_archived_public_records',
            'checked_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'repository': REPOSITORY, 'publication_plan': active_plan, 'publication_index': plan['source_index'],
            'allocation_source_commit': baseline, 'publication_plan_sha256': sha(local(root, active_plan).read_bytes()),
            'publication_index_sha256': sha(local(root, plan['source_index']).read_bytes()),
            'cycle_state_sha256': sha(local(root, STATE).read_bytes()), 'registered_dossiers': len(records),
            'registered_main_results': sum(item['registered'] for item in rows), 'total_main_results': 26,
            'registered_selected_declarations': len(selected), 'total_selected_declarations': plan['selected_theorem_count'],
            'planned_registrations': len(plan['submission_sequence']),
            'records': records, 'main_results': rows, 'direct_companion_results': companion_rows,
            'scope': 'Offline integrity and correspondence audit of archived public entries, official reports, rendering receipts and preservation pins. It does not rerun Lean or revalidate private review-consent bytes. Printed conditional premises remain explicit; the 92 companion results are not all selected separately.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--require-all', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = inspect(require_all=args.require_all)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({key: result[key] for key in ['status', 'registered_dossiers',
                     'registered_main_results', 'registered_selected_declarations']}))
