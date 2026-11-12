#!/usr/bin/env python3
"""Read-only source/type/receipt checks for the publication dossier; no submission."""
from pathlib import Path
from collections import Counter
import argparse,gzip,hashlib,json,re,zipfile
import yaml
from check_manuscript_v20 import statements
from build_publication import bibliography_inventory

ROOT=Path(__file__).resolve().parents[1]
PACKAGE='manuscripts/paper-p1/publication-2026-11-12'
EVIDENCE='docs/validation/publication-2026-11-12'
INDEX='docs/manuscript-results-publication-2026-11-12.json'
ARCHIVE='eb1535b8d0a048fa2b567e2a67e92555c7e20e5cf7fb5736217319216b5ef067'
PIPELINE='14aa8d6b3c2f14a8540605e37144560b9a00e7e7'
PERSON={'name':'Brice Pouly','github':'Vulkin-prog','orcid':'0009-0008-8491-2467'}

def require(value,message):
    if not value:raise ValueError(message)
def read(path):return json.loads(path.read_text())
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def check_partition(index,old):
    rows=index['results'];before={r['label']:r for r in old['results']}
    require(len(rows)==118 and len({r['label'] for r in rows})==118,'Expected118 distinct results')
    require(Counter(r['document'] for r in rows)=={'main':26,'companion':92},'Publication must retain26+92')
    require({r['label'] for r in rows}==set(before),'Current result identities differ')
    changed=[]
    for row in rows:
        prior=before[row['label']]
        require(row['number']==prior['number'] and row['document']==prior['document'],'Result numbering/document changed')
        require(row['entry_points']==prior['entry_points'],'A proof clause endpoint was weakened or replaced')
        require(row['printed_conditional_clause']==prior['printed_conditional_clause'],'Printed conditional premise changed')
        same=row['source']['statement_sha256']==prior['source']['statement_sha256']
        expected='identical_statement' if same else 'clarified_original_contact_scope'
        require(row['comparison_to_v2']==expected,'Incorrect statement comparison disposition')
        if not same:changed.append(row['label'])
    require(changed==index['changed_statement_labels']==['p1:fixed:propagation'],'Only T4.3 is a changed statement block')
    require(all(r['comparison_to_v2']=='identical_statement' for r in rows if r['document']=='main'),'A main statement changed')
    require(index['counts']=={'main':26,'companion':92,'total':118,'identical_statement_blocks':117,'clarified_statement_blocks':1,'main_statement_blocks_unchanged':26,'auxiliary_claims':9,'compiled_propositions':212},'Publication accounting differs')
    require(index['palomar_status']=='six_prepared_dossiers_on_hold_at_author_request','User submission hold changed')

def check_types(actual,old):
    require(len(actual)==212 and actual==old,'Existing compiled proposition types were altered')
    require(all(r['kind']=='theorem' and r['is_proposition'] for r in actual),'A signature or definition is being counted as proof')

def check_metadata(data,slug,snapshot=None):
    require(data['project']['authors']==[PERSON] and data['project']['responsible_maintainers']==[PERSON],'Author or responsible-maintainer ORCID differs')
    source=data['sources'][0]
    require(source['authors']==[PERSON] and source['relationship']=='formalizes','Source author/provenance differs')
    require(source['id'].endswith('/manuscripts/paper-p1/publication-2026-11-12'),'Metadata cite the wrong edition')
    if snapshot:require('/tree/'+snapshot+'/' in source['id'],'Publication source metadata are not frozen')

def check_caller(workflow,plan):
    require(set(workflow['on'])=={'workflow_dispatch'},'Publication preflight must remain manual')
    inputs=workflow['on']['workflow_dispatch']['inputs']
    require(inputs['bundle']['options']==plan['submission_sequence'] and len(inputs['bundle']['options'])==6,'A seventh or incorrect candidate was exposed')
    require(inputs['authorization_relationship']['required']=='true' and inputs['source_commit']['required']=='true','Explicit source and personal declaration must be required')
    require(workflow['concurrency']['group']=='p1-palomar-registration','Submission preflights must share serialization')
    job=workflow['jobs']['verify']
    require(job['uses'].endswith('@'+PIPELINE) and job['with']['pipeline_commit']==PIPELINE,'Official workflow pins differ')
    require(job['with']['mode']=='full' and job['with']['execution_profile']=='palomar-standard-v1','Incomplete official preflight profile')

def check_stage(alignment):
    require(alignment['author_submission_hold'] is True and alignment['official_full_preflight_passed'] is False and alignment['intake_started'] is False and alignment['registration'] is None,'Preparation must not claim an official cycle')
    require(alignment['maximum_registrations']==6 and alignment['selected_theorems']==52 and alignment['main_statement_blocks_identical']==26,'Palomar coverage accounting differs')
    require(alignment['new_kernel_suite_performed'] is False,'Old checker receipts must not be relabelled as new runs')

def verify(allow_unfrozen=False):
    root=ROOT;p=root/PACKAGE;e=root/EVIDENCE
    index=read(root/INDEX);old=read(root/'docs/manuscript-results-v2.0.json');check_partition(index,old)
    provenance=read(p/'RECEIVED_PROVENANCE.json');archive=p/provenance['archive']['path']
    require(sha(archive)==provenance['archive']['sha256']==index['received_archive_sha256']==ARCHIVE,'Received ZIP differs')
    with zipfile.ZipFile(archive) as z:
        require(z.testzip() is None and len(z.infolist())==41,'Received archive integrity failed')
        expected={name:hashlib.sha256(z.read(name)).hexdigest() for name in z.namelist()}
    actual={x.relative_to(p/'received').as_posix():sha(x) for x in (p/'received').rglob('*') if x.is_file()}
    require(actual==expected==provenance['received_files_sha256'],'Received files changed')
    source_files={x.relative_to(p/'sources').as_posix() for x in (p/'sources').rglob('*.tex')}
    require(len(source_files)==34,'Unexpected active TeX inventory')
    changed={name for name in source_files if (p/'sources'/name).read_bytes()!=(p/'received/sources'/name).read_bytes()}
    require(changed=={'formalization.tex'},'Scientific publication sources changed after receipt')
    actual_rows=statements(PACKAGE+'/sources')
    require(set(actual_rows)=={r['label'] for r in index['results']},'Publication source/index identities differ')
    for row in index['results']:require(row['source']==actual_rows[row['label']],'A statement source/hash/locator differs')
    current_types=read(e/'lean-scope/compiled-types.json');prior_types=read(root/'docs/validation/v2.0/v2-scope/compiled-types.json');check_types(current_types,prior_types)
    require(sha(e/'lean-scope/compiled-types.json')==index['compiled_scope']['sha256'],'Compiled-scope hash differs')
    proof=read(e/'lean-validation.json');require(proof['status']=='passed' and all(v==0 for v in proof['actual_process_exit_codes'].values()),'Actual Lean replay did not pass')
    require(proof['compiled_scope_types']==212 and proof['audited_theorems']==20019 and proof['new_lean_theorems']==0,'Proof replay accounting differs')
    for row in proof['logs']:require(sha(root/row['path'])==row['sha256_gzip'],'Proof log bytes differ')
    for name,digest in read(e/'preserved-baseline-files.json').items():require(sha(root/name)==digest,'Protected mathematical/historical source changed: '+name)
    require(len(index['auxiliary_claims'])==9,'Auxiliary claim inventory differs')
    for row in index['auxiliary_claims']:
        s=row['source'];text=(root/s['path']).read_text()
        require(hashlib.sha256(text.encode()).hexdigest()==s['file_sha256'] and text[:text.index(s['anchor'])].count('\n')+1==s['line'],'Auxiliary anchor differs')
    build=read(e/'pdf/build-validation.json');require(build['status']=='passed' and build['cross_references_stable'] is True and not build['unresolved_or_overfull_diagnostics'],'Publication PDF build failed')
    require(4<=len(build['commands'])<=12 and len(build['commands'])%2==0 and all(c['actual_exit_code']==0 for c in build['commands']),'Actual TeX processes did not pass')
    for command in build['commands']:
        logfile=(e/'pdf'/command['log']).resolve()
        require(logfile.is_relative_to((e/'pdf').resolve()) and sha(logfile)==command['log_sha256'],'Actual TeX process log differs')
    for row in build['source_files']:require(sha(p/'sources'/row['path'])==row['sha256'],'Built source differs')
    for row in build['pdfs']:require(sha(p/'pdf'/row['filename'])==row['sha256'],'Built PDF differs')
    for doc in ['main','companion']:
        labels={lab:(number,page) for lab,number,page in re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]*)\}\{([^}]*)\}',(e/'pdf'/f'{doc}.aux').read_text())}
        for row in index['results']:
            if row['document']==doc:require(labels[row['label']]==(row['number'],row['page']),'Compiled result number/page differs')
    bibliography=bibliography_inventory(p/'sources');require({k:len(v) for k,v in bibliography.items()}=={'main':18,'companion':16},'Local bibliography counts differ')
    snapshot_path=e/'documentary-snapshot.json';snapshot=None
    if snapshot_path.exists():
        record=read(snapshot_path);snapshot=record['commit'];require(re.fullmatch('[0-9a-f]{40}',snapshot) and record['path']==INDEX and record['sha256']==sha(root/INDEX),'Frozen statement-index binding differs')
    else:require(allow_unfrozen,'Publication statement index must be frozen before delivery')
    notice=(p/'sources/formalization.tex').read_text()
    target='https://github.com/Vulkin-prog/paper-p1-lean/blob/'+(snapshot or 'main')+'/'+INDEX
    require(target in notice,'Notice does not link this edition-specific frozen index')
    require("At the author's request" in notice and 'remain in preparation' in notice and 'no official submission or registration' in notice,'Actual submission hold must be explicit')
    plan=read(root/'palomar/REGISTRATION_PLAN_PUBLICATION.json');legacy=read(root/'palomar/REGISTRATION_PLAN_V2.json')
    require(len(plan['bundles'])==plan['maximum_registrations']==6 and plan['selected_theorem_count']==52,'Exactly six retained configurations and52 selections are required')
    require(plan['submission_sequence']==legacy['submission_sequence'],'Submission priority changed')
    numbers=[]
    for b,old_b in zip(plan['bundles'],legacy['bundles']):
        require(all(b[k]==old_b[k] for k in ['slug','configuration','challenge','solution','selected_declarations']),'A different project/configuration or theorem identity was introduced')
        require(b['metadata']=='palomar/publication/'+b['slug']+'/formalization.yaml','Unexpected current metadata path')
        for row in b['main_results']:
            current=next(r for r in index['results'] if r['label']==row['label']);numbers.append(row['number'])
            require(row['source']==current['source']['path'] and row['statement_sha256']==current['source']['statement_sha256'] and row['number']==current['number'],'Publication allocation/source binding differs')
        check_metadata(yaml.safe_load((root/b['metadata']).read_text()),b['slug'],snapshot)
    require(len(numbers)==len(set(numbers))==26,'Main results must each be allocated once')
    metadata=read(e/'publication-metadata-validation.json');require(len(metadata['rows'])==6 and metadata['full_palomar_workflow_passed'] is False,'Local metadata checks are not official preflight')
    for row in metadata['rows']:require(row['official_parser_passed'] and sha(root/row['metadata'])==row['sha256'] and row['declared_orcids']==[PERSON['orcid']],'Metadata parse/source/ORCID binding differs')
    alignment=read(root/'palomar/publication/ALIGNMENT.json');check_stage(alignment)
    frozen=alignment['legacy_frozen_validation'];require(sha(root/frozen['path'])==frozen['sha256'],'Frozen checker qualification was altered')
    for b in alignment['bundles']:
        for path,digest in b['unchanged_checked_math_files'].items():require(sha(root/path)==digest,'Previously checked mathematical payload changed')
    caller=root/'.github/workflows/palomar-publication-preflight.yml';workflow=yaml.load(caller.read_text(),Loader=yaml.BaseLoader);check_caller(workflow,plan)
    require("'palomar/publication/'" in caller.read_text() and 'request_id=pb' in caller.read_text(),'Publication caller uses the wrong metadata or request identity')
    if not allow_unfrozen:
        visual=read(e/'pdf/visual-review.json');require(visual['status']=='passed' and visual['all_pages_inspected_in_contact_sheets'] is True,'Visual review incomplete')
        require(visual['pages']=={r['document']:r['pages'] for r in build['pdfs']},'Visual PDF page count differs')
        for row in visual['pdfs']:require(row in build['pdfs'],'Visual review concerns another PDF')
        for row in visual['images']:require(sha(root/row['path'])==row['sha256'],'Visual evidence differs')
    return {'results':118,'main_results_unchanged':26,'clarified_statements':1,'compiled_propositions':212,'palomar_configurations':6,'selected_theorems':52,'submission_hold':True,'draft_index_link_allowed':allow_unfrozen}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--allow-unfrozen-index-link',action='store_true');args=parser.parse_args()
    print(json.dumps(verify(args.allow_unfrozen_index_link),sort_keys=True))
