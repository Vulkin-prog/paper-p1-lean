#!/usr/bin/env python3
"""Check the bounded disclosure update without relabelling frozen receipts."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import yaml

ROOT=Path(__file__).resolve().parents[1]
PERSON={'name':'Brice Pouly','github':'Vulkin-prog','orcid':'0009-0008-8491-2467'}
ASSISTANCE_COMMIT='e564207ab543c7c0967e34b52f3d456d7a8f302c'
ASSISTANCE_PATH='manuscripts/paper-p1/publication-2026-11-12/sources/assistance.tex'
ASSISTANCE_URL='https://github.com/Vulkin-prog/paper-p1-lean/blob/'+ASSISTANCE_COMMIT+'/'+ASSISTANCE_PATH

def require(condition,message):
    if not condition:raise ValueError(message)

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def check_plan(plan,old):
    expected=old['submission_sequence'][1:]
    require(old['submission_sequence'][0]=='quadratic_limits','Wrong first dossier')
    require(plan['maximum_registrations']==6 and plan['new_registration_identities']==0,'Extra registration identity')
    require(plan['remaining_sequence']==expected,'Remaining cycle order differs')
    rows=plan['remaining_bundles'];require([r['slug'] for r in rows]==expected and len(rows)==5,'Wrong remaining dossiers')
    by_slug={b['slug']:b for b in old['bundles']}
    for row in rows:
        before=by_slug[row['slug']]
        require(row['configuration']==before['configuration'] and row['project_path']=='RegistryV2','Comparator identity changed')
        require(row['selected_declarations']==before['selected_declarations'] and row['main_results']==before['main_results'],'Scientific scope changed')
        require(row['baseline_metadata']==before['metadata'],'Wrong baseline metadata')
        require(row['metadata']=='palomar/publication-followup/'+row['slug']+'/formalization.yaml','Unexpected metadata path')
    require(sum(len(r['selected_declarations']) for r in rows)==plan['remaining_selected_theorem_count']==42,'Wrong selection count')
    require(sum(len(r['main_results']) for r in rows)==21,'Wrong remaining main-result count')

def check_metadata_patch(data,baseline,plan):
    method=plan['added_automation_method']
    require(method['method']=='other' and method['framework']=='ChatGPT' and method['models']==['GPT-6 Astra'],'Incorrect assistance identification')
    require(ASSISTANCE_URL in method['prompting_notes'] and 'mathematical arguments' in method['tool_setup'],'Missing pinned mathematical-assistance disclosure')
    expected=deepcopy(baseline)
    require(plan['old_review_note_sentence'] in expected['review']['notes'],'Baseline review notes differ')
    expected['automation']['methods'].append(deepcopy(method))
    expected['review']['notes']=expected['review']['notes'].replace(plan['old_review_note_sentence'],plan['replacement_review_note_sentence'])
    require(data==expected,'Unrelated metadata changed or assistance method missing')
    require(data['project']['authors']==[PERSON] and data['project']['responsible_maintainers']==[PERSON] and data['sources'][0]['authors']==[PERSON],'Human author or ORCID changed')

def validate(root=ROOT):
    root=Path(root);plan=json.loads((root/'palomar/PUBLICATION_FOLLOWUP_METADATA.json').read_text());old=json.loads((root/'palomar/REGISTRATION_PLAN_PUBLICATION.json').read_text())
    check_plan(plan,old)
    assistance=plan['assistance_statement']
    require(assistance['commit']==ASSISTANCE_COMMIT and assistance['path']==ASSISTANCE_PATH and assistance['url']==ASSISTANCE_URL and sha(root/ASSISTANCE_PATH)==assistance['sha256'],'Assistance statement binding differs')
    require(plan['official_full_preflight_passed'] is False and plan['intake_started'] is False,'Preparation relabelled as an actual filing')
    actual={str(p.relative_to(root)) for p in (root/'palomar/publication-followup').glob('*/formalization.yaml')}
    require(actual=={r['metadata'] for r in plan['remaining_bundles']},'Extra or missing candidate metadata')
    for row in plan['remaining_bundles']:
        original=root/row['baseline_metadata'];updated=root/row['metadata']
        require(sha(original)==row['baseline_metadata_sha256'] and sha(updated)==row['metadata_sha256'],'Metadata byte binding differs')
        check_metadata_patch(yaml.safe_load(updated.read_text()),yaml.safe_load(original.read_text()),plan)
    workflow=yaml.load((root/'.github/workflows/palomar-publication-preflight.yml').read_text(),Loader=yaml.BaseLoader)
    edition=workflow['on']['workflow_dispatch']['inputs']['metadata_edition']
    require(edition['options']==['publication','followup'] and edition['default']=='publication','Wrong metadata-edition selection')
    require(workflow['concurrency']['group']=='p1-palomar-registration','Serialization changed')
    require('palomar/publication-followup/' in workflow['jobs']['select']['steps'][0]['run'],'Caller omits follow-up metadata')
    return {'metadata_files':5,'remaining_selected_theorems':42,'remaining_main_results':21,'maximum_registrations':6,'author_orcid_preserved':True,'frozen_metadata_preserved':True,'official_full_preflight_passed':False}

if __name__=='__main__':
    subprocess.run([sys.executable,str(ROOT/'scripts/check_publication.py')],cwd=ROOT,check=True,capture_output=True,text=True)
    print(json.dumps(validate(),sort_keys=True))
