#!/usr/bin/env python3
"""Check the current six main-article dossiers, without reinterpreting old evidence."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys
import yaml
from update_audit import lean_code
ROOT=Path(__file__).resolve().parents[1]
GROUPS={
 'affine_events':{'2.1','2.2','2.3','2.4','2.5'},
 'stopping_reconstruction':{'4.1','4.2','5.1','5.2','5.3'},
 'pairs_channels':{'3.1','3.2','8.1','8.2','8.3'},
 'cumulants_optimality':{'3.3','3.4','6.1','6.2'},
 'quadratic_limits':{'1.1','1.2','7.2','7.3','7.4'},
 'probability_references':{'7.1','8.4'}}
COUNTS=dict(zip(GROUPS,[8,8,13,8,10,5]))
PERSON={'name':'Brice Pouly','github':'Vulkin-prog','orcid':'0009-0008-8491-2467'}
ALLOWED={'propext','Classical.choice','Quot.sound'}

def require(value,message):
 if not value:raise ValueError(message)

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path):return json.loads(path.read_text())

def audit_source(plan,root=ROOT):
 names=[];imports=[]
 for b in plan['bundles']:
  module=Path(b['solution']).stem;imports.append(module)
  names.extend(b['namespace']+'.'+n for n in re.findall(r'^(?:theorem|lemma) ([^\s({:\[]+)',lean_code((root/b['solution']).read_text()),re.M))
 text='module\n\n'+''.join('import '+i+'\n' for i in imports)+'\n'+''.join('#print axioms '+n+'\n' for n in names)
 return names,text

def check(root=ROOT,require_evidence=True):
 root=Path(root);plan=read(root/'palomar/REGISTRATION_PLAN_V2.json')
 require(plan['maximum_registrations']==6 and len(plan['bundles'])==6,'Exactly six replacement dossiers are required')
 require([b['slug'] for b in plan['bundles']]==list(GROUPS),'V2 dossier order/identity differs')
 require(plan['project_path']=='RegistryV2','Unexpected selected project')
 require(len(plan['submission_sequence'])==len(set(plan['submission_sequence']))==6 and set(plan['submission_sequence'])==set(GROUPS),'Submission priority must contain exactly the six dossiers')
 index=read(root/'docs/manuscript-results-v2.0.json');main={r['number']:r for r in index['results'] if r['document']=='main'}
 require(len(main)==26,'Current article must have26 numbered results')
 expected_sources={b[k] for b in plan['bundles'] for k in ['challenge','solution']}|{'RegistryV2/AuditRegistryV2.lean'}
 actual_sources={p.relative_to(root).as_posix() for p in (root/'RegistryV2').rglob('*.lean') if '.lake' not in p.relative_to(root/'RegistryV2').parts}
 require(actual_sources==expected_sources,'An unexpected or unaudited Lean source exists in the contained project')
 allnumbers=[];selected=[]
 for b in plan['bundles']:
  slug=b['slug'];cfg=read(root/b['configuration']);names=cfg['theorem_names']
  require(b['configuration']=='RegistryV2/comparator/p1_'+slug+'.json' and b['metadata']=='palomar/v3/'+slug+'/formalization.yaml','Unexpected submitted paths')
  proved=[b['namespace']+'.'+n for n in re.findall(r'^(?:theorem|lemma) ([^\s({:\[]+)',lean_code((root/b['solution']).read_text()),re.M)]
  require(b['audited_solution_theorems']==proved,'Per-dossier proof inventory differs')
  require(len(names)==COUNTS[slug] and len(set(names))==len(names),'Selection count/duplicates: '+slug)
  require(names==b['selected_declarations'],'Configuration and plan selection differ: '+slug)
  require(set(cfg['permitted_axioms'])==ALLOWED and cfg['enable_nanoda'] is True,'Unexpected trust configuration')
  require(set(r['number'] for r in b['main_results'])==GROUPS[slug],'Main-result allocation differs: '+slug)
  for row in b['main_results']:
   num=row['number'];original=main[num];allnumbers.append(num)
   require(row['label']==original['label'] and row['statement_sha256']==original['source']['statement_sha256'],'V2 source statement differs: '+num)
   require(row['source']==original['source']['path'] and row['parent_proof_endpoints']==original['entry_points'],'Substantive proof-origin map differs: '+num)
   require(bool(row['selected_declarations']) and set(row['selected_declarations'])<=set(names),'Missing direct clause selection: '+num)
   require(row['printed_conditional_clause']==original['printed_conditional_clause'],'Conditional-source status differs: '+num)
  for kind in ['challenge','solution']:
   p=root/b[kind];text=p.read_text();code=lean_code(text)
   require(p.is_file() and not p.is_symlink(),'Non-regular submitted source')
   require(code.lstrip().startswith('module\n'),'Missing module header: '+p.name)
   require(Path(b[kind]).stem==cfg[kind+'_module'],'Module/source mismatch')
   require(len(text.splitlines())<=10000,'Oversized Lean file')
   require('import Challenge' not in code,'A proof must not import a Challenge')
   if kind=='challenge':
    require(len(text.splitlines())<=1000 and len(text.encode())<=100*1024,'Oversized Challenge')
    imports=re.findall(r'^(?:public )?import (\S+)',code,re.M)
    require(imports and all(m.startswith('Mathlib.') for m in imports),'Challenge must import only canonical Mathlib')
    require(not re.search(r'\bPaperP1\.',code),'Project object leaked into Challenge')
    require(len(re.findall(r'\bsorry\b',code))==len(names),'Challenge hole count differs')
    declared=[b['namespace']+'.'+n for n in re.findall(r'^(?:theorem|lemma) ([^\s({:\[]+)',code,re.M)]
    require(set(declared)==set(names),'Challenge theorem selection differs')
   else:require(not re.search(r'\b(?:sorry|admit|sorryAx|axiom|unsafe)\b',code),'Unproved/unsafe substantive source')
  require(b['challenge_lines']==len((root/b['challenge']).read_text().splitlines()) and b['challenge_bytes']==(root/b['challenge']).stat().st_size,'Challenge size inventory is stale')
  metadata=yaml.safe_load((root/b['metadata']).read_text())
  require(metadata['version']=='v0.4','Metadata version differs')
  require(metadata['project']['authors']==[PERSON] and metadata['project']['responsible_maintainers']==[PERSON],'Author name/ORCID metadata differs')
  require(metadata['sources'][0]['authors']==[PERSON] and metadata['sources'][0]['relationship']=='formalizes','Source authorship/provenance differs')
  require('V2.0' in metadata['sources'][0]['title'],'Metadata must name the current edition')
  selected.extend(names)
 require(len(allnumbers)==len(set(allnumbers))==26 and set(allnumbers)==set(main),'Coverage must be exactly26/26, each allocated once')
 require(len(selected)==len(set(selected))==plan['selected_theorem_count']==52,'Expected52 distinct compared statements')
 toolchain=(root/'RegistryV2/lean-toolchain').read_text();require(toolchain==(root/'lean-toolchain').read_text() and 'v4.36.0-rc2' in toolchain,'Compiler pins differ')
 manifest=read(root/'RegistryV2/lake-manifest.json');parent=read(root/'lake-manifest.json')
 require([p for p in manifest['packages'] if p['type']=='path']==[{'type':'path','scope':'','name':'paper_p1_lean','manifestFile':'lake-manifest.json','inherited':False,'dir':'..','copy':False,'configFile':'lakefile.toml'}],'Parent must be the contained substantive path dependency')
 require({p['name']:p['rev'] for p in manifest['packages'] if p['type']=='git'}=={p['name']:p['rev'] for p in parent['packages'] if p['type']=='git'},'Dependency pins differ')
 workflow=yaml.load((root/'.github/workflows/palomar-preflight.yml').read_text(),Loader=yaml.BaseLoader)
 require(set(workflow['on'])=={'workflow_dispatch'},'Palomar preflight must be explicitly manual')
 require(workflow['on']['workflow_dispatch']['inputs']['bundle']['options']==plan['submission_sequence'],'Active workflow must expose only the six V2 choices')
 verify=workflow['jobs']['verify'];pin='14aa8d6b3c2f14a8540605e37144560b9a00e7e7'
 require(verify['uses'].endswith('@'+pin) and verify['with']['pipeline_commit']==pin,'Official workflow pins differ')
 require(verify['with']['mode']=='full' and verify['with']['execution_profile']=='palomar-standard-v1','Incomplete official preflight selector')
 require(workflow['concurrency']['group']=='p1-palomar-registration','Preflights must be serialized')
 names,text=audit_source(plan,root);require(len(names)==len(set(names))==262,'Audit must cover262 proved declarations')
 require(read(root/'RegistryV2/audit-declarations.json')==names and (root/'RegistryV2/AuditRegistryV2.lean').read_text()==text,'Nested axiom inventory differs')
 if require_evidence:
  evidence=root/'palomar/v3';validation=read(evidence/'VALIDATION.json');require(validation['status']=='local_checks_passed','Local qualification is incomplete')
  require(validation['official_full_preflight_passed'] is False and validation['intake_started'] is False and validation['registration'] is None,'Local evidence must not claim an official submission')
  require(validation['selected_theorems']==52 and validation['audited_theorems']==262 and validation['main_results']==26,'Evidence counts differ')
  for path,sha in validation['current_source_files'].items():require(digest(root/path)==sha,'Checked source changed: '+path)
  types=read(evidence/'compiled-types.json');require([r['name'] for r in types]==selected,'Compiled-type selections differ')
  require(all(r['kind']=='theorem' and r['is_proposition'] for r in types),'A compared statement is not a proved proposition')
  byname={r['name']:hashlib.sha256(r['type'].encode()).hexdigest() for r in types}
  require(all(b['compiled_type_sha256']=={n:byname[n] for n in b['selected_declarations']} for b in plan['bundles']),'Compiled type bindings differ from the clause allocation')
  require([b['slug'] for b in validation['kernel_checks']['bundles']]==list(GROUPS),'Checker dossier identities/order differ')
  for b in validation['kernel_checks']['bundles']:
   expected=next(row for row in plan['bundles'] if row['slug']==b['slug'])
   require(b['selected_declarations']==expected['selected_declarations'],'Checked declarations differ from the current selection')
   for key in ['challenge','solution','configuration','metadata']:
    path=expected[key];require(b['files'][path]==digest(root/path),'Compared source or configuration changed: '+path)
   require(b['actual_comparator_exit']==0 and set(b['kernels_accepted'])=={'Lean paranoid','con-leche','con-ron','lean4lean','nanoda','Lean default'},'Incomplete six-kernel acceptance')
  require(len(validation['kernel_checks']['bundles'])==6,'Missing checker dossier')
  for path,sha in validation['evidence_files'].items():require(digest(root/path)==sha,'Evidence bytes changed: '+path)
  # Selected source types retain the printed conditional premise explicitly.
  transfer=next(r for r in types if r['name'].endswith('.conditional_transfer'))
  require(any(b['name']=='hfixed' and 'FixedActivity' in b['type'] for b in transfer['binders']),'The254-order transfer premise is missing')
  nominal=next(r for r in types if r['name'].endswith('.nominal_quadratic_comparison'))
  require([b['name'] for b in nominal['binders']]==['C'],'The nominal comparison constant must be fixed before epsilon')
  require(all(r['type'] for r in types),'Empty compiled theorem type')
 return {'registrations':6,'main_results':26,'selected_theorems':52,'audited_theorems':262,'evidence_checked':require_evidence}

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--without-evidence',action='store_true');parser.add_argument('--audit-log',type=Path);args=parser.parse_args()
 try:
  result=check(require_evidence=not args.without_evidence)
  if args.audit_log:
   expected=read(ROOT/'RegistryV2/audit-declarations.json');text=args.audit_log.read_text()
   matches=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text)
   actual={n:{a.strip() for a in (xs or '').split(',') if a.strip()} for n,xs in matches}
   require(len(matches)==len(expected) and set(actual)==set(expected),'Actual axiom log selection differs')
   require(all(a<=ALLOWED for a in actual.values()),'Actual audit uses an unpermitted axiom')
   result['actual_axiom_log_checked']=len(actual)
  print(json.dumps(result,sort_keys=True))
 except (ValueError,KeyError,OSError) as e:raise SystemExit(str(e))
if __name__=='__main__':main()
