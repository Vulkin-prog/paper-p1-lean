#!/usr/bin/env python3
"""Check the merged final statement surface and preservation of four issued records."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import textwrap
import yaml
from update_audit import lean_code

ROOT=Path(__file__).resolve().parents[1]
ALLOWED={'propext','Quot.sound','Classical.choice'}
PLAN='palomar/REGISTRATION_PLAN_FINAL.json'

def require(value,message):
    if not value:raise ValueError(message)
def read(path):return json.loads(path.read_text())
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def normalized(text):return lean_code(text).split()

def declarations(text):
    namespace=None;names=[]
    for line in lean_code(text).splitlines():
        match=re.match(r'^namespace (\S+)',line)
        if match:namespace=match[1]
        if re.match(r'^end PaperP1Registry\.Final\.',line):namespace=None
        match=re.match(r'^(?:theorem|lemma) ([^\s({:\[]+)',line)
        if match:
            require(namespace is not None,'Theorem outside the audited namespaces')
            names.append(namespace+'.'+match[1])
    return names

def proposition(signature):
    for name in re.findall(r'[({\[]\s*(h\w*)\s*:',signature):
        if len(re.findall(r'(?<!\w)'+re.escape(name)+r'(?!\w)',signature))==1:
            signature=re.sub(r'(?<!\w)'+re.escape(name)+r'(?!\w)','_'+name,signature)
    depth=0
    for i,char in enumerate(signature):
        if char in '([{':depth+=1
        elif char in ')]}':depth-=1
        elif char==':' and depth==0:
            binders=signature[:i].strip()
            return '('+('∀ '+binders+',\n' if binders else '')+textwrap.indent(textwrap.dedent(signature[i+1:]).strip(),'    ')+')'
    raise ValueError('Missing type separator')

def signature(text,name):
    code=lean_code(text)
    start=re.search(r'^theorem '+re.escape(name)+r'\s*',code,re.M)
    require(start is not None,'Missing selected declaration: '+name)
    proof=re.search(r':=\s*by\b',code[start.end():])
    require(proof is not None,'Missing proof delimiter: '+name)
    return code[start.end():start.end()+proof.start()].strip()

def check(root=ROOT,audit_log=None):
    root=Path(root);project=root/'RegistryFinal'
    plan=read(root/PLAN);bundle=plan['bundles'][-1]
    require(plan['planned_registrations']==len(plan['bundles'])==5 and plan['maximum_registrations']==6,
            'Final allocation must preserve four records and one remainder')
    require(plan['selected_theorem_count']==42,'Final allocation must contain42 selected statements')
    frozen=read(root/plan['preservation_manifest'])
    for path,digest in frozen['immutable_public_files'].items():
        require(sha(root/path)==digest,'An immutable registered source/evidence file changed: '+path)
    state=read(root/'palomar/publication/CYCLE_STATE.json')
    require(state['cycles'][:4]==frozen['immutable_cycle_prefix'],'An issued cycle was changed')
    for cycle,b in zip(frozen['immutable_cycle_prefix'],plan['bundles'][:4]):
        require(b['slug']==cycle['slug'] and b['registered_source_commit']==cycle['source_commit']
                and b['registration']==cycle['registration'],'A published identity was remapped')
    cfg=read(root/bundle['configuration']);names=cfg['theorem_names']
    require(len(names)==len(set(names))==3 and names==bundle['selected_declarations'],
            'Exactly three final compound targets are required')
    require(set(cfg['permitted_axioms'])==ALLOWED and cfg['enable_nanoda'] is True,
            'Final trust configuration differs')
    files={p.name for p in project.rglob('*.lean') if '.lake' not in p.parts}
    require(files=={'ChallengeP1FinalFoundations.lean','SolutionP1FinalFoundations.lean','AuditRegistryFinal.lean'},
            'Unexpected or unaudited final Lean source')
    texts={kind:(root/bundle[kind]).read_text() for kind in ['challenge','solution']}
    for kind,text in texts.items():
        code=lean_code(text);path=root/bundle[kind]
        require(not path.is_symlink() and code.lstrip().startswith('module\n') and len(text.splitlines())<=10000,
                'Invalid source header, length or symlink')
        require('import Challenge' not in code,'Challenge imported as proof evidence')
        require(Path(bundle[kind]).stem==cfg[kind+'_module'],'Wrong source module')
        require(not re.search(r'\b(?:axiom|admit|unsafe|sorryAx)\b',code),'Untrusted final source')
    challenge=lean_code(texts['challenge']);solution=lean_code(texts['solution'])
    require(len(texts['challenge'].splitlines())<=1000 and len(texts['challenge'].encode())<=100*1024,
            'Oversized final Challenge')
    imports=re.findall(r'^(?:public )?import (\S+)',challenge,re.M)
    require(imports and all(n.startswith('Mathlib.') for n in imports) and not re.search(r'\bPaperP1\.',challenge),
            'Noncanonical Challenge dependency')
    require(declarations(challenge)==names and len(re.findall(r'\bsorry\b',challenge))==3,
            'Final Challenge holes/selected declarations differ')
    require(not re.search(r'\bsorry\b',solution),'Unproved Solution')
    prefixes=[]
    for code in [challenge,solution]:
        before=code[:re.search(r'^(?:theorem|lemma) ',code,re.M).start()]
        before=re.sub(r'^(?:public )?import \S+\n','',before,flags=re.M)
        prefixes.append(before.split())
    require(prefixes[0]==prefixes[1],'Models differ or a model follows proof elaboration')
    audited=declarations(solution)
    require(len(audited)==len(set(audited))==111 and audited==read(project/'audit-declarations.json')
            ==bundle['audited_solution_theorems'],'Incomplete final theorem inventory')
    expected='module\n\nimport SolutionP1FinalFoundations\n\n'+''.join('#print axioms '+n+'\n' for n in audited)
    require((project/'AuditRegistryFinal.lean').read_text()==expected,'Final axiom inventory is stale')
    mapping=read(project/'clause-map.json');clauses=mapping['inherited_clauses']
    require(len(clauses)==13,'A main-result clause was lost')
    for row in clauses:
        old=root/row['inherited_challenge']
        require(sha(old)==row['inherited_challenge_sha256'],'Inherited Challenge changed')
        typ=proposition(signature(old.read_text(),row['inherited_declaration'].rsplit('.',1)[1]))
        old_ns=row['inherited_declaration'].rsplit('.',1)[0]
        typ=typ.replace(old_ns,row['selected_declaration'].rsplit('.',1)[0])
        require(normalized(typ)==normalized(row['literal_clause_type']),'An inherited hypothesis or quantifier was changed')
    for name in names[:2]:
        fields=[r for r in clauses if r['selected_declaration']==name]
        require([r['conjunction_clause'] for r in fields]==list(range(1,len(fields)+1)),
                'Noncontiguous conjunction clause map')
        expected='\n  ∧ '.join(r['literal_clause_type'] for r in fields)
        extra=mapping['additional_companion_result']
        if name in extra['selected_declarations']:
            require(extra['number']=='T13.1' and extra['label']=='p1:uniform:full-support'
                    and extra['conjunction_clauses']==[9] and sha(root/extra['source'])==extra['source_file_sha256'],
                    'Uniform full-support source or clause differs')
            endpoint=extra['parent_proof_endpoints'][0]
            source=root/endpoint['source']
            require(sha(source)==endpoint['source_sha256'],'Substantive uniform-count proof changed')
            inherited=proposition(signature(source.read_text(),endpoint['name'].rsplit('.',1)[1]))
            inherited=inherited.replace('manuscriptLists','fullSupportLists').replace('dyadicBlock N','Ico N (2*N)')
            compact=lambda text:re.sub(r'\s+','',lean_code(text))
            require(compact(inherited)==compact(extra['literal_clause_type']),
                    'Uniform count hypothesis or quantifier changed')
            expected+='\n  ∧ '+extra['literal_clause_type']
        require(normalized(signature(texts['challenge'],name.rsplit('.',1)[1]).removeprefix(':').strip())==normalized(expected),
                'The selected bundle no longer contains every inherited clause')
    for name in names:
        require(normalized(signature(texts['challenge'],name.rsplit('.',1)[1]))
                ==normalized(signature(texts['solution'],name.rsplit('.',1)[1])),
                'Literal Challenge/Solution type differs')
    comp=mapping['companion_result']
    require(comp['number']=='T15.1' and comp['label']=='p1:obstruction:fixed'
            and sha(root/comp['source'])==comp['source_file_sha256'],'Companion source differs')
    require({r['number'] for r in bundle['main_results']}=={'2.1','2.2','2.3','2.4','2.5','7.1','8.4'},
            'Missing remaining main result')
    require((project/'lean-toolchain').read_bytes()==(root/'lean-toolchain').read_bytes(), 'Compiler pins differ')
    manifest=read(project/'lake-manifest.json');parent=read(root/'lake-manifest.json')
    require({p['name']:p['rev'] for p in manifest['packages'] if p['type']=='git'}
            =={p['name']:p['rev'] for p in parent['packages'] if p['type']=='git'}, 'Dependency pins differ')
    paths=[p for p in manifest['packages'] if p['type']=='path']
    require(len(paths)==1 and paths[0]['name']=='paper_p1_lean' and paths[0]['dir']=='..','Wrong substantive parent dependency')
    metadata=yaml.safe_load((root/bundle['metadata']).read_text())
    person={'name':'Brice Pouly','github':'Vulkin-prog','orcid':'0009-0008-8491-2467'}
    require(metadata['project']['authors']==metadata['project']['responsible_maintainers']
            ==metadata['sources'][0]['authors']==[person],'Name or ORCID differs')
    require({m['framework'] for m in metadata['automation']['methods']}=={'Codex','ChatGPT'},'Incomplete assistance disclosure')
    workflow=yaml.load((root/'.github/workflows/palomar-final-preflight.yml').read_text(),Loader=yaml.BaseLoader)
    require(set(workflow['on'])=={'workflow_dispatch'} and workflow['concurrency']['group']=='p1-palomar-registration',
            'The final official workflow must be manual and serialized')
    verifier=workflow['jobs']['verify'];pin='14aa8d6b3c2f14a8540605e37144560b9a00e7e7'
    require(verifier['uses'].endswith('@'+pin) and verifier['with']['pipeline_commit']==pin
            and verifier['with']['mode']=='full' and verifier['with']['execution_profile']=='palomar-standard-v1',
            'The final official preflight pin or full execution profile differs')
    qualification=read(root/'palomar/final/qualification/VALIDATION.json')
    require(qualification['status']=='local_checks_passed'
            and qualification['parent_audited_declarations']==20019
            and qualification['final_audited_declarations']==111
            and qualification['final_selected_statements']==3,
            'Final local qualification counts or status differ')
    for path,digest in qualification['source_files'].items():
        require(sha(root/path)==digest,'Locally compared final source changed: '+path)
    for path,digest in qualification['evidence_files'].items():
        require(sha(root/path)==digest,'Local qualification evidence changed: '+path)
    kernels=qualification['kernel_checks']
    expected_kernels={'Lean paranoid','con-leche','con-ron','lean4lean','nanoda','Lean default'}
    require(kernels['actual_comparator_exit']==0 and set(kernels['kernels_accepted'])==expected_kernels
            and kernels['selected_declarations']==names and kernels['bubblewrap_enabled'] is True,
            'Incomplete isolated six-kernel comparison')
    log=root/'palomar/final/qualification/six-kernels.log'
    require(sha(log)==kernels['log_sha256'] and 'Your solution is okay!' in log.read_text()
            and all(n+' kernel accepts the solution' in log.read_text() for n in expected_kernels),
            'The actual kernel acceptance log differs')
    parser=read(root/qualification['metadata_parser_validation'])
    require(parser['status']=='pass' and parser['metadata_sha256']==sha(root/bundle['metadata'])
            and parser['pipeline_commit']==pin and parser['all_three_person_roles_verified'] is True,
            'Final metadata parser evidence differs')
    if audit_log:
        matches=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",Path(audit_log).read_text())
        actual={n:{a.strip() for a in (xs or '').split(',') if a.strip()} for n,xs in matches}
        require(set(actual)==set(audited) and all(a<=ALLOWED for a in actual.values()),'Actual final axiom audit failed')
    return {'status':'pass','unchanged_public_files':len(frozen['immutable_public_files']),
            'preserved_registrations':4,'planned_total':5,'final_selected_targets':3,
            'inherited_main_clauses':13,'direct_companion_results':2,
            'audited_final_theorems':111,'local_kernel_evidence_checked':True,
            'actual_axiom_log_checked':bool(audit_log)}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--audit-log',type=Path)
    args=parser.parse_args()
    print(json.dumps(check(audit_log=args.audit_log)))
