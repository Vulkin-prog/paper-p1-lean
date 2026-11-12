"""Negative controls for six-dossier coverage, identity and proof evidence."""
from pathlib import Path
import hashlib,json,shutil,sys,tempfile,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import check_registry_v2 as guard

class RegistryV2Controls(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory(prefix='p1-registry-v2-');self.root=Path(self.temp.name)
  paths=[*ROOT.glob('RegistryV2/*.lean'),*ROOT.glob('RegistryV2/*.json'),*ROOT.glob('RegistryV2/comparator/*.json'),
   ROOT/'RegistryV2/lean-toolchain',ROOT/'RegistryV2/lakefile.toml',ROOT/'lean-toolchain',ROOT/'lake-manifest.json',
   ROOT/'.github/workflows/palomar-preflight.yml',ROOT/'docs/manuscript-results-v2.0.json',ROOT/'palomar/REGISTRATION_PLAN_V2.json',
   *ROOT.glob('palomar/v3/*/formalization.yaml'),*ROOT.glob('palomar/v3/*.json'),*ROOT.glob('palomar/v3/evidence/*')]
  evidence=ROOT/'palomar/v3/VALIDATION.json'
  if evidence.is_file():
   binding=json.loads(evidence.read_text())
   paths.extend(ROOT/path for path in [*binding['current_source_files'],*binding['evidence_files']])
  for path in paths:
   if path.is_file():
    target=self.root/path.relative_to(ROOT);target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(path,target)
 def tearDown(self):self.temp.cleanup()
 def mutate_json(self,path,change):
  p=self.root/path;x=json.loads(p.read_text());change(x);p.write_text(json.dumps(x,indent=2)+'\n')
 def rejected(self):
  with self.assertRaises((ValueError,KeyError)):guard.check(self.root)
 def test_complete_current_fixture(self):self.assertEqual(guard.check(self.root)['main_results'],26)
 def test_omitted_main_result(self):
  self.mutate_json('palomar/REGISTRATION_PLAN_V2.json',lambda p:p['bundles'][0]['main_results'].pop());self.rejected()
 def test_dependency_is_not_direct_coverage(self):
  self.mutate_json('palomar/REGISTRATION_PLAN_V2.json',lambda p:p['bundles'][1]['main_results'][3].update(selected_declarations=[]));self.rejected()
 def test_unselected_claim(self):
  self.mutate_json('palomar/REGISTRATION_PLAN_V2.json',lambda p:p['bundles'][0]['main_results'][0].update(selected_declarations=['PaperP1.fake']));self.rejected()
 def test_orcid_removed(self):
  p=self.root/'palomar/v3/affine_events/formalization.yaml';p.write_text(p.read_text().replace('0009-0008-8491-2467',''));self.rejected()
 def test_unpermitted_axiom(self):
  self.mutate_json('RegistryV2/comparator/p1_affine_events.json',lambda p:p['permitted_axioms'].append('sorryAx'));self.rejected()
 def test_noncanonical_challenge_import(self):
  p=self.root/'RegistryV2/ChallengeP1V2AffineEvents.lean';p.write_text(p.read_text().replace('module\n','module\nimport PaperP1\n',1));self.rejected()
 def test_solution_challenge_dependency(self):
  p=self.root/'RegistryV2/SolutionP1V2AffineEvents.lean';p.write_text(p.read_text().replace('module\n','module\nimport ChallengeP1V2AffineEvents\n',1));self.rejected()
 def test_solution_placeholder(self):
  p=self.root/'RegistryV2/SolutionP1V2AffineEvents.lean';p.write_text(p.read_text()+'\ntheorem unwanted : True := by sorry\n');self.rejected()
 def test_conditional_premise_changed(self):
  p=self.root/'RegistryV2/SolutionP1V2StoppingReconstruction.lean';p.write_text(p.read_text().replace('(hfixed : FixedActivity C β)','(hfixed : True)'));self.rejected()
 def test_exact_mean_replaced(self):
  p=self.root/'RegistryV2/ChallengeP1V2QuadraticLimits.lean';p.write_text(p.read_text().replace('quadraticMass (actualMean N L)','quadraticMass (nominalMean N L)'));self.rejected()
 def test_forged_official_status(self):
  self.mutate_json('palomar/v3/VALIDATION.json',lambda p:p.update(official_full_preflight_passed=True));self.rejected()
 def test_failed_checker(self):
  self.mutate_json('palomar/v3/VALIDATION.json',lambda p:p['kernel_checks']['bundles'][0].update(actual_comparator_exit=1));self.rejected()
 def test_extra_workflow_registration(self):
  p=self.root/'.github/workflows/palomar-preflight.yml';p.write_text(p.read_text().replace('          - affine_events','          - unwanted_seventh\n          - affine_events'));self.rejected()
 def alter_compiled_binding(self,ending,action):
  path='palomar/v3/compiled-types.json';p=self.root/path;x=json.loads(p.read_text())
  action(next(row for row in x if row['name'].endswith(ending)))
  p.write_text(json.dumps(x,indent=2)+'\n')
  self.mutate_json('palomar/v3/VALIDATION.json',lambda v:v['evidence_files'].update({path:hashlib.sha256(p.read_bytes()).hexdigest()}))
 def test_conditional_compiled_premise_cannot_be_hidden_by_rehashing(self):
  self.alter_compiled_binding('.conditional_transfer',lambda row:next(b for b in row['binders'] if b['name']=='hfixed').update(type='True'))
  self.rejected()
 def test_nominal_constant_cannot_follow_epsilon_after_rehashing(self):
  self.alter_compiled_binding('.nominal_quadratic_comparison',lambda row:row['binders'].append({'name':'ε','type':'Real','is_proposition':False,'instance_implicit':False}))
  self.rejected()
 def test_omitted_audit(self):
  self.mutate_json('RegistryV2/audit-declarations.json',lambda p:p.pop());self.rejected()
 def test_changed_compiled_type(self):
  self.mutate_json('palomar/v3/compiled-types.json',lambda p:p[0].update(type='True'));self.rejected()
if __name__=='__main__':unittest.main()
