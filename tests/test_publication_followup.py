"""Scope, attribution and manual-caller controls for the metadata enrichment."""
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import yaml

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from check_publication_followup import check_metadata_patch,check_plan,validate

class FollowupTests(unittest.TestCase):
    def setUp(self):
        self.plan=json.loads((ROOT/'palomar/PUBLICATION_FOLLOWUP_METADATA.json').read_text())
        self.old=json.loads((ROOT/'palomar/REGISTRATION_PLAN_PUBLICATION.json').read_text())
        row=self.plan['remaining_bundles'][0]
        self.updated=yaml.safe_load((ROOT/row['metadata']).read_text())
        self.baseline=yaml.safe_load((ROOT/row['baseline_metadata']).read_text())

    def test_actual_five_dossiers_keep_scope_and_author(self):
        self.assertEqual(validate()['remaining_selected_theorems'],42)

    def test_omitted_assistance_and_changed_author_are_refused(self):
        absent=deepcopy(self.updated);absent['automation']['methods'].pop()
        altered=deepcopy(self.updated);altered['project']['authors'][0]['orcid']='0000-0000-0000-0000'
        for data in (absent,altered):
            with self.subTest(data=data is absent),self.assertRaises(ValueError):
                check_metadata_patch(data,self.baseline,self.plan)

    def test_duplicate_first_dossier_and_scope_changes_are_refused(self):
        extra=deepcopy(self.plan);extra['remaining_bundles'].append(deepcopy(extra['remaining_bundles'][0]))
        scope=deepcopy(self.plan);scope['remaining_bundles'][0]['selected_declarations'].pop()
        for plan in (extra,scope):
            with self.assertRaises(ValueError):check_plan(plan,self.old)

    def select(self,bundle,edition='followup',relationship='I am a responsible author or maintainer'):
        workflow=yaml.load((ROOT/'.github/workflows/palomar-publication-preflight.yml').read_text(),Loader=yaml.BaseLoader)
        script=workflow['jobs']['select']['steps'][0]['run']
        prefix="python3 - <<'PY'\n";self.assertTrue(script.startswith(prefix))
        code=script[len(prefix):].rsplit('\nPY',1)[0]
        with tempfile.TemporaryDirectory() as directory:
            output=Path(directory)/'outputs'
            env={'P1_SOURCE':'a'*40,'P1_BUNDLE':bundle,'P1_RELATIONSHIP':relationship,'P1_METADATA_EDITION':edition,'GITHUB_OUTPUT':str(output)}
            run=subprocess.run([sys.executable,'-c',code],env=env,capture_output=True,text=True)
            data=dict(line.split('=',1) for line in output.read_text().splitlines()) if output.exists() else {}
            return run,data

    def test_caller_selects_all_five_corrected_metadata_paths(self):
        for slug in self.plan['remaining_sequence']:
            run,data=self.select(slug);self.assertEqual(run.returncode,0,run.stderr)
            options=json.loads(data['options'])
            self.assertEqual(options['formalization_metadata_path'],'palomar/publication-followup/'+slug+'/formalization.yaml')
            self.assertEqual(options['comparator_config_path'],'RegistryV2/comparator/p1_'+slug+'.json')
            self.assertRegex(data['request_id'],r'^pf[0-9a-f]{10}$')

    def test_caller_refuses_first_followup_arbitrary_paths_and_unsupported_role(self):
        for args in (('quadratic_limits','followup','I am a responsible author or maintainer'),
                     ('cumulants_optimality','../../elsewhere','I am a responsible author or maintainer'),
                     ('cumulants_optimality','followup','inferred owner')):
            run,data=self.select(*args);self.assertNotEqual(run.returncode,0);self.assertEqual(data,{})

    def test_original_first_dossier_selection_remains_available(self):
        run,data=self.select('quadratic_limits','publication');self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(data['options'])['formalization_metadata_path'],'palomar/publication/quadratic_limits/formalization.yaml')
        self.assertRegex(data['request_id'],r'^pb[0-9a-f]{10}$')

if __name__=='__main__':unittest.main()
