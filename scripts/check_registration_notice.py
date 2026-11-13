#!/usr/bin/env python3
"""Verify the documentary PDF edition against actual issued registry records."""
from pathlib import Path
import hashlib,json,re
from check_registered_coverage import inspect
from check_registry_final import check as check_final

ROOT=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())

def check(root=ROOT):
    root=Path(root);current=read(root/'manuscripts/paper-p1/REGISTRATION_NOTICE_CURRENT.json')
    assert re.fullmatch(r'manuscripts/paper-p1/registration-update-\d{4}-\d{2}-\d{2}',current['package'])
    package=root/current['package'];p=read(package/'DOCUMENTARY_UPDATE.json')
    actual=inspect(root,require_all=True);check_final(root)
    assert p['registered_count']==actual['registered_dossiers']==5
    assert p['main_results_covered']==actual['registered_main_results']==26
    assert p['selected_statements']==actual['registered_selected_declarations']==42
    assert p['direct_companion_results']==['T13.1','T15.1']
    assert {r['url'] for r in p['public_registrations']}=={r['url'] for r in actual['records']}
    source=package/'sources';base=root/p['baseline_source_directory']
    files=sorted(source.rglob('*.tex'));assert len(files)==len(p['source_files'])==34
    for path in files:
        name=str(path.relative_to(source));assert not path.is_symlink()
        assert sha(path)==p['source_files'][name]
    assert [str(path.relative_to(source)) for path in files if sha(path)!=sha(base/path.relative_to(source))]==['formalization.tex']
    notice=(source/'formalization.tex').read_text()
    assert not re.search(r'\\begin\{(?:theorem|proposition|lemma|corollary)\}',notice)
    assert all(r['id'] in notice for r in actual['records'])
    links=read(package/'qa/pdf-link-validation.json');visual=read(package/'qa/visual-review.json')
    assert links['registered_count']==visual['registered_count']==5 and visual['status']=='pass'
    for document,row in p['pdfs'].items():
        assert sha(package/row['path'])==row['sha256']==links['pdfs'][document]['pdf_sha256']==visual['pdfs'][document]['pdf_sha256']
        assert links['pdfs'][document]['all_actual_registry_urls_verified'] is True
        assert links['pdfs'][document]['paired_pdf_file_links_checked']>0
        assert links['pdfs'][document]['all_paired_named_destinations_present'] is True
        assert set(links['pdfs'][document]['registry_urls'])=={r['url'] for r in actual['records']}
        for image in links['pdfs'][document]['rendered_pages']:assert sha(package/image['path'])==image['sha256']
    return {'status':'pass','registered_dossiers':5,'main_results':26,'direct_companion_results':2,
            'unchanged_tex_files':33,'updated_tex_files':1,'pdfs':2}

if __name__=='__main__':print(json.dumps(check()))
