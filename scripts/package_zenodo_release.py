#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Package a committed P1 release and rebuild the standalone paper source ZIP.

Only committed files are read. No Zenodo record is created and no DOI is invented.
Run from a clean Git checkout; choose a new, empty output directory on Ubuntu.
Requires Python >= 3.9, Git, pdflatex, pdfinfo and pdftotext.
"""
from pathlib import Path, PurePosixPath
import argparse
import datetime
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
SPEC = 'release/v1.0.1.json'
TITLE = 'Sharp Poisson approximation and second-order correction for long multiplicative runs'


def run(*args, **kwargs):
    return subprocess.check_output(args, cwd=ROOT, **kwargs)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encode(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode('utf-8')


def package(output):
    if run('git', 'status', '--porcelain').strip():
        raise RuntimeError('Commit the release files first; a clean checkout is required')
    output = output.resolve()
    if output == ROOT or output.is_relative_to(ROOT):
        raise ValueError('Use an output directory outside the repository')
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ValueError('Use a new, empty output directory')
    if output.stat().st_dev != Path('/').stat().st_dev:
        raise ValueError('The output directory must be on the Ubuntu root partition')
    if shutil.disk_usage(output).free < 5 * 1024 ** 3:
        raise RuntimeError('Less than 5 GiB remain on Ubuntu; suspend packaging')
    commit = run('git', 'rev-parse', 'HEAD').decode().strip()

    def blob(path):
        return run('git', 'show', commit + ':' + path)

    def read(path):
        return json.loads(blob(path))

    spec = read(SPEC)
    version, tag, date = spec['version'], spec['tag'], spec['date']
    repository = spec['repository']
    base_url = 'https://github.com/' + repository
    release_url = base_url + '/releases/tag/' + tag
    paper_package = spec['manuscript_package']
    pointer = read('manuscripts/paper-p1/REGISTRATION_NOTICE_CURRENT.json')
    if pointer['package'] != paper_package:
        raise ValueError('The release must use the current documentary manuscript edition')
    documentary = read(paper_package + '/DOCUMENTARY_UPDATE.json')
    records = documentary['public_registrations']
    if len(records) != 5 or documentary['main_results_covered'] != 26:
        raise ValueError('Expected the completed five-record, 26-main-result allocation')
    software_meta = read('.zenodo.json')
    if (software_meta['version'] != version or software_meta['publication_date'] != date
            or software_meta['license'] != spec['software_license']
            or software_meta['creators'] != [{'name': 'Pouly, Brice', 'orcid': '0009-0008-8491-2467'}]):
        raise ValueError('Inconsistent software citation/Zenodo release metadata')
    # The complete CI already checked the mathematical files. Verify that this
    # packaging release really changes only the explicitly reviewed release files.
    allowed = {'.zenodo.json', '.gitattributes', 'CITATION.cff', 'LICENSE_SCOPE.md', 'README.md', SPEC,
               'release/v1.0.0.json', 'LICENSE_MANUSCRIPTS.md', 'LICENSE_CC_BY_4_0.txt',
               'docs/ZENODO_RELEASE.md', 'scripts/package_zenodo_release.py',
               'scripts/paper_source_build.py'}
    changed = set(run('git', 'diff', '--name-only', spec['reference_complete_ci']['source_commit'],
                      commit).decode().splitlines())
    if not changed <= allowed:
        raise ValueError('Additional changes require a newly qualified release: ' + str(sorted(changed - allowed)))

    paper_files = {}
    for name, expected in sorted(documentary['source_files'].items()):
        data = blob(paper_package + '/sources/' + name)
        if sha(data) != expected:
            raise ValueError('Changed manuscript source: ' + name)
        paper_files['sources/' + name] = data
    if len(paper_files) != 34:
        raise ValueError('Expected exactly 34 TeX files')
    for row in documentary['pdfs'].values():
        data = blob(paper_package + '/' + row['path'])
        if sha(data) != row['sha256']:
            raise ValueError('Changed canonical PDF: ' + row['path'])
        paper_files[row['path']] = data
        (output / Path(row['path']).name).write_bytes(data)
    paper_files['build.py'] = blob('scripts/paper_source_build.py')
    paper_files['LICENSE_BUILD.txt'] = blob('LICENSE')
    paper_files['LICENSE_SCOPE.md'] = blob('LICENSE_SCOPE.md')
    if (spec['manuscript_license'] != 'CC-BY-4.0'
            or spec['zenodo_manuscript_license'] != 'cc-by-4.0'):
        raise ValueError('The author selected CC BY 4.0 for both P1 manuscripts')
    for path in ['LICENSE_MANUSCRIPTS.md', 'LICENSE_CC_BY_4_0.txt']:
        data = blob(path)
        paper_files[path] = data
        (output / path).write_bytes(data)
    paper_files['DOCUMENTARY_UPDATE.json'] = blob(paper_package + '/DOCUMENTARY_UPDATE.json')
    paper_files['REGISTRY_SNAPSHOT.json'] = blob(paper_package + '/REGISTRY_SNAPSHOT.json')
    rights = ('Le papier et le compagnon, y compris leurs sources LaTeX et leurs PDF, sont sous '
              'Creative Commons Attribution 4.0 International (CC BY 4.0), selon le choix explicite '
              'de Brice Pouly du 14 novembre 2026. Voir `LICENSE_MANUSCRIPTS.md` et le texte officiel '
              '`LICENSE_CC_BY_4_0.txt` : https://creativecommons.org/licenses/by/4.0/.')
    paper_readme = f'''# P1 — sources du papier et du compagnon

{TITLE}

Auteur : Brice Pouly — https://orcid.org/0009-0008-8491-2467
Édition scientifique : V2.0 ; notice des cinq enregistrements mise à jour le 13 novembre 2026.
Archive préparée le {date} depuis {base_url}/tree/{commit}.

## Contenu et compilation

Les 34 fichiers de `sources/` sont les sources exactes des deux PDF canoniques
de `pdf/` (article : 33 pages ; compagnon : 84 pages). Les sources mathématiques
et la déclaration d’assistance sont conservées sans modification.

Prérequis : Python 3.9 ou plus récent, `pdflatex` et les paquets TeX Live utilisés
dans `sources/preamble.tex`. Sous Ubuntu, une installation convenable comprend
`texlive-latex-base texlive-latex-recommended texlive-latex-extra`
et `texlive-fonts-recommended` (avec `lmodern`).

Depuis le dossier contenant ce README, exécuter :

```sh
python3 build.py
```

Le programme compile les DEUX documents en alternance jusqu’à stabilisation des
références croisées, sans activation de commandes externes par TeX. Il place les
nouveaux PDF dans `rebuilt-pdf/` et les journaux dans `build-evidence/` ; les PDF
canoniques de `pdf/` restent intacts. Il ne nécessite ni Lean ni le dépôt GitHub.
Garder les deux PDF ensemble, avec leurs noms exacts, pour leurs liens réciproques.
La compilation indépendante d’un seul document ne suffit pas pour ces références.
Les horodatages et identifiants internes peuvent changer les empreintes des PDF
recompilés ; le nombre de pages et le texte intégral ont été comparés aux originaux.

`MANIFEST.json` et `SHA256SUMS` permettent de contrôler l’intégrité de l’archive.
Les bibliographies sont incluses en TeX ; aucune base BibTeX ni image externe
n’est nécessaire. Il n’y a pas d’artefact de compilation à installer.

## Formalisation, droits et assistance

Les cinq enregistrements Palomar et leurs sources exactes sont décrits dans
`DOCUMENTARY_UPDATE.json` et dans la notice incluse aux deux documents.
Ils couvrent les 26 résultats numérotés du papier principal par 42 énoncés
sélectionnés. T13.1 et T15.1 du compagnon, ainsi que le corollaire séquentiel
affiché de T15.1, sont directement sélectionnés ; les 92 résultats du compagnon
ne sont pas tous déclarés comme enregistrés. Les hypothèses imprimées, notamment
l’entrée conditionnelle d’ordre 254 du Théorème 5.2, restent explicites.

{rights}
Le programme `build.py` est sous Apache-2.0 (`LICENSE_BUILD.txt`), distincte
de la licence CC BY 4.0 des manuscrits.
La déclaration d’assistance dans `sources/assistance.tex` est conservée :
ChatGPT (GPT-6 Astra) a assisté le travail mathématique et éditorial ; le
développement Lean a bénéficié de l’assistance de Codex. Brice Pouly reste
l’auteur humain responsable. Cette archive ne crée aucun DOI Zenodo.
'''
    paper_files['README_FR.md'] = paper_readme.encode('utf-8')
    paper_files['MANIFEST.json'] = encode({
        'schema_version': 1, 'kind': 'paper_and_companion_source_distribution',
        'source_commit': commit, 'repository': base_url, 'date': date,
        'scientific_version': spec['scientific_manuscript_version'],
        'documentary_edition': paper_package, 'manuscript_license': spec['manuscript_license'],
        'files': {name: {'bytes': len(data), 'sha256': sha(data)}
                  for name, data in sorted(paper_files.items())},
        'manifest_and_checksum_file_are_excluded_from_manifest_file_list': True
    })
    paper_files['SHA256SUMS'] = ''.join(sha(data) + '  ' + name + '\n'
                                      for name, data in sorted(paper_files.items())).encode()
    paper_zip = output / f'P1_paper_companion_sources_{tag}_{date}.zip'
    prefix = 'P1_paper_companion_sources/'
    timestamp = datetime.datetime.fromtimestamp(int(run('git', 'show', '-s', '--format=%ct', commit)),
                                               datetime.timezone.utc).timetuple()[:6]
    with zipfile.ZipFile(paper_zip, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name, data in sorted(paper_files.items()):
            info = zipfile.ZipInfo(prefix + name, date_time=timestamp)
            info.create_system = 3
            info.external_attr = (0o100755 if name == 'build.py' else 0o100644) << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, data, compresslevel=9)
    print('Paper ZIP created; checking extracted standalone compilation.', flush=True)
    with zipfile.ZipFile(paper_zip) as archive:
        if archive.testzip() is not None:
            raise ValueError('Paper ZIP CRC failure')
        for path, data in paper_files.items():
            if archive.read(prefix + path) != data:
                raise ValueError('Paper ZIP content mismatch: ' + path)
        with tempfile.TemporaryDirectory(prefix='p1-source-zip-test-', dir=output) as temporary:
            archive.extractall(temporary)
            extracted = Path(temporary) / prefix
            evidence = output / 'verification'
            subprocess.run([sys.executable, str(extracted / 'build.py'), '--evidence-dir', str(evidence)],
                           cwd=extracted, check=True)
            build_receipt = json.loads((evidence / 'build-validation.json').read_text())
            comparisons = []
            for document, row in documentary['pdfs'].items():
                original = extracted / row['path']
                rebuilt = extracted / 'rebuilt-pdf' / Path(row['path']).name
                original_text = run('pdftotext', '-layout', str(original), '-')
                rebuilt_text = run('pdftotext', '-layout', str(rebuilt), '-')
                if original_text != rebuilt_text:
                    raise ValueError('Rebuilt PDF text differs: ' + document)
                built = next(p for p in build_receipt['pdfs'] if p['document'] == document)
                if built['pages'] != row['pages']:
                    raise ValueError('Rebuilt PDF page count differs: ' + document)
                comparisons.append({'document': document, 'pages': built['pages'],
                                    'full_extracted_text_matches': True,
                                    'extracted_text_sha256': sha(original_text),
                                    'canonical_pdf_sha256': row['sha256'],
                                    'rebuilt_pdf_sha256': built['sha256']})
    build_receipt['source_zip'] = {'filename': paper_zip.name, 'sha256': sha(paper_zip.read_bytes())}
    build_receipt['source_commit'] = commit
    build_receipt['canonical_pdf_comparisons'] = comparisons
    (output / 'PAPER_BUILD_VALIDATION.json').write_bytes(encode(build_receipt))

    software_zip = output / f'paper-p1-lean-{tag}.zip'
    software_prefix = f'paper-p1-lean-{tag}/'
    subprocess.run(['git', 'archive', '--format=zip', '--prefix=' + software_prefix,
                    '--output=' + str(software_zip), commit], cwd=ROOT, check=True)
    tree = {}
    for entry in run('git', 'ls-tree', '-rz', '--full-tree', commit).split(b'\0'):
        if entry:
            metadata, path = entry.split(b'\t', 1)
            mode, kind, oid = metadata.decode().split()
            if kind != 'blob' or mode not in ['100644', '100755']:
                raise ValueError('Unsupported tree entry: ' + path.decode())
            tree[path.decode()] = oid
    with zipfile.ZipFile(software_zip) as archive:
        if archive.testzip() is not None:
            raise ValueError('Software ZIP CRC failure')
        actual = [i.filename.removeprefix(software_prefix) for i in archive.infolist() if not i.is_dir()]
        if len(actual) != len(tree) or set(actual) != set(tree):
            raise ValueError('Software ZIP does not contain the complete Git tree')
        for path in actual:
            parts = PurePosixPath(path).parts
            if path.startswith('/') or '..' in parts or any(p in {'.git', '.lake', '__pycache__'} for p in parts):
                raise ValueError('Unsafe or generated archive entry: ' + path)
            data = archive.read(software_prefix + path)
            git_oid = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            if git_oid != tree[path]:
                raise ValueError('Git blob mismatch: ' + path)
        if archive.comment.decode() != commit:
            raise ValueError('Software ZIP commit comment differs')
    print(f'Software ZIP checked against all {len(tree)} committed files.', flush=True)

    record_lines = '\n'.join(f'- [{r["id"]} v{r["version"]}]({r["url"]}) — source `{r["source_commit"]}`.'
                             for r in records)
    notes = f'''# P1 — formalization {tag}

License and deposit-metadata update of the first archived P1 software release.
The article and companion are now explicitly CC BY 4.0, as selected by the author
on 14 November 2026. The previous v1.0.0 release remains unchanged. The scientific
edition is P1 V2.0 with its five issued Palomar records and documentary notice.
Author: [Brice Pouly](https://orcid.org/0009-0008-8491-2467).

## Exact source and scope

- Release commit: `{commit}`; tag: `{tag}`.
- Lean: `{blob('lean-toolchain').decode().strip()}`.
- Mathlib: `9d581dfff2e41de989072ea63abf3daf69311520`.
- Checked correspondence: all 118 numbered results (26 main, 92 companion),
  with printed hypotheses retained, including the order-254 input in main Theorem 5.2.
- Five Palomar records cover all 26 numbered main results through 42 selections.
  Direct companion selections are T13.1, T15.1 and the latter's displayed sequence
  corollary. This does not claim separate registration of all companion results.

{record_lines}

The release preserves every issued record, exact registered source and public
qualification receipt. The first record's published non-blocking AI-disclosure
warning remains documented; the four subsequent records have no published warnings.
The complete CI at `{spec['reference_complete_ci']['source_commit']}`
[passed]({spec['reference_complete_ci']['url']}). This release changes only
packaging, citation and release documentation: Lean files, dependency pins,
manuscript source/PDFs and existing registration evidence are unchanged.

## Download and reuse

- `{software_zip.name}`: complete tracked repository snapshot, including proofs,
  historical manuscripts, alignment ledgers and public validation/registration evidence.
- `{paper_zip.name}`: standalone 34-file TeX source set, both canonical PDFs,
  and a build helper. Extracted from the ZIP and actually rebuilt: 33/84 pages,
  stable references, no remaining undefined or overfull diagnostics, and full
  extracted text equal to the supplied PDFs.
- `P1_Main_EN.pdf`, `P1_Companion_EN.pdf`: keep together for reciprocal file links.
- `LICENSE_MANUSCRIPTS.md`, `LICENSE_CC_BY_4_0.txt`: explicit author license grant
  for both manuscripts and the unmodified official CC BY 4.0 text.
- `RELEASE_MANIFEST.json`, `PAPER_BUILD_VALIDATION.json`, `SHA256SUMS`: provenance,
  actual packaging/rebuild evidence and integrity hashes.
- `ZENODO_SOFTWARE_METADATA.json`, `ZENODO_PAPER_METADATA.json`, `ZENODO_DEPOSIT_FR.md`:
  separate software/paper deposit preparation. No Zenodo DOI has yet been assigned.

No dependency caches, compiled Lean artifacts, Git internals, account credentials,
private portal files or unpublished private reviews are collected. Historical
public reports already tracked in Git remain included.

Software: Apache-2.0. Article, companion and their LaTeX/PDF distributions: CC BY 4.0.
Third-party notices retained; see `LICENSE_SCOPE.md`. ChatGPT (GPT-6 Astra)'s mathematical/editorial role and
Codex's Lean assistance are disclosed. Brice Pouly remains responsible.
'''
    (output / 'RELEASE_NOTES.md').write_text(notes, encoding='utf-8')
    (output / 'ZENODO_SOFTWARE_METADATA.json').write_bytes(blob('.zenodo.json'))
    paper_meta = {
        'title': TITLE, 'upload_type': 'publication', 'publication_type': 'preprint',
        'creators': software_meta['creators'], 'version': spec['scientific_manuscript_version'],
        'publication_date': date, 'language': 'eng',
        'keywords': software_meta['keywords'],
        'description': '<p>Article and technical companion by Brice Pouly, with exact LaTeX sources. '
                       'Scientific edition V2.0; the documentary formalization notice was updated on '
                       '13 November 2026 with five issued Palomar records. The principal article has '
                       '33 pages and 26 numbered results; the companion has 84 pages and 92 numbered '
                       'results. The associated Lean formalization retains the printed conditional '
                       'hypotheses. All 26 main results are covered by the five Palomar records; this '
                       'does not claim direct registration of all companion results. Mathematical '
                       'and editorial assistance from ChatGPT (GPT-6 Astra), and AI assistance for '
                       'Lean, are disclosed in the preserved assistance statement. Brice Pouly is '
                       'the responsible human author.</p>',
        'related_identifiers': [{'identifier': release_url, 'relation': 'isSupplementedBy', 'scheme': 'url'}]
    }
    paper_meta.update(license=spec['zenodo_manuscript_license'], access_right='open')
    (output / 'ZENODO_PAPER_METADATA.json').write_bytes(encode(paper_meta))
    deposit = f'''# Préparation des deux dépôts Zenodo — P1

## 1. Article et compagnon

Créer un dépôt de type « Publication / Preprint » (ou une nouvelle version d’un
éventuel dépôt P1 existant, sans créer de doublon). Titre : **{TITLE}**.
Auteur : **Brice Pouly**, ORCID **0009-0008-8491-2467**.
Version scientifique : **2.0**, avec mise à jour documentaire du 13 novembre 2026.
Date proposée du dépôt : **{date}** ; l’adapter à la date effective de publication.

Fichiers à déposer ensemble :

- `P1_Main_EN.pdf` (33 pages) ;
- `P1_Companion_EN.pdf` (84 pages) ;
- `{paper_zip.name}` (sources exactes des deux documents et compilation autonome).
- `LICENSE_MANUSCRIPTS.md` et `LICENSE_CC_BY_4_0.txt` (licence explicite des deux manuscrits).

Les champs descriptifs sont préparés dans `ZENODO_PAPER_METADATA.json`.
{rights}
La licence à sélectionner dans le dépôt Zenodo du papier est **CC BY 4.0**
(identifiant `cc-by-4.0`), déjà renseignée avec l’accès ouvert dans les métadonnées.
Garder les noms des deux PDF pour les liens réciproques. Les PDF canoniques ont
les mêmes empreintes que l’édition documentaire du dépôt, sans modification.

## 2. Formalisation Lean

Créer un dépôt **Software**, version **{version}**, licence du logiciel
**Apache-2.0**, avec le même nom et ORCID. Les mentions distinctes des manuscrits
et des tiers restent dans `LICENSE_SCOPE.md` et les fichiers reçus.

Déposer `{software_zip.name}`, `RELEASE_MANIFEST.json`, `SHA256SUMS`,
`PAPER_BUILD_VALIDATION.json`, `RELEASE_NOTES.md` et les métadonnées jointes.
L’archive complète du logiciel contient aussi les manuscrits historiques et les
preuves publiques de validation. Les caches de dépendances et artefacts compilés
sont exclus ; les reproduire avec les instructions du dépôt et les versions fixées.

Métadonnées : `ZENODO_SOFTWARE_METADATA.json` (égal au `.zenodo.json` du tag).
Release GitHub : {release_url}
Révision exacte : `{commit}`.

Le dépôt GitHub n’était pas relié à Zenodo lors de cette préparation ; aucun DOI
n’a été réservé ou publié par ces fichiers. Le dépôt manuel de la release est
prêt. Pour les releases futures, la liaison automatique nécessite une connexion
au compte Zenodo et l’activation du dépôt dans ses paramètres GitHub, AVANT la
nouvelle release : https://help.zenodo.org/docs/github/enable-repository/.
Éviter de déposer deux fois la même version par les deux voies.

## Liens entre les publications et vérification

Après attribution des DOI, ajouter le DOI du papier comme « Is supplement to »
dans le dépôt logiciel et le DOI du logiciel comme « Is supplemented by » dans
le dépôt du papier. Conserver le DOI de version et le DOI conceptuel distincts.
Un DOI du Paper C n’est pas un DOI du P1 ; aucun identifiant P1 n’est inventé ici.
Avant de publier, vérifier les fichiers, l’auteur/ORCID, la date effective et la
licence du papier. Les cinq notices Palomar sont des enregistrements distincts
de Zenodo et restent inchangées. Tous les liens sont dans `RELEASE_NOTES.md`.

Les empreintes de `SHA256SUMS` couvrent les fichiers de la release à l’exception
du fichier de sommes lui-même. Le manifeste lie les archives au commit Git.
La compilation extraite du ZIP a réellement produit les deux documents avec
33 et 84 pages et le même texte intégral que les PDF canoniques.
'''
    (output / 'ZENODO_DEPOSIT_FR.md').write_text(deposit, encoding='utf-8')
    assets = sorted(p for p in output.iterdir() if p.is_file())
    manifest = {
        'schema_version': 1, 'version': version, 'tag': tag, 'release_date': date,
        'repository': base_url, 'release_url': release_url, 'source_commit': commit,
        'lean_toolchain': blob('lean-toolchain').decode().strip(),
        'mathlib_commit': '9d581dfff2e41de989072ea63abf3daf69311520',
        'creator': software_meta['creators'][0],
        'software_archive': {'filename': software_zip.name, 'root': software_prefix,
                             'tracked_files': len(tree), 'checked_against_every_git_blob': True},
        'paper_archive': {'filename': paper_zip.name, 'root': prefix, 'tex_files': 34,
                          'documentary_edition': paper_package, 'exact_source_hashes_checked': True,
                          'actual_extracted_zip_build_and_full_text_comparison': 'PAPER_BUILD_VALIDATION.json'},
        'reference_complete_ci': spec['reference_complete_ci'],
        'release_only_changes': sorted(changed),
        'registered_count': 5, 'main_results_covered': 26, 'selected_statements': 42,
        'public_registrations': [{'id': r['id'], 'version': r['version'], 'url': r['url'],
                                  'source_commit': r['source_commit']} for r in records],
        'zenodo_deposit_created': False, 'zenodo_doi': None,
        'software_license': spec['software_license'], 'manuscript_license': spec['manuscript_license'],
        'zenodo_manuscript_license': spec['zenodo_manuscript_license'],
        'manuscript_license_authority': spec['manuscript_license_authority'],
        'files': {p.name: {'bytes': p.stat().st_size, 'sha256': sha(p.read_bytes())} for p in assets},
        'manifest_and_checksum_file_are_excluded_from_manifest_file_list': True
    }
    (output / 'RELEASE_MANIFEST.json').write_bytes(encode(manifest))
    assets = sorted(p for p in output.iterdir() if p.is_file())
    (output / 'SHA256SUMS').write_text(''.join(sha(p.read_bytes()) + '  ' + p.name + '\n'
                                             for p in assets), encoding='utf-8')
    print(json.dumps({'status': 'passed', 'source_commit': commit,
                      'assets': {p.name: p.stat().st_size for p in output.iterdir() if p.is_file()},
                      'free_gib': round(shutil.disk_usage(output).free / 1024 ** 3, 2)}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    package(args.output_dir)
