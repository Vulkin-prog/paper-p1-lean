# P1 — préparation Zenodo et première release

La release logicielle **v1.0.0** fige la formalisation et ses preuves publiques
de validation, après les cinq enregistrements Palomar. Le numéro du logiciel
est distinct de l’édition scientifique **P1 V2.0**. Les sources mathématiques,
les PDF, Lean, Mathlib et les cinq enregistrements ne changent pas pour cette
préparation. L’édition documentaire courante reste celle du 13 novembre 2026.

Deux dépôts Zenodo sont préparés :

1. **Article et compagnon**, avec les deux PDF et un ZIP autonome contenant les
   34 sources TeX exactes et un programme compilant les deux textes ensemble.
2. **Formalisation Lean**, avec l’archive complète du dépôt au tag de la release,
   les correspondances, l’historique mathématique et les preuves publiques de
   qualification et d’enregistrement déjà suivies dans Git.

Auteur humain : **Brice Pouly**, ORCID
[0009-0008-8491-2467](https://orcid.org/0009-0008-8491-2467).
`CITATION.cff` fournit la citation GitHub ; `.zenodo.json` contient les mêmes
données pour Zenodo. Aucun DOI P1 n’est supposé ni copié du Paper C.
Les rôles de ChatGPT (GPT-6 Astra) et de Codex sont conservés dans les descriptions.
La licence du logiciel est Apache-2.0. La licence des manuscrits est une décision
distincte de l’auteur : voir [LICENSE_SCOPE.md](../LICENSE_SCOPE.md).

## Génération et contrôles

Depuis un dépôt Git propre contenant les fichiers de la release :

```sh
python3 scripts/check_disk.py
python3 scripts/check_registration_notice.py
python3 scripts/check_registered_coverage.py --require-all
python3 scripts/package_zenodo_release.py --output-dir /chemin/Ubuntu/nouveau-dossier
python3 scripts/check_disk.py
```

Le dossier de sortie doit être nouveau, vide, sur la partition Ubuntu et hors
du dépôt. Le programme lit les fichiers du commit, jamais des fichiers voisins
ou privés. Il produit :

- `paper-p1-lean-v1.0.0.zip` : chaque fichier Git suivi, vérifié contre son objet
  Git ; aucun `.git`, `.lake`, cache de dépendance ou fichier opérationnel privé.
- `P1_paper_companion_sources_2026-11-14.zip` : les 34 TeX, les deux PDF exacts,
  un `build.py` autonome, les informations d’origine, les droits et les empreintes.
- Les deux PDF séparés, `PAPER_BUILD_VALIDATION.json`, `RELEASE_MANIFEST.json`,
  `SHA256SUMS`, `RELEASE_NOTES.md`, `ZENODO_DEPOSIT_FR.md` et les deux fichiers
  de métadonnées Zenodo.

Le ZIP du papier est extrait dans un répertoire neuf et son propre programme
recompile réellement les deux documents. Le contrôle exige la stabilisation
des références, l’absence de diagnostics non résolus ou de débordement, 33/84
pages et l’égalité du texte intégral extrait avec les PDF canoniques. Il n’exige
pas l’égalité binaire des PDF recompilés : les horodatages peuvent la changer.
Les PDF canoniques et tous les TeX conservent leurs empreintes documentées.

Le dernier contrôle complet de la formalisation avant cette préparation est
[le run 43518789449](https://github.com/Vulkin-prog/paper-p1-lean/actions/runs/43518789449)
au commit `40b19b56d06d0de0d60ca88dd9855c5a21e38ff5` : construction complète,
audit parent de 20 019 déclarations, audit RegistryV2 de 262 déclarations et audit
RegistryFinal de 111 déclarations. Le programme vérifie que seuls les fichiers
de préparation de la release ont changé depuis ce contrôle ; il n’attribue pas
ce contrôle à un autre commit. Aucune nouvelle soumission Palomar n’est lancée.

## Publication et DOI

Les fichiers générés sont joints à la
[release v1.0.0](https://github.com/Vulkin-prog/paper-p1-lean/releases/tag/v1.0.0).
Les métadonnées préparées ne créent pas un dépôt Zenodo. La session Zenodo
disponible n’est pas connectée et le dépôt GitHub n’est pas relié automatiquement
à Zenodo lors de cette préparation. `ZENODO_DEPOSIT_FR.md` indique les fichiers
et champs des deux dépôts manuels. Après création des vrais DOI, ajouter les
liens réciproques papier/logiciel dans leurs métadonnées et dans la citation.

Pour une intégration future, suivre la
[liaison officielle GitHub–Zenodo](https://help.zenodo.org/docs/github/enable-repository/)
avant la release concernée. Éviter de créer un dépôt manuel en double d’une
ingestion automatique. Lorsque les deux fichiers de citation sont présents,
Zenodo utilise [`.zenodo.json`](https://help.zenodo.org/docs/github/describe-software/zenodo-json/).
