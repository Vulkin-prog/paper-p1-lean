# Palomar preparation

**Submission hold, 7 November 2026.** The user has requested a pause before any
Palomar submission while both manuscripts receive independent mathematical and
editorial review. No full workflow, intake or registration has been launched.
Keep the six prepared dossiers; do not dispatch them until the user resumes.

The version 1.7 draft has 167 proved numbered statements: 73 in the article and 94 in the companion. The separate version 1.8 draft retains all 167 labels and has checked stronger statements at mathematical checkpoint P1-MATH-0998. The six selected registration configurations retain their existing exact types and qualification sources; the new witness endpoint is not an additional selection. The original version 1.6 and the two documented false-original scopes remain preserved.

## Six registrations, strictly successive

The user requested fewer than ten registrations, with five or six a good target. The chosen plan has **exactly six in total**, containing the same **68 selected declarations** from the **seventeen original components**. The [plan](../palomar/REGISTRATION_PLAN.json) records the ordering, source hashes and a bijective declaration map. The [overview](../palomar/v2/README.md) links all six configurations and metadata files. The preserved component interfaces and receipts under palomar/v1 are not additional submissions.

The [independent scope comparison](reviews/2026-11-07/registration-scope-audit.json)
checks the pre-consolidation source 3e5a5c0e563bbcfc1ab92472411f86dc1b44d74b:
all 68 selections occur once, all 17 families are present, and 85 original
interface, configuration, metadata and receipt files are byte-identical.
This exhaustivity concerns the original selection, rather than 167 separate
registration targets. The 21 new reference-field theorems at checkpoint 0997
are in the development and companion but are not additional selected targets.

Run only one full cycle at a time: full workflow, intake, mechanical verification, private editorial review, the human decision, then actual registration or documented closure. The workflow has one global concurrency group and accepts one bundle, with no matrix and no all-bundles choice. Its mutex ends with the workflow; it does not represent a closed intake or editorial cycle. The operator must check the actual portal state and the recorded outcome before beginning the next bundle.

## Mathematical and local-check evidence

The original seventeen component source pairs and their receipts retain their exact bytes and historic source commits. The consolidated pairs preserve complete model definitions, theorem types and proof bodies through a coherent namespace relocation. Each Challenge imports only Mathlib and has deliberate holes only for its explicit selected theorems. No Solution, substantive proof or axiom audit imports a Challenge. The permitted axioms remain propext, Classical.choice and Quot.sound.

The [consolidation checker](../scripts/check_registry_consolidation.py) reconstructs every new module from its original components and rejects other edits. The [candidate checker](../scripts/check_registry_candidates.py) checks all seventeen components and six registrations. The [evidence checker](../scripts/check_registry_evidence.py) checks preserved logs, exact snapshots, inventories, configuration and current transitive proof imports, including imports between Solution modules. Historical receipts retain their own original audit counts.

```sh
python3 scripts/check_disk.py
python3 scripts/check_sources.py
python3 scripts/check_revised_sources.py --require-proved
python3 scripts/update_audit.py --check
python3 scripts/check_registry_candidates.py
python3 scripts/check_registry_consolidation.py
python3 scripts/check_palomar_sources.py
python3 scripts/check_registry_evidence.py --require-all
```

These local checks do not replace the full reusable Palomar workflow or editorial review. All proof and temporary files stay on the Ubuntu partition. Disk is checked before and after builds, downloads and large exports; available space below 10 GiB is reported, and large downloads stop below 5 GiB.

## Author and ORCID

Each active metadata file uses a structured person record with **Brice Pouly**, GitHub **Vulkin-prog**, and **ORCID 0009-0008-8491-2467**, together in project.authors, project.responsible_maintainers and the self-paper source authors. This follows the [official pinned person-record contract](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/README.md) and the [recent paper-c-lean example](https://github.com/Vulkin-prog/paper-c-lean/blob/main/palomar/v3prel/palm/formalization.yaml). It avoids a free-text name suffix or an unrecognized ORCID sidecar.

The official parser validates each actual metadata file and normalizes its author association. A separate receipt records the checksum and a bounded live lookup of the current ORCID record. That lookup is not personal authentication or a submitter-role declaration. The community v0.4 schema predates structured people; its check is explicitly limited to a name-only projection.

## Full workflow, intake and human decisions

The [single active caller](../.github/workflows/palomar-preflight.yml) pins both uses and pipeline_commit to PalomarSubmission **14aa8d6b3c2f14a8540605e37144560b9a00e7e7**, with mode full, execution_profile palomar-standard-v1 and read-only repository permissions. It selects one configuration under comparator/registrations and the matching palomar/v2 metadata. The previous three callers are preserved outside .github/workflows as historical evidence. The old fifteen-configuration request at source 0a9d3e68a8af39b6ea1ce725027f72ca5f10e8c4 is superseded by the six-registration scope.

Before dispatch, obtain the protocol-required truthful human relationship declaration. Before intake, present the exact repository, immutable 40-character source SHA, the single configuration and that relationship for human agreement. The full report must actually say status pass for that source and target. Do not weaken isolation, pins, source checks or standard limits to obtain a pass.

Use the [current intake protocol](https://submit.palomar-registry.org/llms.txt). The authenticated GitHub CLI route may prove repository write access with its prescribed temporary tag and secret gist, deleting both afterwards. Do not automate browser sign-in or recovery. Before permanent registration, show the actual private editorial review to the user and obtain their decision about publishing that exact review. Preserve the digest and record a registry identifier only after actual issuance. Finish or explicitly close this entire cycle before opening the next one. No workflow dispatch, intake, editorial decision, registration identifier or publication DOI is currently claimed.
