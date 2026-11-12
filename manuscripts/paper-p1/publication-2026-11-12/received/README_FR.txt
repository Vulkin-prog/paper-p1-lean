P1 — Dossier de publication

Contenu

P1_Main_EN.pdf : article principal en anglais, 33 pages.
P1_Companion_EN.pdf : compagnon technique en anglais, 84 pages.
sources/ : sources LaTeX complètes, bibliographie commune figée, listes
bibliographiques locales et script de compilation.
NOTE_DE_LIVRAISON_FR.txt : modifications éditoriales et portée des contrôles.
verification.json : résultats des contrôles de structure et de liens.
source_provenance.json : sources documentaires et empreintes des fichiers.

Recompiler

Prérequis : Python 3 et une installation TeX Live disposant de pdfLaTeX et
des paquets déclarés dans sources/preamble.tex. Le script de compilation
utilise uniquement la bibliothèque standard de Python.

Depuis le dossier décompressé :

    python3 sources/build.py

Le script reconstruit les deux bibliographies locales à partir de
sources/bibliography.tex, puis compile les deux textes jusqu'à stabilisation
réciproque de leurs références. Les PDF reconstruits sont écrits dans
sources/P1_Main_EN.pdf et sources/P1_Companion_EN.pdf. Les journaux et le
rapport de compilation se trouvent dans sources/build/.

Conserver les deux PDF dans le même dossier : leurs liens croisés utilisent
les noms P1_Main_EN.pdf et P1_Companion_EN.pdf.

Complément documentaire prévu

Les identifiants des enregistrements Palomar pourront être ajoutés dans le
fichier commun sources/formalization.tex. La notice distingue déjà les
preuves, les contrôles locaux et l'enregistrement officiel. Aucun autre
emplacement à compléter n'est laissé dans les articles.
