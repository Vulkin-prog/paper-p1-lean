P1 — VERSION 2.0
Édition de travail du 9 novembre 2026

Sharp Poisson approximation and second-order correction for long multiplicative runs
Brice Pouly

CONTENU DU DOSSIER

P1_V2_0_Main_EN.pdf
    Article principal en anglais, 32 pages. Il développe le modèle, les
    échelles arithmétiques, l'expansion arrêtée, la reconstruction de la loi,
    la preuve d'optimalité et les références à canaux explicites.

P1_V2_0_Companion_EN.pdf
    Compagnon technique en anglais, 84 pages. Il réunit les estimations
    arithmétiques, les preuves à sources fixées, la géométrie des triples
    et les contrôles uniformes de la grande cardinalité. L'article et ce
    compagnon constituent une même démonstration ; les deux sont nécessaires
    pour en vérifier l'ensemble.

P1_V2_0_Revision_FR.pdf
    Note française de 5 pages expliquant la nouvelle architecture, les renforcements,
    le périmètre retenu et le travail de correspondance formelle à reprendre.

sources/
    Sources LaTeX complètes des deux manuscrits, bibliographie et scripts
    de contrôle et de compilation.

editorial/
    Source de la note française, table de correspondance, inventaire des
    résultats et relectures d'intégration. CORRECTIONS_APPLIQUEES.txt indique
    la résolution des signalements contenus dans ces relectures chronologiques.

LECTURE ET LIENS ENTRE LES PDF

Conserver les deux PDF scientifiques dans le même dossier, sous leurs noms
fournis. Les renvois commençant par T désignent le compagnon ; les autres
désignent l'article. Les liens externes entre les PDF dépendent de ces noms
et du lecteur PDF utilisé. La numérotation imprimée reste utilisable si le
lecteur ne permet pas de suivre ces liens. La note française peut être
conservée dans le même dossier pour suivre ses liens vers les manuscrits.

RECONSTRUIRE LES DOCUMENTS

Les commandes suivantes s'exécutent depuis la racine de ce dossier.
Elles ne téléchargent aucune dépendance et n'appellent pas Lean.

1. Contrôler les sources actives et les renvois :

       python3 sources/check_sources.py

   Ce contrôle détecte notamment les labels absents ou dupliqués et les
   caractères de contrôle inattendus. Il ne vérifie pas les démonstrations.

2. Compiler l'article et le compagnon :

       python3 sources/build.py

   Le script alterne les compilations pdfLaTeX jusqu'à stabilisation des
   fichiers de renvois et des tables des matières. Il crée les fichiers
   temporaires dans sources/build/ et copie les deux PDF finaux à la racine
   du dossier. Les commandes sont exécutées sans autoriser shell-escape.

3. Compiler séparément la note française :

       python3 editorial/build_note.py

   Le script utilise editorial/revision_note.tex, écrit ses fichiers
   temporaires dans editorial/build/ et copie P1_V2_0_Revision_FR.pdf à la
   racine du dossier. Il ne modifie pas les sources des deux manuscrits.

Python 3 et une installation TeX Live fonctionnelle avec pdfLaTeX sont
nécessaires. Les dépendances LaTeX des manuscrits sont déclarées dans
sources/preamble.tex : Babel anglais, Latin Modern, microtype, geometry,
les packages mathématiques AMS, mathtools, mathrsfs, les packages de tableaux,
de listes et d'en-têtes, ainsi que xr-hyper, hyperref, bookmark et xurl.
La note utilise également Babel français. Les scripts Python fournis
n'utilisent que la bibliothèque standard.

Les journaux de compilation détaillent les erreurs éventuelles. Le script
scientifique s'arrête si les renvois ne se stabilisent pas ou si des
diagnostics de référence ou de débordement persistent. Un contrôle de
sources ou une compilation réussie ne remplace ni une relecture mathématique
ni une inspection visuelle ; les contrôles de livraison sont consignés
séparément dans les pièces de validation du dossier.

ORIGINE ET STATUT DE CETTE ÉDITION

La base est l'aperçu éditorial unifié du 7 novembre 2026 dans le dépôt :

    https://github.com/Vulkin-prog/paper-p1-lean
    commit fb83aec7b03ddef1397e3a7f9f8f8c458c82003a
    manuscripts/paper-p1/editorial-unified-preview-2026-11-07/

La V2.0 a été préparée comme une nouvelle édition séparée. Le dépôt source
et ses versions historiques n'ont pas été modifiés. La nouvelle structure
utilise l'autorisation de remanier un travail encore inédit : l'article
se concentre sur le nombre total de départs, et le compagnon fournit les
estimations de cette preuve. La branche du champ positionnel, de la
suppression, du forçage et de certaines conséquences supplémentaires n'est
plus comprise dans cette édition.

editorial/CORRESPONDANCE_V1_8_V2_0.csv suit chacun des 167 résultats de la
base, avec sa destination, sa nouvelle numérotation, ses références Lean
existantes et le travail d'alignement restant. L'inventaire complet de la
nouvelle édition se trouve dans editorial/result_inventory.json : il compte
118 résultats. Cinquante anciens résultats sont indiqués « Hors du périmètre
de P1 V2.0 ». Cette disposition est un choix de contenu ; elle ne signifie
pas que ces résultats sont faux. Leurs textes et preuves historiques
demeurent dans la base identifiée ci-dessus.

FORMALISATION

Le développement Lean associé est une source de preuves et de vérifications
antérieures, avec son compilateur et sa révision Mathlib fixés. Aucun nouveau
rejeu complet de Lean n'a été effectué pour la V2.0. La correspondance
renumérotée n'est donc pas présentée comme une nouvelle interface déjà
compilée.

Deux conclusions sont exposées par composition d'estimations existantes :
le contrôle Palm positif pour toutes les fenêtres cibles, y compris
irrégulières, et le comptage de supports complets uniforme en leur taille
minimale et en la sous-famille choisie. Leur formulation intégrée doit encore
recevoir une interface Lean correspondante. Les autres réorganisations,
regroupements et formes fortes sont également documentés dans la table
pour faciliter la comparaison des énoncés avant la reprise formelle.

La mention d'assistance et la note formelle dans les manuscrits précisent
leur statut. Ni une publication, ni une nouvelle certification, ni une
validation humaine indépendante ne sont revendiquées par ce dossier.
