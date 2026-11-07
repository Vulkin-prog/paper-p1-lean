# Reprise éditoriale après vérification des interfaces

La copie de relecture la plus récente est l’[aperçu renforcé de 165 pages](editorial-proposals/2026-11-07/scientific-strengthening/README.md)
(article : 64 ; compagnon : 101). Elle conserve les cinq précisions initiales
et les treize simplifications, puis intègre des bornes déjà prouvées plus fortes
dans T9.1, T1.14 et T4.4. La clause à une cible reçoit son raccord homogène
positif explicite, et une remarque précise le témoin logarithmique 17 de 13.4,
hors du théorème attribué. Les [cinq dispositions scientifiques](editorial-proposals/2026-11-07/scientific-strengthening/amendments.json)
renvoient au journal existant et à 15 types réellement compilés, relus séparément.

Les 167 résultats et leurs numéros restent présents. Par rapport à 1.8, trois
blocs antérieurs précisaient déjà un contexte hérité ; les trois énoncés
renforcés s’y ajoutent. Les 161 autres blocs restent identiques. Les 548 labels
restants sont conservés ; les quatre anciens labels d’équations retirés avec
leur preuve restent sans réaffectation. Les nouvelles explications ajoutent 28
lignes à l’aperçu simplifié, sans augmenter son nombre de pages. Le gain de 277
lignes documenté pour les treize coupes se rapporte à ce stade précédent.

Les [trois aperçus de simplification](editorial-proposals/2026-11-07/integration-status.json)
et leurs reçus restent figés. Leur index décrit cette chaîne historique,
pas l’état ultérieur de la copie scientifique renforcée. Cette dernière possède
son propre reçu, sa revue du diff et son contrôle automatique. Aucune de ces
passes ne constitue une nouvelle version adoptée ni un nouvel énoncé original
déclaré faux. Les deux corrections nécessaires restent celles rappelées ci-dessous.

Le [nouveau raccord Palm](SHARP_GOOD_EDGE_PALM.md) possède quatre preuves
relues et un replay complet au checkpoint 1005. Ses propositions de coupes
supplémentaires restent distinctes et ne sont pas encore intégrées à cet aperçu.

Cette note conserve la justification des propositions initiales, en complément
de la [relecture initiale](reviews/2026-11-07/RAPPORT_FR.txt) et de la
[révision 1.8](MANUSCRIPT_REVISION_V1_8.md). Les formulations anglaises ci-dessous
sont des propositions historiques désormais intégrées aux aperçus séparés,
à adopter ou adapter par l’auteur dans une future version. Les sources et PDF
v1.8 restent préservés. La dernière source de preuve entièrement rejouée est
`d342b507332315c67b1463009061c03f14b5be9b`, sous Lean 4.36.0-rc2.

Les deux corrections nécessaires de la version originale restent T1.10
(rayon d'alignement) et T5.1 (plafond trivial de l'exposant). Elles sont déjà
intégrées aux versions révisées. La relecture ciblée des interfaces n'a
identifié aucun troisième énoncé original faux dans son contexte.

## 1. T22.7 : définir le noyau de la formule nominale

Dans la [proposition T22.7](../manuscripts/paper-p1/v1.8/sources/companion_sections/uniform_appendix.tex#L351),
préciser le sens de K_pi immédiatement après la formule. Le facteur nominal
p^r utilise le noyau sur toutes les coordonnées formelles d'occurrences,
avant quotient par les relations internes. La formule avec noyau relatif
effectif utilise le produit des marginales réelles. Les centres répétés
gardent leurs coordonnées distinctes dans les deux constructions.

Proposition de texte :

> Here K_pi is the kernel of the colored valuation map on the full formal
> occurrence-coordinate space, before quotienting by internal window
> relations. Repeated occurrences retain separate formal coordinates.
> Equivalently, after passing to the effective relative kernel, the nominal
> factor p^r is replaced by the product of the actual occurrence marginals.
> In both formulas the affine compatibility indicator is retained.

Preuves : `NominalRunReplicaFormula.companion_T22_7` et
`NominalRunReplicaFormula.heterogeneous_run_formula`. Le premier alias
ferme la formule seule. Conserver les preuves distinctes de propagation
positive et de moments dans l'index ; ne pas attribuer toute T22.7 à cet
alias de formule.

L'[exemple exact x=18,L=10](IRREGULAR_WINDOW_EXAMPLES.md) peut illustrer
ce choix de notation : sa probabilité réelle vaut 2^(-9), son noyau formel
a dimension un et sa nullité relative effective de singleton vaut zéro.

## 2. T8.2 : séparer les deux masses

Pour les [triplets primitifs denses](../manuscripts/paper-p1/v1.8/sources/companion_sections/confinement.tex#L191),
la probabilité de l'événement homogène peut être positive quand une
marginale affine originale est nulle. Employer explicitement la vraie
probabilité homogène dans cette clause et dans son argument de preuve.

Proposition de texte pour la preuve :

> Each primitive triple has homogeneous event probability at most
> K_C N^(-2), where K_C=8(2^C)^4. Combining this with the dense host
> count gives the homogeneous mass bound. This argument also covers
> irregular windows and does not require original affine compatibility.

`DensePrimitiveHomogeneousMass.companion_T8_2` ferme maintenant les trois
clauses imprimées sous un seuil commun. Le théorème précédent sur le poids
affine reste un résultat distinct et valide.

Le même [dossier d'exemples](IRREGULAR_WINDOW_EXAMPLES.md) prouve qu'à
x=3,L=7 la marginale originale est nulle tandis que la probabilité
homogène est positive. Il rend concrète la distinction entre ces objets.

## 3. 15.8 : rendre visibles les quantificateurs

Dans la [queue à support complet](../manuscripts/paper-p1/v1.8/sources/main_sections/exact_transfer.tex#L448),
la taille s peut être fixée avant toute perte epsilon. Le nouveau résultat
prouve même une borne pure N^(-a), pour a<2 fixé, sur le régime critique
et les types comprimés de largeur bornée fixés à l'avance.

Proposition de texte :

> The size cutoff s can be chosen independently of epsilon. In fact,
> for each fixed a<2 the same tail is at most N^(-a) above a suitable
> threshold. For one compressed block its independent weight is vp,
> charged once; all remaining factors are the actual vp_x.

Preuve : `FixedCutoffIndependentTail.article_15_8_fixed_cutoff`. Ne pas étendre cette
phrase au bord a=2 ni à une collection de types dont la largeur croît avec N.

## 4. 15.4 : rappeler le cutoff de fenêtre hérité

La [seconde assertion sur les petits noyaux](../manuscripts/paper-p1/v1.8/sources/main_sections/exact_transfer.tex#L202)
hérite du cutoff H=C_D B fixé précédemment. Ajouter un rappel évite de lire
une uniformité en H arbitraire, qui serait fausse.

Proposition de texte :

> Here H is the previously fixed window cutoff C_D B; in particular
> its ratio to L+1 is bounded by a fixed constant.

Preuve : `SmallKernelWindows.critical_two_count`. Ce rappel explicite le
contexte existant ; il ne constitue pas une nouvelle correction de l'énoncé.

## 5. 15.11 : conserver la portée différente des deux clauses

Dans les [budgets à plusieurs ancres](../manuscripts/paper-p1/v1.8/sources/main_sections/exact_transfer.tex#L693),
la condition theta+delta<1 concerne uniquement la clause saturée.
La clause modérée garde tous les paramètres de base imprimés, même si
theta+delta est supérieur ou égal à 1. Une preuve commune sous la condition
forte ne suffit donc pas comme référence unique pour les deux clauses.

Conserver `MultiAnchorModerateMass.uniform_bound` pour la première, avec
`MultiAnchorBudgets.article_15_11` pour la seconde. L'exemple de contrôle
t=4, A_0=3, b=9/10, sigma=3/4 donne theta+delta=163/120>1, avec un
exposant modéré -14/15. Le texte imprimé a déjà la bonne distinction ;
il s'agit surtout d'éviter sa perte pendant une réorganisation de la preuve.

## 6. T21.4 : conserver les variantes et les hypothèses de rang

L'index garde séparément la variante en dimension trois, les plans, la
sublinéarité et les seuils suffisants. Le raccord de poids au niveau beta=2
pour les triplets originaux utilise les deux rangs locaux pleins du contexte.
La primitivité seule ne les fournit pas. Une reprise éditoriale doit garder
ces conventions ou les rappeler avant d'appliquer ce raccord.

Les déclarations et hypothèses exactes sont dans la ligne T21.4 de
l'[index complet](MANUSCRIPT_ENDPOINTS_V1_8.md) et le
[rapport ciblé](reviews/2026-11-07/endpoint-dense.json).

## 7. Exemple N=18, q=3 : précision facultative

La version 1.8 imprime la borne valide rang<=10. La preuve ultérieure donne
rang=10, exactement deux affectations compatibles et probabilité 2^(-10).
On peut remplacer la majoration par cette égalité dans une future version,
en reprenant le [certificat et son explication](EXACT_RANK_EXAMPLE.md).
Cette égalité est maintenant intégrée aux aperçus séparés, sans modification
du texte v1.8 archivé ni nouvelle sélection Palomar.

## 8. 3.1 et 15.13 : conserver les implications imprimées

Ces deux résultats ont des prémisses mathématiques explicites dans le texte.
En particulier, [15.13](../manuscripts/paper-p1/v1.8/sources/main_sections/exact_transfer.tex#L874)
est un transfert à partir des 254 ordres fixés 3<=r<=256, pour beta fixé
dans 1<beta<=4/3. Sa preuve est une implication complète ; il ne faut pas
la reformuler comme une estimation sans sa prémisse d'activités connexes.
La formalisation conserve exactement cette distinction.

## Compléments de la dernière relecture indépendante

Le [rapport des 79 derniers résultats](reviews/2026-11-07/endpoint-remaining79.json)
complète l'examen direct des 167 labels, sans nouvelle lacune mathématique
confirmée. Il propose aussi de rendre trois conventions plus visibles :

- **7.2** : les listes ordonnées comptées sont injectives. La formulation
  « ordered lists of r distinct original windows » explicite cette convention.
- **13.4** : l'interface représente une courbe affine par l'idéal homogène
  premier de sa clôture projective, avec polynôme de Hilbert de degré un.
  Décrire ce raccord dans l'index évite de donner une lecture trop littérale
  du nom de la variable Lean.
- **T1.9** : le seuil premier agrandi domine le diamètre normalisé. Dans la
  dernière clause, les paramètres de canal et de largeur sont fixés et
  le cutoff vérifie 2 radius(max(a,b),L)<=H<=DB. Le terme « enlarged »
  doit conserver ce sens lors d'une réécriture.

Ces points explicitent les objets et hypothèses hérités déjà examinés ;
ils ne sont pas classés comme de nouveaux énoncés originaux faux.
Le [patch de cinq propositions](editorial-proposals/2026-11-07/README.md)
donne une première modification concrète de quatre fichiers TeX, appliquée
uniquement à une copie jetable et conservant les 167 labels.
Une [relecture indépendante du diff](editorial-proposals/2026-11-07/independent-review.json)
a confirmé les cinq thèmes et les quatre empreintes proposées. La précision
sur le second membre nul des événements homogènes y est intégrée ; aucun
PDF n’avait été construit à cette étape initiale. Depuis, les cinq précisions
ont été intégrées et les aperçus compilés et inspectés. Les rapports initiaux
restent figés ; les validations finales décrivent les contrôles postérieurs.

## Simplification et élagage appliqués

Les [treize propositions](editorial-proposals/2026-11-07/integration-status.json)
sont intégrées dans la dernière copie de relecture : 277 lignes source retirées
par rapport au stade clarifié et quatre pages de moins que les PDF v1.8.
Les dernières coupes réemploient le demi-compte de 10.1 pour T1.14 et le résultat
fixe plus fort de 15.5 pour T4.3 ; T4.4 reçoit simultanément une preuve autonome.
Les projections effectives, les sources homogènes incompatibles, le centre
normalisé et la clause à une cible sont explicites. La nouvelle carte de lecture
explique les dépendances en avant, sans cycle avec les reconstructions ou les moments.
Trente déclarations existantes ont été réextraites ; la relecture du diff
et le contrôle visuel des 165 pages sont consignés dans le
[dernier dossier](editorial-proposals/2026-11-07/proof-simplification/README.md).
Les règles à ordre croissant et toute la branche T14–T17 sont conservées.

## Documents à transmettre à une nouvelle instance

Commencer par les deux PDF et les sources de l’[aperçu simplifié](editorial-proposals/2026-11-07/proof-simplification/README.md),
puis cette note, l’index d’intégration et le
[rapport de révision v1.8](MANUSCRIPT_REVISION_V1_8.md). Comparer ensuite aux
versions et aperçus préservés pour distinguer le fond scientifique des coupes.
L’
[index des 167 résultats](MANUSCRIPT_ENDPOINTS_V1_8.md) fournit les
faisceaux exacts, localisateurs, hypothèses et rapports de relecture.
Les journaux de compilation et leurs périmètres sont sous
[validation](validation/manuscript-endpoints-v1.8/README.md).

La relecture par une instance distincte est une aide mathématique et
éditoriale. Elle ne vaut pas revue humaine et ne remplace pas la comparaison
des significations TeX/Lean par l'auteur. Les six soumissions Palomar restent
en attente ; elles reprennent exactement les 17 familles et 68 sélections
antérieures, avec Brice Pouly et son ORCID 0009-0008-8491-2467.
