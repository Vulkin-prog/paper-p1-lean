# Reprise éditoriale après vérification des interfaces

Cette note complète la [relecture initiale](reviews/2026-11-07/RAPPORT_FR.txt)
et les améliorations déjà intégrées à la [version 1.8](MANUSCRIPT_REVISION_V1_8.md).
Elle porte sur les précisions apparues pendant l'examen des 167 faisceaux
de preuves, jusqu'à la source Lean `08f019df4d33a817377e5c937356fe4d87ae08e1`.
Les sources et PDF v1.8 sont conservés. Les textes anglais ci-dessous sont
des propositions pour une révision ultérieure ; ils ne sont pas annoncés
comme déjà intégrés aux PDF.

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
Cette précision n'ajoute aucune sélection Palomar.

## 8. 3.1 et 15.13 : conserver les implications imprimées

Ces deux résultats ont des prémisses mathématiques explicites dans le texte.
En particulier, [15.13](../manuscripts/paper-p1/v1.8/sources/main_sections/exact_transfer.tex#L874)
est un transfert à partir des 254 ordres fixés 3<=r<=256, pour beta fixé
dans 1<beta<=4/3. Sa preuve est une implication complète ; il ne faut pas
la reformuler comme une estimation sans sa prémisse d'activités connexes.
La formalisation conserve exactement cette distinction.

## Documents à transmettre à une nouvelle instance

Commencer par les deux PDF v1.8 et leurs sources, puis cette note et le
[rapport de révision v1.8](MANUSCRIPT_REVISION_V1_8.md), afin de distinguer
ce qui est déjà intégré des propositions restantes. L'
[index des 167 résultats](MANUSCRIPT_ENDPOINTS_V1_8.md) fournit les
faisceaux exacts, localisateurs, hypothèses et rapports de relecture.
Les journaux de compilation et leurs périmètres sont sous
[validation](validation/manuscript-endpoints-v1.8/README.md).

La relecture par une instance distincte est une aide mathématique et
éditoriale. Elle ne vaut pas revue humaine et ne remplace pas la comparaison
des significations TeX/Lean par l'auteur. Les six soumissions Palomar restent
en attente ; elles reprennent exactement les 17 familles et 68 sélections
antérieures, avec Brice Pouly et son ORCID 0009-0008-8491-2467.
