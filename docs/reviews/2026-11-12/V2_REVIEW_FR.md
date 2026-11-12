# Relecture et alignement de P1 V2.0

La V2 reçue le 12 novembre 2026 est cohérente avec les estimations nécessaires
à son nouveau périmètre, après ajout des interfaces Lean décrites ci-dessous.
La comparaison des changements examinés n'a révélé aucune nouvelle erreur
nécessitant de modifier un énoncé mathématique de la V2. Ce constat est une
relecture assistée par IA et un contrôle des preuves formelles ; la traduction
du texte en énoncés Lean n'est pas elle-même un théorème du noyau.

## Ce qui devient la version courante

L'archive du 9 novembre est conservée intégralement, avec ses 55 fichiers,
ses rapports chronologiques et ses PDF d'origine. Son SHA-256 est
`60a6a2557750ee96e280714d826bbcaf60e430f9a234e04c9e01124a7f30012d`.
Les 54 empreintes internes ont été vérifiées à réception. Les scripts joints
n'ont pas servi d'instructions à l'agent ; la reconstruction utilise un
programme du dépôt, sans exécution de commandes depuis TeX.

Le nouveau périmètre contient **118 résultats : 26 dans l'article et 92 dans
le compagnon**. Il conserve 117 identités antérieures, ajoute le lemme 2.3 et
retire 50 résultats du périmètre consacré au compte scalaire. Ces 50 résultats
ne sont pas déclarés faux : leurs preuves, sources et index historiques sont
conservés. Par rapport au dernier aperçu unifié, 107 blocs d'énoncés conservés
sont identiques et dix ont changé. La nouvelle numérotation a été comparée
aux références produites par LaTeX, pas seulement au tableau fourni.

Les sources actives reproduisent la V2 reçue, à une exception documentaire :
`formalization.tex` décrit désormais l'alignement effectivement réalisé.
Aucun énoncé scientifique reçu n'a été modifié dans cette session. Les deux
PDF recompilés restent à **32 et 84 pages**, soit 116 pages contre 165 dans
l'ancien aperçu. Cette réduction de 49 pages inclut un changement de périmètre ;
elle ne constitue pas seulement une coupe stylistique à résultats constants.

## Raccords mathématiques contrôlés

| Résultat V2 | Point vérifié | Preuve ou interface courante |
|---|---|---|
| Lemme 2.3 | Factorisation exacte ; domination de trois poids, même avec marges nulles ; facteur `2^|I|` explicite | `V2HomogeneousEnvelope.finite_domination`, `uniform_nominal_comparison` |
| T1.12 | Puissance 41/30 dans les deux canaux bruts ; constante commune des paires choisie avant la marge | `V2FixedHomogeneousSeeds.companion_T1_12` |
| T4.7 | Puissance `r/2` pour trois masses de listes ordonnées ; coût `r!` à ordre fixé | `SharpOrderedPrimitiveMass.companion_T4_7` |
| T10.5 | Cibles arbitraires dans `I_N` ; somme des coûts positifs exact et nominal ; positivité de la masse source avant division | `AllTargetGoodEdgePalm.companion_T10_5`, `principal_channels` |
| T12.4 | Un seuil pour les quatre poids, le compte dense et toutes les sous-familles ; fenêtres irrégulières incluses | `FixedArityHomogeneousMass.uniform_all_bounds` |
| T12.7 | Puissance pure `N^-a`, `a<2` ; coupure fixée avant toute marge ultérieure ; un seul poids nominal pour le bloc comprimé | `FixedCutoffIndependentTail.uniform_tail` |
| T13.1 | Seuil avant tous `s` et `G` ; somme ordonnée divisée par `r!` ; puissance `min(s/2,2)` avec marge | `UniformFullSupportCount.companion_T13_1` |

Ces raccords réutilisent les estimations géométriques déjà établies. Les
24 nouvelles propositions sont des preuves de comparaison, de composition
ou d'uniformité, réparties dans six modules mathématiques. Elles n'équivalent
pas à 24 corrections du papier. Les cinq nouvelles entrées du journal
P1-MATH-1006 à 1010 précisent leur nature et leur origine.

Deux risques d'indexation ont aussi été traités : le seuil local de T8.9
utilise le théorème donnant `5m`, et la clause à une cible de T4.8 utilise
la borne `41/30`. Leurs anciennes interfaces plus faibles restent vraies,
mais ne suffisent pas seules à justifier les formes renforcées du texte.
L'index actuel reprend également les autres renforcements déjà intégrés
dans l'aperçu unifié, au lieu de revenir aux seuls anciens noms canoniques.

## Distinctions à conserver dans les prochaines révisions

- Le théorème 5.2 est un principe de transfert **conditionnel comme imprimé** :
  son hypothèse porte sur les 254 ordres fixes de 3 à 256. Sa preuve est complète
  avec cette hypothèse explicite ; la conclusion principale du papier possède
  séparément une preuve inconditionnelle.
- La nullité relative effective, la nullité brute et la nullité maximale
  compatible ne sont pas interchangeables. Le changement de notation vers
  `rho_*` ne change pas leur définition.
- Dans T10.5, le coût exact est centré en `p_z`, le coût nominal en `p`.
  Le premier se compare à une masse homogène positive sans diviser par `p_z` ;
  le recentrage du second ajoute la masse source multipliée par l'erreur
  absolue totale des marges. Le seuil commun `24B` suffit aux deux canaux
  principaux. Aucune optimalité ni borne de discrepancy absolue n'est ajoutée.
- L'absorption de `2^r` ou de `r!` exige un ordre fixé. T13.1 et la queue
  indépendante ont des preuves uniformes distinctes ; la borne limite pure
  `N^-2` n'est pas affirmée.
- La construction des hôtes primitifs denses précède leur pondération.
  La réutilisation par T12.4 et T4.7 conserve l'indépendance de la preuve
  des moments fixes vis-à-vis de la reconstruction de la loi.

## Simplifications proposées

**S01, option prête à relire :** remplacer la fin de la preuve de T13.1,
qui distingue `s=2`, `s=3`, `4<=s<R` et `s>=R`, par une seule comparaison
`r/2 >= min(s/2,2)` pour les couches présentes. La queue satisfait déjà la
même majoration. Le seuil est toujours le maximum d'un nombre fini de seuils,
pris avant `s,G`. Le patch joint retire deux lignes physiques ; il ne change
aucun énoncé ni aucune étiquette et correspond à l'organisation de la preuve
Lean. Cette option n'est pas appliquée aux sources actives et aucun gain de
page n'est revendiqué.

**S02, option éditoriale :** garder la notice complète de formalisation dans
l'article et la remplacer dans le compagnon par un renvoi de deux ou trois
phrases. Cela économiserait une répétition documentaire sans toucher aux
arguments. La notice commune actuelle conserve néanmoins l'avantage de
rendre chaque PDF compréhensible séparément ; aucune coupe n'est appliquée.

Il paraît préférable de conserver les courtes explications des marges exactes,
des contacts à distance `L`, de la positivité avant division et de la différence
entre ordre fixé et queue uniforme. Les supprimer ferait gagner peu de place
et rendrait les hypothèses plus difficiles à suivre. Aucune nouvelle coupe de
résultats n'est nécessaire pour réaliser l'alignement demandé.

## Validation et suite

Le replay au commit de preuve
`aa12e797ce895f6b7aef6e4f1f0c6e5e9a58aab4` a réussi : 18 645 tâches de
construction, audit des 20 019 théorèmes et vérification de 19 942 références,
avec codes de sortie effectifs nuls. Seuls les axiomes usuels `propext`,
`Classical.choice` et `Quot.sound` apparaissent. La compilation utilise
Lean v4.36.0-rc2 et Mathlib `9d581dfff2e41de989072ea63abf3daf69311520`.

Les 118 résultats correspondent à 199 interfaces de clauses ; neuf affirmations
auxiliaires conservées portent le total contrôlé à 212 propositions distinctes.
Les 24 nouvelles propositions ont aussi leur extraction séparée. Les anciens
inventaires de 528, 539 et 264 types, les neuf exemples, les sept interfaces
d'arité fixée et les quatre interfaces Palm antérieures ont été rejoués avec
des types strictement identiques. Les 547 anciens fichiers de manuscrits et
les anciens modules mathématiques restent inchangés.

Les six exécutions LaTeX ont réussi avec références stabilisées et sans boîte
débordante ni référence non résolue. Les 116 pages ont été inspectées dans dix
planches, et onze pages sensibles individuellement. Les reçus, journaux et
images inspectées sont conservés dans `docs/validation/v2.0`.

Les contrôles locaux du dépôt et les 75 tests automatisés ont réussi. Les
18 contrôles propres à la V2 comprennent 17 cas volontairement invalides
(affaiblissement des domaines, perte de clauses, ordre des quantificateurs,
poids ou facteurs incorrects), tous rejetés.

Les **six dossiers Palomar historiques restent suspendus**, avec le nom et
l'ORCID de Brice Pouly conservés. Leur qualification antérieure ne qualifie
pas automatiquement les nouveaux énoncés V2. La reprise de ce travail devra
comparer ces six périmètres historiques à la V2 et actualiser les sélections
avant tout contrôle officiel ou dépôt. Aucune soumission n'a été effectuée.
