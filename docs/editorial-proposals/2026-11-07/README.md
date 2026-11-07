# Proposition de compléments éditoriaux

Le [diff TeX](clarifications-and-finite-examples.patch) rend concrètes cinq
propositions issues de l'examen des interfaces et des exemples vérifiés :

1. définir le noyau formel de T22.7 et donner le cas x=18,L=10 ;
2. illustrer la différence entre masse homogène et marginale originale ;
3. rappeler le H=C_D B hérité dans 15.4 ;
4. exposer le choix du cutoff de 15.8 avant epsilon ;
5. donner le rang exactement égal à dix dans l'exemple N=18,q=3.

Le patch touche quatre fichiers. Il a été appliqué avec succès à une
copie jetable des sources v1.8 ; les 167 labels numérotés sont conservés.
Un seul bloc numéroté change : 15.4, par le rappel de son hypothèse de
contexte. Les autres ajouts sont dans l'exposition ou les preuves.
La [validation](validation.json) lie chaque proposition aux théorèmes
audités, aux empreintes des fichiers d'origine et aux fichiers proposés.

Les sources et PDF actuels n'ont pas été modifiés. Aucun PDF de cette
proposition n'a été construit ni inspecté ; une intégration ultérieure
dans une nouvelle version devra effectuer cette vérification et mettre
à jour les correspondances de sources. Ce document complète la
[note de reprise](../../EDITORIAL_HANDOFF_AFTER_ENDPOINT_REVIEW.md).

Pour examiner le patch, utiliser une copie complète des sources v1.8.
Les chemins du diff sont relatifs à ce répertoire de sources. Le texte
anglais proposé peut être adapté par l'auteur avant une intégration
dans un nouveau répertoire de version. Ne pas réappliquer le patch aux
versions historiques préservées.

Palomar reste en attente. Ces précisions n'ajoutent aucune sélection
aux six dossiers prévus.
