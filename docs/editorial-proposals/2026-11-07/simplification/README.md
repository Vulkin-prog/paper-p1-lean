# Simplification et élagage : première passe vérifiée

Treize propositions sont consignées dans la [relecture indépendante](../../../reviews/2026-11-07/simplification-review.json).
Les huit premières sont appliquées dans un
[aperçu séparé avec ses sources et ses deux PDF](../../../../manuscripts/paper-p1/editorial-condensed-preview-2026-11-07/).
Elles retirent **120 lignes source** : l’article conserve 65 pages et le
compagnon passe de 104 à 103 pages. Le gain mesuré est d’une page au total.

| Coupe appliquée | Simplification | Contenu conservé |
|---|---|---|
| SIM01 | Renvoyer la construction ancrée de 15.5 à T8 | Poids exacts, compte dense, séparation des nullités et ordre fixé |
| SIM02 | Déduire T9.1 de T1.1 | Seuil imprimé et offsets entiers distincts |
| SIM03 | Déduire T9.2 de T1.3 | Uniformité sur les fenêtres critiques ; Chebyshev déplacé intégralement avant Mertens |
| SIM04 | Spécialiser l’argument général pour T8.2 | Hôtes denses, vraie masse homogène et activité centrée globale |
| SIM05 | Appliquer T6.1 au second volet de 15.4 | Coupure fixée et cas limite `q=0` |
| SIM06 | Resserrer l’annonce introductive de deux puissances | Régimes, constantes mobiles et témoin `10:12:15` |
| SIM07 | Raccourcir la seconde carte du compagnon | Dépendances positionnelles et branche T14–T17 |
| SIM08 | Calculer la norme à `mu=1` une seule fois | Constantes `3/e`, `3/(4e)` et `1/(12e)` |

Les 167 blocs numérotés et les 552 occurrences de labels sont inchangés par
ces huit coupes. L’aperçu reprend aussi les cinq clarifications antérieures,
dont le rappel de la coupure dans 15.4 ; il ne remplace aucune version archivée.

Le [diff concret](concise-proofs.patch) s’applique **après** le
[patch de clarification](../clarifications-and-finite-examples.patch).
L’autre instance a relu ses sept fichiers, les raccords et les empreintes :
aucune correction mathématique nécessaire ni lacune confirmée dans cette
[relecture du diff](independent-patch-review.json).
Le parent a ensuite compilé les deux documents en trois passes alternées,
contrôlé les 167 numéros, rendu les 168 pages et inspecté les douze planches
et les 44 pages de détail, sans défaut visuel observé.
Les [résultats et empreintes finales](final-validation.json) distinguent
ces opérations de la relecture assistée par IA et des preuves Lean.

Les cinq autres propositions restent séparées :

- SIM09 : mutualiser la conversion analytique après avoir explicité les
  coefficients réels arbitraires ; conserver la différence entre somme
  des valeurs absolues et valeur absolue de la somme.
- SIM10 : rapprocher les contre-exemples des deux énoncés corrigés et
  alléger le bilan commun, sans supprimer leur contenu scientifique.
- SIM11 : déplacer la table des marges après la reconstruction ; ce
  déplacement améliore le parcours de lecture sans raccourcissement garanti.
- SIM12 : étudier le raccourci de T1.14 par le demi-compte, avec son raccord
  entre projections formelles et effectives et ses dépendances tardives.
- SIM13 : réorganiser T4.3 seulement en conservant une preuve autonome du
  cas comprimé T4.4 ; aucune économie de ses 146 lignes n’est acquise.

Les deux précisions de vocabulaire facultatives du rapport du diff sont
conservées dans le bilan final. Les sources actuelles de l’aperçu restent
exactement celles qui ont été relues et compilées.

Les rapports et validations initiaux sont figés à leur propre étape : leurs
mentions de compilation ou de revue encore en attente décrivent cet instant.
Le bilan final ci-dessus contient les contrôles accomplis ensuite. Les chemins
de travail locaux des rapports sont des localisateurs historiques ; le
manifeste scientifique est aussi publié dans le dossier de l’aperçu, et le
[graphe d’imports cité](../../../reviews/2026-11-07/simplification-import-evidence.json)
est conservé dans les documents de relecture.

La source de preuve est le commit `7bfc953c`, sous Lean 4.36.0-rc2. Ses sept
nouvelles interfaces d’enveloppe commune sont décrites
[séparément](../../../FIXED_ARITY_HOMOGENEOUS_ENVELOPE.md).
Les six dossiers Palomar conservent les 68 sélections initiales ; les
soumissions restent en attente à la demande de l’auteur.
