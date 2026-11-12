# P1 V2 : six enregistrements pour l’article principal

Le périmètre proposé couvre **les 26 résultats numérotés de l’article principal**,
avec leurs clauses et leurs hypothèses, au moyen de **six dossiers et 52 énoncés
comparés**. Les six dossiers remplacent le précédent découpage ; ils ne s’y
ajoutent pas. Les anciens fichiers et leurs validations restent conservés.

L’ordre conseillé commence par le résultat central du papier :

| Priorité | Dossier | Résultats de l’article | Énoncés comparés |
|---|---|---|---:|
|1|Approximation quadratique optimale et échelles de Poisson|1.1–1.2,7.2–7.4|10|
|2|Cumulants et optimalité|3.3–3.4,6.1–6.2|8|
|3|Profils des paires et hiérarchie des canaux|3.1–3.2,8.1–8.3|13|
|4|Arrêt, conversion et reconstruction de la loi complète|4.1–4.2,5.1–5.3|8|
|5|Positivité quadratique et lois de Hermite|7.1,8.4|5|
|6|Événements affines et enveloppe homogène|2.1–2.5|8|

La [carte détaillée des clauses](../palomar/v3/COVERAGE.md) précise les 26 blocs.
Le [plan vérifiable](../palomar/REGISTRATION_PLAN_V2.json) associe chaque numéro
et chaque étiquette du texte à ses énoncés sélectionnés, aux empreintes des
énoncés et aux preuves du développement principal. Une simple présence parmi
les dépendances d’une preuve ne compte pas comme une sélection directe.

Le compagnon fournit les preuves du développement substantiel. Ce découpage
ne revendique pas la sélection directe de chacun de ses 92 résultats, ni celle
de toute la prose de l’article. L’ensemble de la formalisation V2 conserve son
périmètre de 118 résultats. Les extensions historiques absentes du papier V2
restent présentes dans la bibliothèque.

Les précisions suivantes sont conservées :

- Le transfert 5.2 affiche ses 254 hypothèses, pour les ordres 3 à 256 ; la
  reconstruction 5.3 porte bien sa conclusion inconditionnelle.
- Les vrais paramètres sont utilisés pour l’approximation exacte. Les
  références nominales ont leurs propres erreurs et équivalents.
- Les constantes de comparaison du biais sont choisies avant epsilon. La
  somme entière du biais et l’encadrement de son quantum par des constantes
  fois 1/N sont explicités.
- Les résultats de hauteur finie et les poids polynomiaux fixent leur ordre
  avant le seuil en N. Les cas d’incompatibilité affine et de marge nulle
  restent dans les énoncés qui les admettent.
- L’approximation de Hermite conserve ses trois volets ; aucune borne
  inférieure correspondante n’est annoncée pour sa référence aux paramètres
  exacts.

Ces raccordements portent sur la présentation Lean destinée à Palomar. Ils
n’introduisent pas de nouvelle correction mathématique au papier. Les sources
scientifiques, les PDF, les corrections déjà recensées et les anciennes preuves
sont conservés.

Une simplification éditoriale possible, laissée à votre appréciation pour une
prochaine version, concerne le lemme 5.1 : la [preuve déjà disponible](../PaperP1/Probability/UniversalHeterogeneousConversion.lean#L115)
donne la constante universelle 16 exp(2) pour des marges entre 0 et 1. Les
restrictions supplémentaires sur la moyenne et sur la marge maximale à 1/4
peuvent donc être supprimées dans cet énoncé. Cette proposition est relevée
ici ; le texte scientifique reçu reste conservé.

Chaque dossier inclut **Brice Pouly**, son compte **Vulkin-prog** et son
**ORCID 0009-0008-8491-2467** dans des champs structurés. Leur interprétation
par le validateur officiel de métadonnées est contrôlée localement.

La [validation locale](../palomar/v3/VALIDATION.json) distingue les compilations,
les types effectivement extraits, l’audit des 262 théorèmes d’interface et de
raccordement, les comparaisons exactes et les vérificateurs utilisés localement.
Les 18 contrôles négatifs protègent notamment la couverture, l’ORCID, les
hypothèses conditionnelles, les paramètres et la traçabilité des preuves.

Le contrôle officiel complet Palomar, la soumission, l’avis privé et
l’enregistrement sont des étapes distinctes. Le [lancement préparé](../.github/workflows/palomar-preflight.yml)
choisit un seul dossier et une révision précise. Le protocole demande d’abord
votre déclaration personnelle sur votre qualité d’auteur ou de mainteneur
responsable, ou sur l’accord d’une telle personne. La décision de publier
l’avis privé viendra après sa réception. Un cycle entier doit être terminé ou
clos avant de commencer le suivant.
