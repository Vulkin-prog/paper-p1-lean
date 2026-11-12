# Avis sur le dossier de publication P1

12 novembre 2026. Comparaison au dépôt `a1c8092f7e25acf7f3b78283039cfbd69491f88e`.

Cette livraison est plus aboutie pour une publication. Les deux tableaux
nouveaux rendent lisibles les niveaux de précision et les dépendances des
preuves. La bibliographie distingue mieux les références classiques et
l'apport arithmétique propre au modèle. Le raccord de T7.1 est plus convaincant
que le renvoi précédent à un résultat réservé aux triples primitifs.

La comparaison directe trouve **118 résultats : 26 principaux et 92 dans le
compagnon**. Les 117 autres blocs d'énoncés sont identiques à la version du
dépôt ; T4.3 précise une portée déjà respectée par Lean. Les 26 énoncés
principaux sont tous identiques. Les taux centraux et les régimes d'uniformité
restent ceux déjà formalisés.

## Points mathématiques examinés

**T4.3 : une clarification utile.** Le nouveau texte réserve la petite masse
des familles comportant un défaut ou un contact aux événements originaux.
Les sommes conditionnelles et la propagation admettent les prescriptions
homogènes. `FixedSourcePropagationTheorem.main_6_3` distingue exactement ces
domaines : ses deux premières clauses portent sur des prescriptions arbitraires,
sa dernière sur `infiniteFamilyJointMoment`. Le cas r=s est déjà inclus dans
la preuve formelle par k=0. Le texte reçu traite désormais ce cas avant de
diviser la marge par r-s. Ce changement ne demande aucun nouveau théorème Lean.

**T7.1 : le bon témoin géométrique.** La preuve écrite appelle maintenant le
témoin ancré sur le même espace physique M pour chacun des trois centres.
La condition de récupération est utilisée avant l'effacement final, sans
énumération des sous-espaces ni des historiques d'effacement. C'est la route
de `NearPrimitiveTripleHosts.uniform_hosts`, via la régularisation physique
et `DensePhysicalKernelWitness.uniform_witness_active`, plutôt qu'un appel
supposant la primitivité. Avec theta<eta/100, le coefficient
7 eta/8-9 theta est supérieur à 0,785 eta ; la perte constante 12 est absorbée
pour L assez grand, avant le choix des centres. La réservation d'une moitié
de la marge pour le poids homogène est cohérente.

**T12.4 : la dépendance annoncée correspond à la preuve.** Le nouveau texte
sépare T12.3, auxiliaire, de la construction des hôtes primitifs denses et
du demi-comptage conditionnel qui donnent T12.4. Il correspond au raccord
`FixedArityHomogeneousMass.uniform_all_bounds`. Les quantificateurs gardent
l'arité fixée avant le seuil ; le facteur 2^r n'est pas absorbé à arité croissante.

**L'exemple 10:12:15 est bien cadré.** Pour L=30m, la formule des quatre parties
entières donne 19m-2. Avec N=2^L, le poids vaut N^(-71/30)/4. Le nombre de
translations et la formule centrée donnent le coefficient 1/120 pour cette
sous-famille dans K3+. Le calcul figurait déjà dans la preuve du compagnon ;
son développement dans l'article est pédagogique. Il ne fournit pas un
équivalent complet du cumulant. Le texte fait cette distinction explicitement.

Le tableau initial distingue correctement l'équivalent de Poisson, la puissance
optimale 4/3 de la référence quadratique exacte, les hauteurs h fixées et la
seule borne supérieure annoncée pour la référence de Hermite exacte.

## Bibliographie et attribution

Les vérifications ciblées sont consignées dans
[le relevé des références](../../validation/publication-2026-11-12/bibliography-review.json).
Ce contrôle des ajouts ne constitue pas un audit exhaustif de priorité.

La référence quadratique est bien explicite dans le théorème 1, page 588,
de [Barbour et Eagleson](https://user.math.uzh.ch/barbour/pub/Barbour/BEagleson_ImprovedPoisson.pdf).
Le texte situe donc mieux l'apport propre au papier : paramètres arithmétiques,
contrôle uniforme et non-annulation du reste.

La minoration de [Čekanavičius et Vellaisamy, théorème 2.1, (2.3)](https://www.math.uni.wroc.pl/~pms/files_doi/f1648/f1648.pdf)
contient bien un carré du deuxième cumulant factoriel, avec des hypothèses
de dépendance locale et un terme de reste. Elle sert ici de contexte ; elle
n'est pas une preuve transférée au modèle multiplicatif.

La comparaison avec [Basak, Nath et Zaharescu](https://doi.org/10.1093/imrn/rnad168)
respecte leurs blocs disjoints, l'exception sur les premiers et la longueur
limitée par quatre logarithmes itérés. Le texte auteur a été consulté depuis
[la page de Nath](https://sites.google.com/view/kunjakanannath/research).

Le rapprochement avec [Shparlinski et Sleiman](https://arxiv.org/html/2609.29408v1)
est justifié par les résultants et les bornes uniformes en degré. Le contrôle
d'un espace entier de relations et des fibres de la grille reste distingué.

[Binyamini, Cluckers et Kato, corollaire 8, (23)](https://arxiv.org/html/2401.03982)
donne la borne affine citée pour les courbes sur Q, avec un exposant logarithmique
existentiel. La valeur 17 reste attribuée à la déclaration Lean précise, et
non présentée comme une valeur imprimée dans cet énoncé externe.

Le contexte des produits carrés à nombre fixé de facteurs est correctement
distingué des estimations uniformes utilisées ici ; voir
[de la Bretèche, Kurlberg et Shparlinski](https://kurlberg.github.io/eprints/SquareProduct.pdf).
Les bornes finies du [texte auteur de Mod-discrete expansions](https://people.math.ethz.ch/~kowalski/mod-discrete.pdf),
théorème 5.1, admettent aussi des paramètres de Poisson bornés sous leurs
hypothèses de contrôle du résidu.

Le DOI du papier C correspond à celui annoncé par
[son dépôt auteur](https://github.com/Vulkin-prog/paper-c-lean) ; il est distinct
du DOI de la formalisation. Le résolveur Zenodo n'a pas pu être relu par l'outil
web durant ce contrôle. La notice de Kemp et Kemp est identifiée chez
[l'éditeur](https://academic.oup.com/biomet/article-abstract/52/3-4/381/336471).

## Ajustements appliqués et simplifications possibles

La copie reçue est conservée intégralement. Dans la copie active, seule la
notice de formalisation a été retouchée : lien vers l'index propre à cette
édition, identifiants affichés sur 12 caractères avec liens complets conservés,
et état Palomar explicite. « Identifiants en attente » pouvait laisser croire
à une procédure déjà lancée. Les six dossiers sont en préparation à votre
demande ; aucun cycle officiel n'a commencé.

Je conserverais les deux tableaux, qui compensent leur place par une meilleure
lecture des contributions. Deux allègements restent possibles :

- Le lemme 5.1 peut perdre la borne sur la moyenne et la restriction p*<=1/4 :
  la preuve Lean par produits contractants donne 16 exp(2) sur le domaine
  naturel 0<=p_i<=1. La preuve écrite par série logarithmique devrait alors
  être remplacée par cet argument, puisqu'elle utilise la restriction actuelle.
  Cette simplification déjà signalée n'est pas appliquée au texte reçu.
- T12.3 et sa preuve peuvent être déplacés vers un complément facultatif si
  l'on souhaite resserrer le compagnon sur la preuve principale. L'inventaire
  des renvois ne trouve que sa présentation et sa propre preuve, y compris
  le renvoi à son équation. Son intérêt autonome doit être pesé avant une coupe.
  Aucun gain de pages n'est annoncé sans reconstruire cette variante.

## Portée de la vérification

Un nouveau passage local sous Lean 4.36.0-rc2 a effectivement réussi : compilation
incrémentale de 18 645 tâches, audit de 20 019 théorèmes et extraction de 212 types
de propositions. Ces types sont identiques à ceux du précédent alignement.
Les preuves, les paramètres du compilateur et les dépendances sont conservés.
Les six acceptations par vérificateurs des dossiers précédents sont réutilisées
pour des fichiers mathématiques identiques ; elles ne sont pas présentées comme
une nouvelle campagne de vérification des métadonnées ou comme une certification.

La correspondance texte/Lean et cet avis sont assistés par IA. Le succès de Lean
ne démontre pas une traduction automatique fidèle de chaque phrase des PDF et
ne remplace pas une relecture humaine indépendante.
