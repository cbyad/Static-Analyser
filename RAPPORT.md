# Projet d'analyseur statique du cours TAS - Rapport de projet
**[Yannick-Alain Couassi-Blé && Rudy Kruissel]**

# consignes
* les fonctionnalités que vous avez implantées ;
* les tests que vous avez ajoutés ;
* les difficutés éventuelles rencontrées ; en particulier, si certains tests échouent, ou si certaines fonctionnalités demandéees ne fonctionnent pas, vous en expliquerez les raisons ;
* pour l'extension au choix, vous prendrez un soin tout particulier à détailler les extensions de syntaxe et de sémantique, les options ajoutées en ligne de commande et les tests ajoutés.

## Ajout du support des assertions
Principe : On analyse par filtrage sur la condition.
On analyse la condition en supposant l'assertion fausse : 
    si on obtient un ensemble non vide alors on affiche un message d'erreur, on renvoie le filtrage de la condition en la supposant vraie afin de continuer l'analyse.

## Complétion du domaine des constantes
* Opérations arithmétiques
** multiplication 
Effectuer sur le principe de de la div fournie.
Si une des opérandes est une constante Z.zero retourner Z.zero 
sinon faire lifter leur multiplication
__lifter :__ passer du monde des entiers vers notre type t 

* Comparaisons 
** eq
** geq
** gt  
** neq
Nous les avons implémenté assez naturelement. Rien de spécial à préciser à ce niveau.
## Domaine des intervalles
L'implémentation du domaine des intervalles à été moins facile surtout sur certaines règles qui paraissent intuitives mais qui lorsqu'elles ne sont pas realisées avec les règles d'abstraction données dans en cours echouent les tests. Un exemple est __(`-∞`*0 = 0*`+∞`=0)__ 

Fonctions implémentées : top, bottom, const, rand, meet, join, subset
is_bottom, print, unary, binary, compare, neg, add, sub, mul, div 
__widen__ une premiere approche approximative mais sûre en utilisant l'union.
Nous l'implementerons plus precisement dans le domaines des bloucles
eq, neq, geq, gt
bwd_unary, __bwd_binary__ // a terminer 

## Analyse des boucles
La version fournie etant pas precise nous commencons l'analyse par implementer la fonction d'elargissement dans le domaine des intervalles.

## Produit réduit
Vue la difficulté de l'implantation de l'analyse des boucles nous avons decidé de faire le produit reduit qui parait plus simple avant de revenir plus tard sur les boucles.

* Nous commencons par créer les 4 fichiers necessaires et ecrire le domaine des parité

* ecrire la reduction des des intervals et des parité

Enfin on connecte le tout dans le main en ajoutant un nouveau module ParityIntervalAnalysis  



### extension 
apron --> deja implementation des polyhedre