# Projet d'analyseur statique du cours TAS - Rapport de projet
**[Yannick-Alain Couassi-Blé && Rudy Kruissel]**

**PS : Ce rapport a été écrit depuis le premier jour de developpment jusqu'au rendu final. Cependant certaines fonctionnalités qui n'avaient pas été implanté plus tôt l'ont été fait après (sauf mention contraire). Donc ce rapport est plus un recit qui deroule notre cheminement**

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
    * multiplication 
    Effectuer sur le principe de de la div fournie.
    Si une des opérandes est une constante Z.zero retourner Z.zero 
    sinon faire appliquer le lift a leur multiplication

* Comparaisons 
    * eq
    * geq
    * gt  
    * neq
    
Nous les avons implémenté assez naturelement. Rien de spécial à préciser à ce niveau.
## Domaine des intervalles
L'implémentation du domaine des intervalles à été moins facile. Par exemple : 
* certaines règles qui paraissent intuitives mais qui lorsqu'elles ne sont pas realisées avec les règles d'abstraction données en cours échouent les tests. Un exemple est __(`-∞` * 0 = 0 * `+∞` =0)__ .

* l'operation de division : Nous avons ajouté un test, celui du cours sur la division des intervalles __[5,10]/#[-1,1]__ (page 50/66 cours 9). Celui-ci nous à permis de couvrir plus de cas que prévu dans notre implémentation.

Fonctions implémentées : top, bottom, const, rand, meet, join, subset,is_bottom, print, unary, binary, compare, neg, add, sub, mul, div ,eq, neq, geq, gt, __bwd_unary, bwd_binary__.

 __widen : une premiere approche approximative mais sûre en utilisant l'union. Nous l'implémenterons plus precisement dans l'analyse des bloucles__
## Analyse des boucles
La version fournie étant pas precise nous commencons l'analyse par implementer la fonction d'élargissement dans le domaine des intervalles.
cette implantation suit l'algo decrit dans le cours . (sans modification)

Par contre il a fallu modifier le AST_while en incluant cette fonction mais pas que. en utilisant le retardement avant de faire l'elargissement et en deroulant la boucle.
Suivre exactement ce qui a eté mis dans le cours n'a pas vraiment aidé pour l'implementation mais juste pour avoir la moitié des tests positifs au debut.

Tous les tests passent. 



## Produit réduit
Vue la difficulté de l'implantation de l'analyse des boucles nous avons decidé de faire le produit réduit qui parait plus simple avant de revenir plus tard sur les boucles.

 Nous commencons par créer les 4 fichiers nécessaires :
 * écrire les fonctions du domaine des parités : __parity_domain.ml__

* écrire la réduction des intervalles et des parités : 
    cette etape consiste à implementer la fonction reduce.
    Cette fonction repose sur un algorithme simple mais a été plus difficile que prévu à coder.
    Nous n'avons pas accès au type et bornes des intervalles depuis un module externe. Cependant il a fallu rajouter une fonction __get_value : t->int->int__ dans __value_domain.ml__. Cette fonction a été aussi utile pour connaitre la parité d'un élément.  
* écrire le produit reduit en applicant la reduction sur l'appel des fonctions de chacun des domaines abstraits (Intervalles && parité). Sauf sur le widen car ça limite la convergence.

Enfin on connecte le tout avec un foncteur générique dans le main en ajoutant un nouveau module ParityIntervalAnalysis  
# Extension 
Nous avons decidé d'implementer le domaine des disjonctions d'intervalles.
Nous avons par l'intermediaire de monsieur __[A. Miné]__ qu'il avait une astuce OCaml pour ouvrir les domaines a l'exterieur. Cependant Nous avons pas changé notre strategie dans le produit reduit (pour le temps passé dessus) mais nous le ferons ici . Pour eviter de dupliquer les travaux deja fait dans les intervalles.

Nous avons fais toute les fonction mais n'avons pas eu le temps d'introduire une borne de test pour tester .
