# Projet d'analyseur statique du cours TAS - Rapport de projet

[Yannick-Alain Couassi-Blé && Rudy Kruissel]

#consignes
* les fonctionnalités que vous avez implantées ;
* les tests que vous avez ajoutés ;
* les difficutés éventuelles rencontrées ; en particulier, si certains tests échouent, ou si certaines fonctionnalités demandéees ne fonctionnent pas, vous en expliquerez les raisons ;
* pour l'extension au choix, vous prendrez un soin tout particulier à détailler les extensions de syntaxe et de sémantique, les options ajoutées en ligne de commande et les tests ajoutés.



## Ajout du support des assertions
Principe : On analyse par filtrage sur la condition.
On analyse la condition en supposant l'assertion fausse : 
    si on n'obtient un ensemble non vide alors on affiche un message d'erreur, on renvoie le filtrage de la condition en la supposant vraie afin de continuer l'analyse

*ajout de tests  TODO
 

## Complétion du domaine des constantes

#mul 
let mul a b = 
  (* lift2 Z.mul a b*)
      if b = Cst Z.zero || a=Cst Z.zero then Cst Z.zero 
        else lift2 Z.mul a b 

si une des operandes est une constante Zero retourner 0 sinon lifter a e b 

#eq
let eq a b =
    match a,b with 
    |Cst x , Cst y when x=y -> a,a
    |BOT,Cst x -> b,b
    |Cst x , BOT -> a,a
    |TOP, Cst x -> b,b
    |Cst x , TOP -> a,a
    |_,_ -> a,b 

#geq
  let geq a b =
    match a,b with 
    |Cst x , Cst y -> if x>=y then Cst x , Cst y else BOT,BOT
    |BOT ,Cst x |Cst x,BOT -> a,b
    |_,_ -> a,b 
#gt
  let gt a b =
    match a,b with 
    | Cst x , Cst y -> if x>y then Cst x, Cst y  else BOT,BOT
    | BOT, Cst x | Cst x,BOT -> a,b
    |_,_ -> a,b


#let neq a b =  //done but to verified after
    match a,b with 
    |Cst x , Cst y -> if x!=y then Cst x, Cst y else BOT,BOT
    |BOT ,Cst x |Cst x,BOT -> a,b
    |_,_ -> a,b 


## Domaine des intervalles



### extension 
apron --> deja implementation des polyhedre