# Projet d'analyseur statique du cours TAS

## Introduction

Le but du projet est d'implanter un analyseur statique par interprétation abstraite pour un langage "jouet" impératif très simple.
La syntaxe est inspirée de C, mais extrêmement simplifiée : le langage ne comporte que des entiers (mathématiques, non bornés), le *if-then-else* et la boucle *while*.
La langage ne comporte ni pointeur, ni fonction, ni tableau, ni allocation dynamique, ni objet.

Vos trouverez ici un squelette de base pour faciliter le développement de l'analyse :
* un analyseur syntaxique qui transforme le texte du programme en arbre syntaxique abstrait ;
* un interprète par induction sur la syntaxe, paramétré par le choix d'un domaine d'interprétation ;
* des signatures pour les domaines d'environnements et les domaines de valeurs ;
* le domaine concret, permettant de collecter l'ensemble précis des états de programme accessibles ;
* le domaine abstrait des constantes.

L'interprète et le domaine des constantes sont encore incomplets.
Une première tâche sera donc de les compléter.

Le fichier [TRAVAIL.md](TRAVAIL.md) détaille le travail demandé pour le projet.

## Dépendances

Les dépendances suivantes doivent être installées pour pouvoir compiler le projet :
* le langage [OCaml :camel:](https://ocaml.org/index.fr.html) ;
* [Menhir](http://gallium.inria.fr/~fpottier/menhir) : un générateur d'analyseurs syntaxiques pour OCaml ;
* [GMP](https://gmplib.org) : une bibliothèque C d'entiers multiprécision (nécessaire pour Zarith et Apron) ;
* [MPFR](http://www.mpfr.org) : une bibliothèque C de flottants multiprécision (nécessaire pour Apron) ;
* [Zarith](http://github.com/ocaml/Zarith/) : une bibliothèque OCaml d'entiers multiprécision ;
* [CamlIDL](http://github.com/xavierleroy/camlidl/) : une bibliothèque OCaml d'interfaçage avec le C ;
* [Apron](http://apron.cri.ensmp.fr/library) : une bibliothèque C/OCaml de domaines numériques.


### Installation des dépendances sous Ubuntu

Sous Ubuntu (et distributions dérivées), l'installation des dépendances peut se faire avec `apt-get` et [opam](https://opam.ocaml.org/) :
```
sudo apt-get update
sudo apt-get install -y m4 libgmp3-dev libmpfr-dev ocaml ocaml-native-compilers ocaml-findlib opam
opam init -y
opam config -y env
opam install -y menhir zarith mlgmpidl apron
```

### Installation manuelle d'Apron

Si l'installation d'Apron avec `opam` échoue, il est possible de l'installer à la main par :
```
  svn co svn://scm.gforge.inria.fr/svnroot/apron/apron/trunk apron
  cd apron
  ./configure -no-ppl -prefix /usr
  make
  sudo make install
```

## Compilation et test

Après installation des dépendances, faire `make` pour compiler.
L'exécutable généré est `analyzer.byte`.

En cas de succès de la compilation, vous pouvez tester le binaire :
1. `./analyzer.byte tests/01_concrete/0111_rand.c` doit afficher sur la console le texte du programme `tests/01_concrete/0111_rand.c` (en réalité, le programme a été transformé en AST par le *parseur* et reconverti en texte)
2. `./analyzer.byte tests/01_concrete/0111_rand.c -concrete` doit afficher sur la console le résultat de toutes les exécutions possibles du programme de test, ici, le fait que `x` vaut une valeur entre 1 et 5

## Architecture du projet

L’arborescence des sources est la suivante :
* [Makefile](Makefile) : compilation de l’analyseur, à modifier au fur et à mesure que vous ajoutez des sources ;
* [src/main.ml](src/main.ml) : point d’entrée de l'analyseur, à modifier pour ajouter des nouvelles analyses et options ;
* [src/libs/](src/libs) : contient une version légèrement améliorée du module Map d’OCaml ;
* [src/frontend/](src/frontend) : transformation du source (texte) en arbre syntaxique ;
* [src/frontend/abstract_syntax_tree.ml](src/frontend/abstract_syntax_tree.ml) : type des arbres syntaxiques abstraits (AST) ;
* [src/frontend/lexer.mll](src/frontend/lexer.mll) : analyseur lexical OCamlLex ;
* [src/frontend/parser.mly](src/frontend/parser.mly) : analyseur syntaxique Menhir ;
* [src/frontend/file_parser.ml](src/frontend/file_parser.ml) : point d’entrée pour la transformation du source en AST ;
* [src/frontend/abstract_syntax_printer.ml](src/frontend/abstract_syntax_printer.ml) : affichage d’un AST sous forme de sources ;
* [src/domains/](src/domains) : domaines d’interprétation de la sémantique ;
* [src/domains/domain.ml](src/domains/domain.ml) : signature des domaines représentant des ensembles d’environnements ;
* [src/domains/concrete_domain.ml](src/domains/concrete_domain.ml) : domaine concret de la sémantique collectrice ;
* [src/domains/value_domain.ml](src/domains/value_domain.ml) : signature des domaines représentant des ensembles d’entiers ;
* [src/domains/constant_domain.ml](src/domains/constant_domain.ml) : exemple de domaine d’ensembles d’entiers, le domaine des constantes ;
* [src/domains/non_relational_domain.ml](src/domains/non_relational_domain.ml) : foncteur qui crée un domaine d'environnements en associant à chaque variable une valeur de domaine d'entier ;
* [src/interpreter/interpreter.ml](src/interpreter/interpreter.ml) : interprète générique des programmes paramétré par un domaine d’environnements ;
* [tests/](tests) : ensemble de programmes dans le langage analysé pour tester votre analyseur.

## Langage

Nous décrivons succinctement les traits du langage d'entrée de l'analyseur :
* les tests :

```
if (bexpr) { block }
if (bexpr) { block } else { block }
```

* les boucles :

```
while (bexpr) { block }
```

* les affectations :

```
var = expr
```

* l'affichage de la valeur des variables précisées :

```
print(var1,...,varn)
```

* l'affichage de l'environnement complet (toutes les variables) :

```
print_all
```

* l'arrêt du programme :

```
halt
```

* les assertions, qui arrêtent le programme sur un message d’erreur si la condition booléenne n'est pas vérifiée :

```
assert(bexpr)
```

* les expressions entières `expr` sont composées des opérateurs classiques `+`, `-`, `*`, `/`, des variables, des constantes, plus une opération particulière, `rand (l,h)`, où l et h sont deux entiers, et qui représente l’ensemble des entiers entre l et h ;
* les expressions booléennes `bexpr` utilisées dans les tests et les boucles, sont composées des opérateurs `&&`, `||`, `!`, des constantes `true` et `false`, et de la comparaison de deux expressions entières grâce aux opérateurs `<`, `<=`, `>`, `>=`, `==`, `!=` ;
* les blocs sont composés d’une suite de déclarations de variables, suivie d’une suite d’instructions :

```
{ decl1; ...; declN; stat1; ...; statM; }
```

Seul le type `int` est reconnu, et les déclarations n’ont pas d’initialisation (il faut faire suivre d’une affectation).
Une déclaration ne déclare qu'une variable à la fois (`int a; int b;` est possible, mais pas `int a,b;`).
Dans un bloc, toutes les déclarations doivent précéder toutes les instructions.

Un exemple simple de programme valide est :
```
{
  int x;
  x = 2 + 2;
  print(x);
}
```

Pour plus d'informations sur la syntaxe, vous pouvez consulter le fichier d'analyse syntaxique [src/frontend/parser.mly](frontend/parser.mly).
Vous trouverez également des exemples de programmes dans le répertoire [tests/](tests).

## Options de l'analyseur

Quelques options sont disponibles en ligne de commande, à vous d'en ajouter :
1. `-concrete` indique qu'il faut exécuter le programme dans la sémantique concrète collectrice ;
2. `-trace` permet de suivre le déroulement des calculs en affichant l'environnement après l'exécution de chaque instruction.
