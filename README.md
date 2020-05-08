# PDA_2020_Projet

## Sujet de TP - UE M1 PDA - 2019-2020

Le but de ce TP est d'implanter la méthode des tableaux sémantiques
en logique classique, telle qu'elle a été étudiée en cours (méthode
standard avec constantes). Le langage choisi pour cette implantation
est le langage Prolog.

le TP comporte deux parties : l'implantation de la méthode pour le
calcul propositionnel et ensuite l'implantation de la méthode pour le
calcul des prédicats du premier ordre.

## Utilisation du projet

Pour utiliser le code Prolog développé, il faut consulter le fichier main.pl qui contient
toutes les fonctionnalités demandées, à savoir, la méthode des tableaux sémantiques.

Pour la logique propositionnelle, on peut exécuter le programme avec:

```
solve(Tree, propositionnal).
```

Pour la logique du premier ordre, on peut exécuter le programme avec:

```
solve(Tree, Mult, first_order).
```

Avec Tree un arbre de la forme suivante:

```
Tree = [a v b, a => b, ....]
```

Et mult un entier correspondant à la multiplicité.

## Rendu

Le dossier de rendu du TP comportera
- un rapport explicitant les choix principaux de l'implantation pour ces
deux parties et tout autre élément mettant en avant des caractéristiques
du travail réalisé.
- une copie du code Prolog de ces implantations.
- un ensemble de tests à partir d'exemples significatifs illustrant le
travail.

La date limite de remise de ce TP est le lundi 11 mai 2020.
