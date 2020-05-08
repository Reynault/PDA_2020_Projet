% ----------------------------------------------------
% TP - PDA - Groupe : Brandon Hornbeck, Reynault Sies
% ----------------------------------------------------

% Liste des opérateurs permettant de gérer les formules
% de la logique propositionnelle

% ----------------------------------------------------
% Définition des éléments de la logique propositionnelle
% ----------------------------------------------------

:- op(1,fx ,not) . % non
:- op(2,xfy,&)   . % et
:- op(3,xfy,v)   . % ou
:- op(4,xfy,=>)  . % implication

% opérateur indiquant une formule déjà utilisée
:- op(100,fx,marked)  .