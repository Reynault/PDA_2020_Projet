% ----------------------------------------------------
% TP - PDA - Groupe : Brandon Hornbeck, Reynault Sies
% ----------------------------------------------------

% ----------------------------------------------------
% Configuration - Débuggage
% ----------------------------------------------------

cls :- write('\e[H\e[2J').

set_echo :- assert(echo_on).
clr_echo :- retractall(echo_on).
echo(T) :- echo_on, !, write(T).
echo(_).

:- set_echo.

% ----------------------------------------------------
% Paramètres utilisés:
%
%   - tree  : Tableau qui correspond aux branches réalisées 
%     C'est un tableau qui contient l'arbre sous la forme de formules et de tableaux.
%     Sachant que lorsqu'un conflit est détécté, le premier élément du tableau correspondant
%     à la branche est la constante conflict. 
%     Avec le tableau principal qui correspond à la branche principale.
%
%   - Form      : Une formule du système 
%     (une formule simple)
%
%   - Marked    : Formules déjà développées
%
% Notation utilisée:
%   - conflict : constante qui tagge si une branche a un conflit
% ----------------------------------------------------

% ----------------------------------------------------
% Définition des éléments de la logique propositionnelle
% ----------------------------------------------------

:- op(20,xfy,&)   . % and
:- op(20,xfy,v)   . % or
:- op(20,fx ,not) . % not
:- op(20,xfy,=>)  . % implication
:- op(20,xfy,<=>) . % equality

% ----------------------------------------------------
% Implantation de la méthode pour le calcul propositionnel
% ----------------------------------------------------

% ----------------------------------------------------
% Prédicats rules: Permet de vérifier quelle règle appliquer
% à la formule
% ----------------------------------------------------

rule(Form, or).
rule(Form, nor).

rule(Form, and).
rule(Form, nand).

rule(Form, imp).
rule(Form, nimp).

% ----------------------------------------------------
% Prédicats apply: Permet d'appliquer une règle sur une formule
% ----------------------------------------------------

apply(Form, Branch, or).
apply(Form, Branch, nor).

apply(Form, Branch, and).
apply(Form, Branch, nand).

apply(Form, Branch, imp).
apply(Form, Branch, nimp).

% ----------------------------------------------------
% Prédicats utilitaires
% ----------------------------------------------------

% Prédicat de copie
copy([], []).
copy([H| L], [H| N]) :- copy(L, N).

% Prédicat de vérification de l'existance d'un conflit dans une branche
conflict_exists([conflict | _]).

% ----------------------------------------------------
% Prédicats solve: Permet de lancer l'algorithme des tableaux sémantiques
% ----------------------------------------------------

solve(Tree, Type) :- set_echo,
    loop(Tree, [], Type), !.

loop(Tree, Marked, propositional) :-
    check_tree(Tree),
    conflict_exists(Tree).

loop(Tree, Marked, propositional) :-
    get_form(Tree, Marked, Form, Rule, propositional), !,
    get_branch(Tree, Form, Branch),
    apply(Form, Branch, Rule),
    mark_Form(Form, Marked).

% ----------------------------------------------------
% Prédicats qui permettent la fermeture des branches avec conflit
% ----------------------------------------------------

check_tree([First | Others]) :-
    \+is_list(First),
    check_branches(Others, First),
    check_tree(Others),
    .

check_tree([First | Others]) :-
    is_list(First),
    First = [First_Branch, Others_Branches],
    check_tree(First_Branch),
    check_tree(Others_Branches).

check_branches(Branches, Form):-
    .

close_branche(Branch, New_Branch) :-
    New_Branch = [conflict, Branch].
