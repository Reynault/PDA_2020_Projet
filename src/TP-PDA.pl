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

% Prédicat d'ajout d'une formule déjà utilisée dans un tableau de formules marquées
mark_Form(Form, Marked, New_Marked) :-
    append(Form, Marked, New_Marked).

% ----------------------------------------------------
% Prédicats solve: Permet de lancer l'algorithme des tableaux sémantiques
% ----------------------------------------------------

solve(Tree, Type) :- set_echo,
    loop(Tree, _, [], _, Type), !.

loop(Tree, ClosedTree, Marked, NewMarked, propositional) :-
    check_tree(Tree, ClosedTree),
    conflict_exists(ClosedTree).

loop(Tree, ClosedTree, Marked, NewMarked, propositional) :-
    get_form(Tree, Marked, Form, Rule, propositional), !,
    get_branch(Tree, Form, Branch),
    apply(Form, Branch, Rule),
    mark_Form(Form, Marked, NewMarked),
    loop(ClosedTree, _, NewMarked, _, Type).

% ----------------------------------------------------
% Prédicats qui permettent la fermeture des branches avec conflit
% ----------------------------------------------------

% Prédicat de parcours de l'arbre

% Cas simple où First est une formule
check_tree([First | Others]) :-
    \+is_list(First),
    check_branches(Others, First),
    check_tree(Others).

% Cas dans lequel First est un tableau
check_tree([First | Others]) :-
    is_list(First),
    First = [First_Branch, Others_Branches],
    check_tree(First_Branch), % Propagation du parcours dans les branches
    check_tree(Others_Branches).

% Prédicat de parcours des branches à la recherche
% de la formule opposée

% Cas simple dans lequel le premier élément est une formule
check_branches([First | Others], Form):- \+is_list(First), First = not Form.
check_branches([First | Others], Form):- \+is_list(First), Form = not First.

% Cas dans lequel le premier élément est un tableau
check_branches([First | Others], Form):-
    is_list(First),
    First = [First_Branch, Others_Branches],
    check_branches(First_Branch, Form), % Propagation de la recherche dans les branches
    check_branches(Others_Branches, Form).

close_branche(Branch, New_Branch) :-
    append([conflict], Branch, New_Branch).
