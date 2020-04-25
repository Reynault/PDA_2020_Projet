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

rule(Form, A, B, or) :- Form = A v B.
rule(Form, A, B, nor) :- Form = not (A v B).

rule(Form, A, B, and) :- Form = A & B.
rule(Form, A, B, nand) :- Form = not (A & B).

rule(Form, A, B, imp) :- Form = A => B.
rule(Form, A, B, nimp) :- Form = not (A => B).


% ----------------------------------------------------
% Prédicats apply: Permet d'appliquer une règle sur une formule
% ----------------------------------------------------



%cas simples où la branche ne contient pas de sous branche
apply(Form, Branch, New_Branch, or) :- no_sub_branch(Branch), rule(Form, F1, F2, or), append(Branch, [[F1]], Branch_Temp), append(Branch_Temp, [[F2]], New_Branch).
apply(Form, Branch, New_Branch, nor):- no_sub_branch(Branch), rule(Form, F1, F2, nor), append(Branch, [not F1, not F2], New_Branch).

apply(Form, Branch, New_Branch, and):- no_sub_branch(Branch), rule(Form, F1, F2, and), append(Branch, [F1, F2], New_Branch).
apply(Form, Branch, New_Branch, nand):- no_sub_branch(Branch), rule(Form, F1, F2, nand), append(Branch, [[not F1]], Branch_Temp), append(Branch_Temp, [[not F2]], New_Branch).

apply(Form, Branch, New_Branch, imp):- no_sub_branch(Branch), rule(Form, F1, F2, imp), append(Branch, [[not F1]], Branch_Temp), append(Branch_Temp, [[F2]], New_Branch).
apply(Form, Branch, New_Branch, nimp):- no_sub_branch(Branch), rule(Form, F1, F2, nimp), append(Branch, [F1, not F2], New_Branch).

%cas où la branche contient des sous branches
apply(Form, Branch, New_Branch, Rule) :- 
    \+no_sub_branch(Branch), 
    rule(Form, F1, F2, Rule), 
    find_sub_branches(Branch, B1, B2), 
    apply(Form, B1, NB1, Rule), 
    apply(Form, B2, NB2, Rule),
    remove(B1, Branch, Branch_Temp1), remove(B2, Branch_Temp1, Branch_Temp2),
    append(Branch_Temp2, [NB1], Branch_Temp3), append(Branch_Temp3, [NB2], New_Branch).
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
% Prédicat no_sub_branch: rend vrai si la branche n'a pas de sous branche
% ----------------------------------------------------

no_sub_branch([First|Others]) :- \+is_list(First), no_sub_branch(Others).
no_sub_branch([]).

% ----------------------------------------------------
% Prédicat find_sub_branches: rend vrai si B1 et B2 sont les sous Branches de Branch
% ----------------------------------------------------

find_sub_branches([First|Others], B1, B2) :- is_list(First), B1 = First, find_sub_branches(Others, B2).
find_sub_branches([First|Others], B1, B2) :- \+is_list(First), find_sub_branches(Others, B1, B2).


find_sub_branches([First|Others], B2) :- is_list(First), B2 = First.
find_sub_branches([First|Others], B2) :- \+is_list(First), find_sub_branches(Others, B2).



% ----------------------------------------------------
% Prédicats remove:
% ----------------------------------------------------
remove(_, [], []).
remove(X, [X|Others], R1) :- remove(X, Others, R1).
remove(X, [Y|Others], R1) :- X \== Y, length(Others, N), N > 0, remove(X, Others, R2), append([Y], R2, R1).
remove(X, [Y|Others], R1) :- X \== Y, length(Others, 0), R1 = [Y].
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
