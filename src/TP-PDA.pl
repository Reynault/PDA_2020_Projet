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
% Prédicats utilitaires
% ----------------------------------------------------

% Prédicat de copie
copy([], []).
copy([H| L], [H| N]) :- copy(L, N).

% ----------------------------------------------------
% Prédicats qui permettent de parcourir l'arbre et de fermer les branches
% qui contiennent un conflit
% ----------------------------------------------------

% Cas dans lequel on arrive à la fin d'une branche
close_conflicts(TreeBeginning, [], ClosedTree).

close_conflicts(TreeBeginning, [], ClosedTree) :- conflict_exists(TreeBeginning).

% Cas dans lequel on se trouve dans une branche sans sous branches
close_conflicts(TreeBeginning, [First| Others], ClosedTree) :-
    \+is_list(First),
    no_sub_branch(Others),
    check_conflicts(Others, First),
    ClosedTree = [conflict| TreeBeginning].

close_conflicts(TreeBeginning, [First| Others], ClosedTree) :-
    \+is_list(First),
    no_sub_branch(Others),
    \+check_conflicts(Others, First),
    close_conflicts(TreeBeginning, Others, ClosedTree).

% Cas dans lequel on se trouve dans une branche avec sous branches
close_conflicts(TreeBeginning, [First| Others], ClosedTree) :-
    \+is_list(First),
    \+no_sub_branch(Others),
    check_conflicts(Others, First),
    ClosedTree = [conflict| TreeBeginning].

close_conflicts(TreeBeginning, [First| Others], ClosedTree) :-
    \+is_list(First),
    \+no_sub_branch(Others),
    \+check_conflicts(Others, First),
    close_conflicts(TreeBeginning, Others, ClosedTree).

close_conflicts(TreeBeginning, [First| Others], ClosedTree) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    close_conflicts(B1, B1, ClosedB1),
    close_conflicts(B2, B2, ClosedB2),
    append([ClosedB1], [ClosedB2], ClosedTree).

close_conflicts(TreeBeginning, [First| Others], ClosedTree) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    close_conflicts(B1, B1, ClosedTree),
    close_conflicts(B2, B2, ClosedTree).


% check_conflicts permet de vérifier si la branche est à fermer (conflits dans
% toutes les sous-branches)
check_conflicts([First| Others], Form) :-
    \+is_list(First),
    is_conflict([First| Others], Form).

check_conflicts([First| Others], Form) :-
    \+is_list(First),
    \+is_conflict([First| Others], Form),
    close_conflicts(Others, Form).

check_conflicts([First| Others], Form) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    conflict_exists(B1),
    conflict_exists(B2).

check_conflicts([First| Others], Form) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    conflict_exists(B1, Form ),
    \+conflict_exists(B2, Form),
    check_conflicts(B2, Form).

check_conflicts([First| Others], Form) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    \+conflict_exists(B1, Form ),
    check_conflicts(B1, Form),
    conflict_exists(B2, Form).

check_conflicts([First| Others], Form) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    \+conflict_exists(B1, Form),
    check_conflicts(B1, Form ),
    \+conflict_exists(B2, Form),
    check_conflicts(B2, Form).

% is_conflict permet de vérifier si un conflit existe entre deux formules
is_conflict(A, B):- \+is_list(A), A = not B.
is_conflict(A, B):- \+is_list(A), B = not A.

% ----------------------------------------------------
% Prédicat qui permet de vérifier si une branche possède un conflit
% ----------------------------------------------------

conflict_exists([conflict| _]).

% ----------------------------------------------------
% Prédicat de récupération de la formule sur laquelle on veut travailler
% ----------------------------------------------------

get_form(Tree, Marked, Form, Rule, propositional).

% ----------------------------------------------------
% Prédicat d'ajout d'une formule déjà utilisée dans un tableau de formules marquées
% ----------------------------------------------------

get_branch(Tree, Form, Branch).

% ----------------------------------------------------
% Prédicat d'ajout d'une formule déjà utilisée dans un tableau de formules marquées
% ----------------------------------------------------

mark_Form(Form, Marked, New_Marked) :- append(Form, Marked, New_Marked).

% ----------------------------------------------------
% Prédicats solve: Permet de lancer l'algorithme des tableaux sémantiques
% ----------------------------------------------------

solve(Tree, Type) :- set_echo, loop(Tree, _, [], _, Type), !.

loop(Tree, ClosedTree, Marked, NewMarked, propositional) :-
    check_tree(Tree, ClosedTree), conflict_exists(ClosedTree).

loop(Tree, ClosedTree, Marked, NewMarked, propositional) :-
    get_form(Tree, Marked, Form, Rule, propositional), !,
    get_branch(Tree, Form, Branch),
    apply(Form, Branch, Rule),
    mark_Form(Form, Marked, NewMarked),
    loop(ClosedTree, _, NewMarked, _, Type).