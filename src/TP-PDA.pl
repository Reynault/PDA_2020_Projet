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

:- op(1,fx ,not) . % not
:- op(2,xfy,&)   . % and
:- op(3,xfy,v)   . % or
:- op(4,xfy,=>)  . % implication
:- op(5,xfy,<=>) . % equality

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
    rule(Form, _, _, Rule), 
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


find_sub_branches([First|_], B2) :- is_list(First), B2 = First.
find_sub_branches([First|Others], B2) :- \+is_list(First), find_sub_branches(Others, B2).

% ----------------------------------------------------
% Prédicat close_main_branch: détècte s'il y a un conflit dans deux branches données en paramètres, si c'est le cas,
% ferme la branche
% ----------------------------------------------------

close_main_branch(MainBranch, B1, B2, NewMainBranch) :- 
    conflict_exists(B1), 
    conflict_exists(B2), 
    append([conflict], MainBranch, NewMainBranch).
close_main_branch(MainBranch, _, _, NewMainBranch) :- NewMainBranch = MainBranch.

% ----------------------------------------------------
% Prédicat get_before_sub_branches: rend vrai si B1 et B2 sont les sous Branches de Branch
% ----------------------------------------------------

get_before_sub_branches([First| _], BeforeBranches) :- 
    is_list(First),
    BeforeBranches = [].

get_before_sub_branches([First| Others], BeforeBranches) :- 
    \+is_list(First),
    get_before_sub_branches(Others, B),
    append([First], B, BeforeBranches).

% ----------------------------------------------------
% Prédicat get_position_in_tree: récupère la position de Form dans l'arbre donné
% ----------------------------------------------------

get_position_in_tree([First| Others], Form, Position) :-
    Form == First,
    Position = [First| Others].

get_position_in_tree([First| Others], Form, Position) :-
    \+Form == First,
    get_position_in_tree(Others, Form, Position).

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

% Prédicat de vérification si une liste est vide
isEmpty([]).

% ----------------------------------------------------
% Prédicats qui permettent de parcourir l'arbre et de fermer les branches
% qui contiennent un conflit
% ----------------------------------------------------

% Cas dans lequel on arrive à la fin d'une branche
close_conflicts(TreeBeginning, [], ClosedTree) :- 
    ClosedTree = TreeBeginning,
    echo("end").

close_conflicts(TreeBeginning, _, ClosedTree) :- 
    conflict_exists(TreeBeginning),
    ClosedTree = TreeBeginning,
    echo("conflict").

% Cas dans lequel on se trouve dans une branche sans sous branches
close_conflicts(TreeBeginning, [First| Others], ClosedTree) :-
    \+is_list(First),
    no_sub_branch(Others),
    check_conflicts(Others, First),
    ClosedTree = [conflict| TreeBeginning],
    echo("1").

close_conflicts(TreeBeginning, [First| Others], ClosedTree) :-
    \+is_list(First),
    no_sub_branch(Others),
    \+check_conflicts(Others, First),
    close_conflicts(TreeBeginning, Others, ClosedTree), !,
    echo("2").

% Cas dans lequel on se trouve dans une branche avec sous branches
close_conflicts(TreeBeginning, [First| Others], ClosedTree) :-
    \+is_list(First),
    \+no_sub_branch(Others),
    check_conflicts(Others, First),
    ClosedTree = [conflict| TreeBeginning],
    echo("3").

close_conflicts(TreeBeginning, [First| Others], ClosedTree) :-
    \+is_list(First),
    \+no_sub_branch(Others),
    \+check_conflicts(Others, First),
    find_sub_branches([First| Others], B1, B2),
    check_conflicts(B1, First),
    \+conflict_exists(B1),
    append([conflict], B1, ClosedB1),

    get_before_sub_branches(TreeBeginning, BeforeBranches),
    append(BeforeBranches, [ClosedB1], B),
    append(B, [B2], TreePartiallyClosed),

    get_position_in_tree(TreePartiallyClosed, First, [_| O]),
    close_conflicts(TreePartiallyClosed, O, ClosedTree), !,
    echo("4").

close_conflicts(TreeBeginning, [First| Others], ClosedTree) :-
    \+is_list(First),
    \+no_sub_branch(Others),
    \+check_conflicts(Others, First),
    find_sub_branches([First| Others], B1, B2),
    check_conflicts(B2, First),
    \+conflict_exists(B2),
    append([conflict], B2, ClosedB2),

    get_before_sub_branches(TreeBeginning, BeforeBranches),
    append(BeforeBranches, [B1], B),
    append(B, [ClosedB2], TreePartiallyClosed),

    get_position_in_tree(TreePartiallyClosed, First, [_| O]),
    close_conflicts(TreePartiallyClosed, O, ClosedTree), !,
    echo("5").

close_conflicts(TreeBeginning, [First| Others], ClosedTree) :-
    \+is_list(First),
    \+no_sub_branch(Others),
    \+check_conflicts(Others, First),
    find_sub_branches([First| Others], B1, B2),
    \+check_conflicts(B1, First),
    \+check_conflicts(B2, First),
    close_conflicts(TreeBeginning, Others, ClosedTree), !,
    echo("6").

close_conflicts(TreeBeginning, [First| Others], ClosedTree) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    close_conflicts(B1, B1, ClosedB1), !,
    close_conflicts(B2, B2, ClosedB2), !,

    echo(TreeBeginning),
    close_main_branch(TreeBeginning, ClosedB1, ClosedB2, NewTree),
    get_before_sub_branches(NewTree, BeforeBranches),
    append([ClosedB1], [ClosedB2], C),
    append(BeforeBranches, C, ClosedTree),
    echo("7").

% check_conflicts permet de vérifier si la branche est à fermer (conflits dans
% toutes les sous-branches)
check_conflicts([First| _], Form) :-
    \+is_list(First),
    is_conflict(First, Form).

check_conflicts([First| Others], Form) :-
    \+is_list(First),
    \+is_conflict(First, Form),
    check_conflicts(Others, Form).

check_conflicts([First| Others], _) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    conflict_exists(B1),
    conflict_exists(B2).

check_conflicts([First| Others], Form) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    conflict_exists(B1),
    \+conflict_exists(B2),
    check_conflicts(B2, Form).

check_conflicts([First| Others], Form) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    \+conflict_exists(B1),
    check_conflicts(B1, Form),
    conflict_exists(B2).

check_conflicts([First| Others], Form) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    \+conflict_exists(B1),
    check_conflicts(B1, Form ),
    \+conflict_exists(B2),
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

get_form([First| _], TreeBeginning, Marked, Form, Branch, Rule, propositional) :-
    \+is_list(First),
    \+member(First, Marked),
    First \= conflict,
    Branch = TreeBeginning,
    Form = First,
    rule(Form, _, _, Rule).

get_form([First| Others], TreeBeginning, Marked, Form, Branch, Rule, propositional) :-
    \+is_list(First),
    member(First, Marked),
    get_form(Others, TreeBeginning, Marked, Form, Branch, Rule, propositional), !.

get_form([First| Others], _, Marked, Form, Branch, Rule, propositional) :-
    is_list(First),
    find_sub_branches([First| Others], B1, _),
    \+conflict_exists(B1),
    get_form(B1, B1, Marked, Form, Branch, Rule, propositional), !.

get_form([First| Others], _, Marked, Form, Branch, Rule, propositional) :-
    is_list(First),
    find_sub_branches([First| Others], _, B2),
    \+conflict_exists(B2),
    get_form(B2, B2, Marked, Form, Branch, Rule, propositional), !.

% ----------------------------------------------------
% Prédicat d'ajout d'une formule déjà utilisée dans un tableau de formules marquées
% ----------------------------------------------------

mark_Form(Form, Marked, New_Marked) :- append(Form, Marked, New_Marked).

% ----------------------------------------------------
% Prédicats solve: Permet de lancer l'algorithme des tableaux sémantiques
% ----------------------------------------------------

solve(Tree) :- set_echo,
    close_conflicts(Tree, Tree, ClosedTree), !,
    loop(ClosedTree, _, [], _, propositional), !.

% ----------------------------------------------------
% Prédicats loop pour la logique propositionnelle
% ----------------------------------------------------

loop(Tree, _, _, _, _) :- conflict_exists(Tree).

loop(Tree, ClosedTree, Marked, NewMarked, propositional) :-
    get_form(ClosedTree, ClosedTree, Marked, Form, Branch, Rule, propositional), !,
    apply(Form, Branch, Rule),
    mark_Form(Form, Marked, NewMarked),
    close_conflicts(Tree, Tree, ClosedTree), !,
    loop(ClosedTree, _, NewMarked, _, propositional), !.

% ----------------------------------------------------
% Prédicats display_tree : prédicat d'affichage de l'arbre
% ----------------------------------------------------

display_tree(Tree) :- display_tree(Tree, "").

display_tree([], _).

display_tree([First| Others], _) :-
    no_sub_branch([First| Others]),
    isEmpty(Others),
    echo(First).

display_tree([First| Others], _) :-
    no_sub_branch([First| Others]),
    \+isEmpty(Others),
    echo(First),
    echo(" --- "),
    display_tree(Others).

display_tree(Tree, Offset) :-
    \+no_sub_branch(Tree),
    get_before_sub_branches(Tree, BeforeBranches),
    display_tree(BeforeBranches),
    find_sub_branches(Tree, B1, B2),
    string_concat(Offset, "        ", NewOffset),
    echo("\n"),
    echo(NewOffset),
    echo(" --- "),
    display_tree(B1, NewOffset),
    echo("\n"),
    echo(NewOffset),
    echo(" --- "),
    display_tree(B2, NewOffset).
