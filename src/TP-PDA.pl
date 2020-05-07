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

:- op(100,fx,marked)  . % for marked forms

% ----------------------------------------------------
% Implantation de la méthode pour le calcul propositionnel
% ----------------------------------------------------

% ----------------------------------------------------
% Prédicats rules: Permet de vérifier quelle règle appliquer
% à la formule
% ----------------------------------------------------

rule(Form, A, marked) :- Form = marked (A).

rule(Form, A, B, or) :- Form = A v B.
rule(Form, A, B, nor) :- Form = not (A v B).

rule(Form, A, B, and) :- Form = A & B.
rule(Form, A, B, nand) :- Form = not (A & B).

rule(Form, A, B, imp) :- Form = A => B.
rule(Form, A, B, nimp) :- Form = not (A => B).

rule(not Form, A, B, nforall) :- rule(Form, A, B1, forall), B1 \= not F, B = not B1.
rule(not Form, A, B, nexists) :- rule(Form, A, B1, exists), B1 \= not F, B = not B1.
rule(not Form, A, B, nforall) :- rule(Form, A, B1, forall), B1 = not F, B = F.
rule(not Form, A, B, nexists) :- rule(Form, A, B1, exists), B1 = not F, B = F.

rule(Form, A, B, forall) :-
    compound(Form), functor(Form, Name, Arity), Name == forall, Arity == 2,
    arg(1, Form, Var), var(Var), A = Var, arg(2, Form, B).

rule(Form, A, B, exists) :-
    compound(Form), functor(Form, Name, Arity), Name == exists, Arity == 2,
    arg(1, Form, Var), var(Var), A = Var, arg(2, Form, B).

% ----------------------------------------------------
% Prédicats apply: Permet d'appliquer une règle sur une formule
% ----------------------------------------------------

%cas simples où la branche ne contient pas de sous branche
apply(Form, Branch, New_Branch, _, _, _, _, or) :- no_sub_branch(Branch),!, rule(Form, F1, F2, or), append(Branch, [[F1]], Branch_Temp), append(Branch_Temp, [[F2]], New_Branch).
apply(Form, Branch, New_Branch, _, _, _, _, nor):- no_sub_branch(Branch),!, rule(Form, F1, F2, nor), append(Branch, [not F1, not F2], New_Branch).

apply(Form, Branch, New_Branch, _, _, _, _, and):- no_sub_branch(Branch),!, rule(Form, F1, F2, and), append(Branch, [F1, F2], New_Branch).
apply(Form, Branch, New_Branch, _, _, _, _, nand):- no_sub_branch(Branch),!, rule(Form, F1, F2, nand), append(Branch, [[not F1]], Branch_Temp), append(Branch_Temp, [[not F2]], New_Branch).

apply(Form, Branch, New_Branch, _, _ ,_ ,_, imp):- no_sub_branch(Branch),!, rule(Form, F1, F2, imp), append(Branch, [[not F1]], Branch_Temp), append(Branch_Temp, [[F2]], New_Branch).
apply(Form, Branch, New_Branch, _, _, _, _, nimp):- no_sub_branch(Branch),!, rule(Form, F1, F2, nimp), append(Branch, [F1, not F2], New_Branch).
apply(Form, Branch, New_Branch, Constants, ToConsume, New_Constants, New_ToConsume, exists) :- no_sub_branch(Branch),!, rule(Form, Var, F, exists), count_constants(Constants, N),
NameConstant is N+1, Var = NameConstant, append(Branch, [Form], New_Branch), append(Constants, [NameConstant], New_Constants).
%cas où la branche contient des sous branches
apply(Form, Branch, New_Branch, Constants, ToConsume, New_Constants, New_ToConsume, Rule) :- 
    \+no_sub_branch(Branch), 
    rule(Form, _, _, Rule), 
    find_sub_branches(Branch, B1, B2), 
    find_sub_branches(Constants, C1, C2),
    apply(Form, B1, NB1, C1, ToConsume, NC1, New_ToConsume, Rule), 
    apply(Form, B2, NB2, C2, ToConsume, NC2, New_ToConsume, Rule),
    remove(B1, Branch, Branch_Temp1), remove(B2, Branch_Temp1, Branch_Temp2),
    append(Branch_Temp2, [NB1], Branch_Temp3), append(Branch_Temp3, [NB2], New_Branch),
    remove(C1, Constants, Constants_Temp1), remove(C2, Constants_Temp1, Constants_Temp2),
    append(Constants_Temp2, [NC1], Constants_Temp3), append(Constants_Temp3, [NC2], New_Constants).


test(Tree, Sub1, Sub2, C, C1, C2):- find_sub_branches(Tree, Sub1, Sub2), find_sub_branches(C, C1, C2).


% ----------------------------------------------------
% Prédicat no_sub_branch: rend vrai si la branche n'a pas de sous branche
% ----------------------------------------------------
no_sub_branch([]).
no_sub_branch([First|Others]) :- \+is_list(First), no_sub_branch(Others).


% ----------------------------------------------------
% Prédicat find_sub_branches: rend vrai si B1 et B2 sont les sous Branches de Branch
% ----------------------------------------------------
find_sub_branches([], _, _).
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
% Prédicat get_before_sub_branches: rend vrai si BeforeBranches correspond
% à ce qui se trouve avant les branches
% ----------------------------------------------------

get_before_sub_branches([], BeforeBranches) :- 
    BeforeBranches = [].

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
remove(List, List, []).
remove(X, [X|Others], R1) :- remove(X, Others, R1).
remove(X, [Y|Others], R1) :- X \== Y, length(Others, N), N > 0, remove(X, Others, R2), append([Y], R2, R1).
remove(X, [Y|Others], R1) :- X \== Y, length(Others, 0), R1 = [Y].

% ----------------------------------------------------
% Prédicats utilitaires
% ----------------------------------------------------

count_constants([], 0).
count_constants([First|Others], NbConstants):- \+is_list(First), count_constants(Others, NB), NbConstants is NB+1.
count_constants([First|Others], NbConstants):- is_list(First), count_constants(First, NB1), count_constants(Others, NB2), NbConstants is NB1+NB2.

isEmpty([]).

% Prédicat de copie
copy([], []).
copy([H| L], [H| N]) :- copy(L, N).

%cas ou la branche à remplacer est l'arbre complet
replace_branch(Tree, NewBranch, Tree, NewBranch).

%cas ou tree contient là branche (les suivants ne la contiennent pas)
replace_branch(Tree, NewTree, Branch, NewBranch) :-
    member(Branch, Tree),
    remove(Branch, Tree, TempTree),
    append(TempTree, [NewBranch], NewTree).

%cas ou le premier élément n'est pas une liste
replace_branch([First|Others], NewTree, Branch, NewBranch):- 
    \+is_list(First),
    replace_branch(Others, TempNewTree, Branch, NewBranch),
    append([First], TempNewTree, NewTree).


%cas ou First est une liste, qui n'est pas la branche (vu que l'arbre ne la contient pas)
replace_branch([First|Others], NewTree, Branch, NewBranch):-
    is_list(First),
    replace_branch(First, TempTree, Branch, NewBranch),
    NewTree = [TempTree|Others].

%cas ou First est une liste, qui n'est pas la branche, mais le remplacement échoue
replace_branch([First|Others], NewTree, Branch, NewBranch):-
    is_list(First),
    \+replace_branch(First, _, Branch, NewBranch),
    replace_branch(Others, TempTree, Branch, NewBranch),
    NewTree = [First|TempTree].

% permet de reformer un arbre avec la branche principale et les deux sous branches
concat_and_close_new_tree(TreeBeginning, B1, B2, NewTree) :-
    get_before_sub_branches(TreeBeginning, BeforeBranches),
    append(BeforeBranches, [B1], Tmp),
    append(Tmp, [B2], Tmp2),
    (
        conflict_exists(B1), conflict_exists(B2),
        append([conflict], Tmp2, NewTree)
        ;
        NewTree = Tmp2
    ).

% ----------------------------------------------------
% Prédicats qui permettent de parcourir l'arbre et de fermer les branches
% qui contiennent un conflit
% ----------------------------------------------------

%close_tree([a v (not a), [a, not a], [b, not b]], [a v (not a),[a, not a], [b, not b]], ClosedTree),!.

% Fin de la branche
close_tree(TreeBeginning, [], ClosedTree) :-
    ClosedTree = TreeBeginning,
    echo("1").

% Branche déjà fermé
close_tree(TreeBeginning, _, ClosedTree) :- 
    conflict_exists(TreeBeginning),
    ClosedTree = TreeBeginning,
    echo("2").

% Formule à vérifier
close_tree(TreeBeginning, [First| Others], ClosedTree) :-
    \+is_list(First),
    close_conflicts(TreeBeginning, Others, First, ClosedTreeForFirst),
    get_position_in_tree(ClosedTreeForFirst, First, [_| OthersInClosedTree]),
    close_tree(ClosedTreeForFirst, OthersInClosedTree, ClosedTree),
    echo("3").

% Jonction entre deux branches
close_tree(TreeBeginning, [First| _], ClosedTree) :-
    is_list(First),
    find_sub_branches(TreeBeginning, B1, B2),
    close_tree(B1, B1, ClosedB1),
    close_tree(B2, B2, ClosedB2),
    concat_and_close_new_tree(TreeBeginning, ClosedB1, ClosedB2, ClosedTree),
    echo("4").

% ----------------------------------------------------
% Prédicat close_conflicts permet de fermer les branches
% qui présentent un conflit avec la formule en paramètre
% ----------------------------------------------------

close_conflicts(TreeBeginning, [_| _], _, ClosedTree) :-
    conflict_exists(TreeBeginning), ClosedTree = TreeBeginning.

close_conflicts(TreeBeginning, [], _, ClosedTree) :-
    ClosedTree = TreeBeginning.

close_conflicts(TreeBeginning, [First| _], Form, ClosedTree) :-
    \+is_list(First),
    is_conflict(First, Form),
    append([conflict], TreeBeginning, ClosedTree).

close_conflicts(TreeBeginning, [First| Others], Form, ClosedTree) :-
    \+is_list(First),
    \+is_conflict(First, Form),
    close_conflicts(TreeBeginning, Others, Form, ClosedTree), !.

close_conflicts(TreeBeginning, [First| Others], Form, ClosedTree) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    close_conflicts(B1, B1, Form, ClosedB1), !,
    close_conflicts(B2, B2, Form, ClosedB2), !,
    concat_and_close_new_tree(TreeBeginning, ClosedB1, ClosedB2, ClosedTree).

% ----------------------------------------------------
% Prédicat is_conflict permet de vérifier si un conflit existe entre deux formules
% ----------------------------------------------------

is_conflict(A, B):- \+is_list(A), A = not B.
is_conflict(A, B):- \+is_list(A), B = not A.

% ----------------------------------------------------
% Prédicat qui permet de vérifier si une branche possède un conflit
% ----------------------------------------------------

conflict_exists([conflict| _]).

% ----------------------------------------------------
% Prédicat de récupération de la formule sur laquelle on veut travailler
% ----------------------------------------------------


get_form([First| Others], TreeBeginning, Form, Branch, Rule, propositional) :-
    \+is_list(First),
    \+rule(First, _, marked),
    First \= conflict,
    \+rule(First, _, _, Rule),
    get_form(Others, TreeBeginning, Form, Branch, Rule, propositional).

get_form([First| _], TreeBeginning, Form, Branch, Rule, propositional) :-
    \+is_list(First),
    \+rule(First, _, marked),
    First \= conflict,
    Branch = TreeBeginning,
    Form = First,
    rule(Form, _, _, Rule).

get_form([First| Others], TreeBeginning, Form, Branch, Rule, propositional) :-
    \+is_list(First),
    rule(First, _, marked),
    get_form(Others, TreeBeginning, Form, Branch, Rule, propositional), !.

get_form([First| Others], _, Form, Branch, Rule, propositional) :-
    is_list(First),
    find_sub_branches([First| Others], B1, _),
    \+conflict_exists(B1),
    get_form(B1, B1, Form, Branch, Rule, propositional), !.

get_form([First| Others], _, Form, Branch, Rule, propositional) :-
    is_list(First),
    find_sub_branches([First| Others], _, B2),
    \+conflict_exists(B2),
    get_form(B2, B2, Form, Branch, Rule, propositional), !.

% ----------------------------------------------------
% Prédicat d'ajout d'une formule déjà utilisée dans un tableau de formules marquées
% ----------------------------------------------------

mark_Form(Form, [First| Others], New_Marked) :-
    \+is_list(First),
    \+Form == First,
    mark_Form(Form, Others, Tmp),
    append([First], Tmp, New_Marked).

mark_Form(Form, [First| Others], New_Marked) :-
    \+is_list(First),
    Form == First,
    New_Form = marked (Form),
    append([New_Form], Others,New_Marked).

% ----------------------------------------------------
% Prédicats solve: Permet de lancer l'algorithme des tableaux sémantiques
% ----------------------------------------------------

solve(Tree) :- 
    clr_echo,
    close_tree(Tree, Tree, TempTree), !,
    loop(TempTree, ClosedTree, propositional),!,

    set_echo,
    display_tree(ClosedTree),!.

% ----------------------------------------------------
% Prédicats loop pour la logique propositionnelle
% ----------------------------------------------------

loop(Tree, ClosedTree, _) :- conflict_exists(Tree), ClosedTree = Tree.

loop(Tree, ClosedTree, propositional) :-
    get_form(Tree, Tree, Form, Branch, Rule, propositional), !,
    apply(Form, Branch, NewBranch, _, _, _, _, Rule),
    mark_Form(Form, NewBranch, MarkedBranch),
    replace_branch(Tree, TempTree, Branch, MarkedBranch),
    close_tree(TempTree, TempTree, TempTree3), !,
    loop(TempTree3, ClosedTree, propositional), !.

% ----------------------------------------------------
% Prédicats get_forall : prédicat qui permet de récupérer les forall
% ----------------------------------------------------

get_forall(Tree, Mult, Constants, Forall) :- get_forall(Tree, Mult, Constants, [], Forall).

get_forall([], _, _, Forall, NewForall) :- NewForall = Forall.

get_forall([First| Others], Mult, Constants, Forall, NewForall) :-
    \+is_list(First),
    rule(First, _, _, forall),
    append(Forall, [map(First, Mult, Constants)], Tmp),
    get_forall(Others, Mult, Constants, Tmp, NewForall).

get_forall([First| Others], Mult, Constants, Forall, NewForall) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    find_sub_branches(Constants, C1, C2),

    get_forall(B1, Mult, C1, [], Forall1),
    get_forall(B2, Mult, C2, [], Forall2),

    append(Forall, Forall1, Tmp),
    append(Tmp, Forall2, NewForall).

% ----------------------------------------------------
% Prédicats get_all_constants : prédicat qui permet de récupérer les constantes
% ----------------------------------------------------

get_all_constants(Tree, Constants) :- get_all_constants(Tree, [], Constants).

get_all_constants([], Constants, NewConstants) :- NewConstants = Constants.

get_all_constants([First| Others], Constants, NewConstants) :-
    \+is_list(First),
    get_constants(First, Constants, ConstantsInForm),
    union(Constants, ConstantsInForm, Tmp),
    get_all_constants(Others, Tmp, NewConstantsOthers),
    union(Tmp, NewConstantsOthers, NewConstants).

get_all_constants([First| Others], Constants, NewConstants) :-
    is_list(First),
    get_before_sub_branches(Constants, BeforeBranches),
    find_sub_branches([First| Others], B1, B2),
    get_all_constants(B1, [], ConstantsB1),
    get_all_constants(B2, [], ConstantsB2),

    union(BeforeBranches, ConstantsB1, NewB1),
    union(BeforeBranches, ConstantsB2, NewB2),
    append(Constants, [NewB1], Tmp),
    append(Tmp, [NewB2], NewConstants).

% ----------------------------------------------------
% Prédicats get_constants : prédicat qui permet de récupérer les constantes en provenance
% d'une formule
% ----------------------------------------------------

get_constants(Form, Constants, NewConstants) :-
    rule(Form, A, B, _),
    get_constants(A, [], ConstantsA),
    get_constants(B, [], ConstantsB),
    union(Constants, ConstantsA, Tmp),
    union(Tmp, ConstantsB, NewConstants).

get_constants(Form, Constants, NewConstants) :-
    \+rule(Form, _, _, _),
    (
        atomic(Form),
        append(Constants, [Form], NewConstants)
        ;
        compound(Form),
        get_constants_in_function(Form, [], InFunctionConstants), !,
        append(Constants, InFunctionConstants, NewConstants)
    ).

% ----------------------------------------------------
% Prédicats get_constants_in_function : prédicat qui permet de récupérer les constantes 
% en provenance d'une fonction
% ----------------------------------------------------

get_constants_in_function(Constant, Constants, NewConstants) :-
    (
        atomic(Constant), union(Constants, [Constant], NewConstants)
        ;
        var(Constant), NewConstants = Constants
    ).

get_constants_in_function(Function, Constants, NewConstants) :-
    compound(Function),
    compound_name_arguments(Function, _, [First| Arguments]),
    get_constants_in_function(First, [], ConstantsFirst),
    get_constants_in_arguments(Arguments, [], ConstantsArguments),
    union(Constants, ConstantsFirst, Tmp),
    union(Tmp, ConstantsArguments, NewConstants).

% ----------------------------------------------------
% Prédicats get_constants_in_arguments : prédicat qui permet de récupérer les constantes 
% en provenance des arguments d'une fonction
% ----------------------------------------------------

get_constants_in_arguments([], Constants, NewConstants) :- NewConstants = Constants.

get_constants_in_arguments([First| Arguments], Constants, NewConstants) :-
    get_constants_in_function(First, [], ConstantsFirst),
    get_constants_in_arguments(Arguments, [], ConstantsArguments),
    union(Constants, ConstantsFirst, Tmp),
    union(Tmp, ConstantsArguments, NewConstants).

% ----------------------------------------------------
% Prédicats constant_exists : prédicat qui permet de vérifier si une constante
% existe dans l'arbre donné
% ----------------------------------------------------

constant_exists(ConstantsTree, Constant) :-
    (member(Constant, ConstantsTree)
    ;
    \+no_sub_branch(ConstantsTree),
    find_sub_branches(ConstantsTree, B1, B2),
    (constant_exists(B1, Constant);constant_exists(B2, Constant))).

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