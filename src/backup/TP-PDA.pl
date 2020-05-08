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

rule(Form, A, marked) :- \+var(Form), Form = marked (A).

rule(Form, A, B, or) :- \+var(Form), Form = A v B.
rule(Form, A, B, nor) :- \+var(Form), Form = not (A v B).

rule(Form, A, B, and) :- \+var(Form), Form = A & B.
rule(Form, A, B, nand) :- \+var(Form), Form = not (A & B).

rule(Form, A, B, imp) :- \+var(Form), Form = A => B.
rule(Form, A, B, nimp) :- \+var(Form), Form = not (A => B).

rule(CF, A, B, nforall) :- \+var(CF), CF = not Form, rule(Form, A, B1, forall), B1 \= not F, B = not B1.
rule(CF, A, B, nexists) :- \+var(CF), CF = not Form, rule(Form, A, B1, exists), B1 \= not F, B = not B1.
rule(CF, A, B, nforall) :- \+var(CF), CF = not Form, rule(Form, A, B1, forall), B1 == not F, B = F.
rule(CF, A, B, nexists) :- \+var(CF), CF = not Form, rule(Form, A, B1, exists), B1 == not F, B = F.

rule(Form, A, B, forall) :-
    \+var(Form), 
    compound(Form), functor(Form, Name, Arity), Name == forall, Arity == 4,
    arg(1, Form, Var), var(Var), A = Var, arg(2, Form, B).

rule(Form, A, B, exists) :-
    \+var(Form), 
    compound(Form), functor(Form, Name, Arity), Name == exists, Arity == 2,
    arg(1, Form, Var), var(Var), A = Var, arg(2, Form, B).

rule(Form, A, B, unparsedForall) :-
    \+var(Form), 
    compound(Form), functor(Form, Name, Arity), Name == forall, Arity == 2,
    arg(1, Form, Var), var(Var), A = Var, arg(2, Form, B).

% ----------------------------------------------------
% Prédicat is_composed est vrai si la règle correspond à un composé
% (exists(X, ...), forall(X, ...) ...)
% ----------------------------------------------------

is_composed(Rule) :- 
    (
        Rule == unparsedForall; 
        Rule == forall; 
        Rule == nforall; 
        Rule == exists; 
        Rule == nexists
    ).

% ----------------------------------------------------
% Prédicats apply: Permet d'appliquer une règle sur une formule
% ----------------------------------------------------

%cas simples où la branche ne contient pas de sous branche
apply(Form, Branch, New_Branch, Constants, New_Constants,_, or) :- 
    no_sub_branch(Branch),!,
    rule(Form, F1, F2, or),
    append(Branch, [[F1]], Branch_Temp),
    append(Branch_Temp, [[F2]], New_Branch),

    get_before_sub_branches(Constants, Before_Branches),
    append(Constants, [Constants], Tmp_Const),
    append(Tmp_Const, [Constants], New_Constants).

apply(Form, Branch, New_Branch, Constants, Constants,_, nor):- 
    no_sub_branch(Branch),!, rule(Form, F1, F2, nor), append(Branch, [not F1, not F2], New_Branch).

apply(Form, Branch, New_Branch, Constants, Constants,_, and):- 
    no_sub_branch(Branch),!, rule(Form, F1, F2, and), append(Branch, [F1, F2], New_Branch).

apply(Form, Branch, New_Branch, Constants, New_Constants,_, nand):- 
    no_sub_branch(Branch),!,
    rule(Form, F1, F2, nand),
    append(Branch, [[not F1]], Branch_Temp),
    append(Branch_Temp, [[not F2]], New_Branch),
    append(Constants, [Constants], Tmp_Const),
    append(Tmp_Const, [Constants], New_Constants).
apply(Form, Branch, New_Branch, Constants, New_Constants ,_, imp):- 
    no_sub_branch(Branch),!,
    rule(Form, F1, F2, imp),
    append(Branch, [[not F1]], Branch_Temp),
    append(Branch_Temp, [[F2]], New_Branch),

    append(Constants, [Constants], Tmp_Const),
    append(Tmp_Const, [Constants], New_Constants).

apply(Form, Branch, New_Branch, Constants, Constants,_, nimp):- 
    no_sub_branch(Branch),!, rule(Form, F1, F2, nimp), append(Branch, [F1, not F2], New_Branch).

apply(Form, Branch, New_Branch, Constants, New_Constants, _, exists) :- 
    no_sub_branch(Branch),!,
    rule(Form, Var, F, exists),

    count_constants(Constants, N),
    generate_constant(Constants, N, New_Constant),
    replace_var_by_const(F, Var, New_Constant, New_Form),

    append(Branch, [New_Form], New_Branch),
    append(Constants, [New_Constant], New_Constants).

apply(Form, Branch, New_Branch, Constants, Constants, _, forall) :- 
    no_sub_branch(Branch),!,
    rule(Form, Var, F, forall),
    arg(3, Form, Mult),
    arg(4, Form, Consumed_Constants),
    get_before_sub_branches(Constants, BeforeBranches),
    subtract(BeforeBranches, Consumed_Constants, Constants_To_Consume),

    consume_constants(F, Var, Constants_To_Consume, New_Forms),
    append(Consumed_Constants, Constants_To_Consume, New_Constants),
    New_Form = forall(Var, F, Mult, New_Constants),
    replace_form_in_branch(Branch, Changed_Branch, Form, New_Form),
    append(Changed_Branch, New_Forms, New_Branch).

apply(Form, Branch, New_Branch, Constants, Constants, Mult, nexists) :- 
    no_sub_branch(Branch),!,
    rule(Form, Var, F, nexists),
    New_Form = forall(Var, F, Mult, []),
    append(Branch, [New_Form], New_Branch).

apply(Form, Branch, New_Branch, Constants, Constants, Mult, nforall) :- 
    no_sub_branch(Branch),!,
    rule(Form, Var, F, nforall),
    New_Form = exists(Var, F),
    append(Branch, [New_Form], New_Branch).

%cas où la branche contient des sous branches
apply(Form, Branch, New_Branch, Constants, New_Constants, Mult, Rule) :- 
    \+no_sub_branch(Branch), 
    rule(Form, _, _, Rule), 

    find_sub_branches(Branch, B1, B2), 
    find_sub_branches(Constants, C1, C2),

    apply(Form, B1, New_B1, C1, New_C1, Mult, Rule),
    apply(Form, B2, New_B2, C2, New_C2, Mult, Rule),

    replace_branch(Branch, TempBranch, B1, New_B1),
    replace_branch(TempBranch, New_Branch, B2, New_B2),

    replace_branch(Constants, TempConstants, C1, New_C1),
    replace_branch(TempConstants, New_Constants, C2, New_C2).

% ----------------------------------------------------
% Prédicat no_sub_branch: rend vrai si la branche n'a pas de sous branche
% ----------------------------------------------------
no_sub_branch([]).
no_sub_branch([First|Others]) :- \+is_list(First), no_sub_branch(Others).


% ----------------------------------------------------
% Prédicat find_sub_branches: rend vrai si B1 et B2 sont les sous Branches de Branch
% ----------------------------------------------------
find_sub_branches([], [], []).
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
remove(X, [X|Others], R1) :- R1 = Others.
remove(X, [Y|Others], R1) :- X \== Y, length(Others, N), N > 0, remove(X, Others, R2), append([Y], R2, R1).
remove(X, [Y|Others], R1) :- X \== Y, length(Others, 0), R1 = [Y].

% ----------------------------------------------------
% Prédicats utilitaires
% ----------------------------------------------------

consume_constants(Form, Var, [], New_Forms) :- New_Forms = [].

consume_constants(Form, Var, [First| Others], New_Forms) :-
    replace_var_by_const(Form, Var,First, New_Form),
    consume_constants(Form, Var, Others, NF),
    append([New_Form], NF, New_Forms).

generate_constant(Constants, Nb_Constants, New_C) :-
    New_Constant is Nb_Constants + 1,
    contains_constant(Constants, New_Constant),
    generate_constant(Constants, New_Constant, New_C).

generate_constant(Constants, Nb_Constants, New_C) :-
    New_C is Nb_Constants + 1, \+contains_constant(Constants, New_C).

count_constants([], 0).
count_constants([First|Others], NbConstants):- \+is_list(First), count_constants(Others, NB), NbConstants is NB+1.
count_constants([First|Others], NbConstants):- is_list(First), count_constants(First, NB1), count_constants(Others, NB2), NbConstants is NB1+NB2.

contains_constant([First| Others], C) :- \+is_list(First), (First == C; First \= C, contains_constant(Others, C)).
contains_constant([First| Others], C) :- is_list(First), find_sub_branches([First| Others], B1, _), contains_constant(B1, C).
contains_constant([First| Others], C) :- is_list(First), find_sub_branches([First| Others], _, B2), contains_constant(B2, C).

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


replace_form_in_branch(Form, New_Form, Form, New_Form).

replace_form_in_branch([First|Others], Changed_Branch, Form, New_Form) :-
    is_list(First),
    replace_form_in_branch(First, TempTree, Form, New_Form),
    Changed_Branch = [TempTree| Others].

replace_form_in_branch([First|Others], Changed_Branch, Form, New_Form) :-
    is_list(First),
    \+replace_form_in_branch(First, _, Form, New_Form),
    replace_branch(Others, TempTree, Form, New_Form),
    Changed_Branch = [First| TempTree].

replace_form_in_branch([First|Others], Changed_Branch, Form, New_Form) :-
    \+is_list(First),
    (
        \+(First == Form),
        replace_form_in_branch(Others, Changed, Form, New_Form),
        append([First], Changed, Changed_Branch)
        ;
        First == Form,
        append([New_Form], Others, Changed_Branch)
    ).

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

get_form([First| Others], TreeBeginning, Constants, Form, C, Branch, Rule) :-
    \+is_list(First),
    \+rule(First, _, marked),
    First \= conflict,
    \+rule(First, _, _, Rule),
    get_form(Others, TreeBeginning, Constants, Form, C, Branch, Rule).

get_form([First| Others], TreeBeginning, Constants, Form, C, Branch, Rule) :-
    \+is_list(First),
    \+rule(First, _, marked),
    First \= conflict,
    rule(First, _, _, forall),
    arg(3, First, Mult),
    Mult > 0,
    \+get_form(Others, TreeBeginning, Constants, Form, C, Branch, Rule),
    Branch = TreeBeginning,
    Form = First,
    C = Constants,
    Rule = forall.

get_form([First| Others], TreeBeginning, Constants, Form, C, Branch, Rule) :-
    \+is_list(First),
    \+rule(First, _, marked),
    First \= conflict,
    rule(First, _, _, forall),
    get_form(Others, TreeBeginning, Constants, Form, C, Branch, Rule).

get_form([First| _], TreeBeginning, Constants, Form, C, Branch, Rule) :-
    \+is_list(First),
    \+rule(First, _, marked),
    \+rule(First, _, _, forall),
    First \= conflict,
    Branch = TreeBeginning,
    Form = First,
    C = Constants,
    rule(Form, _, _, Rule).

get_form([First| Others], TreeBeginning, Constants, Form, C, Branch, Rule) :-
    \+is_list(First),
    rule(First, _, marked),
    get_form(Others, TreeBeginning, Constants, Form, C, Branch, Rule), !.

get_form([First| Others], _, Constants, Form, C, Branch, Rule) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    find_sub_branches(Constants, C1, C2),
    \+conflict_exists(B1),
    get_form(B1, B1, C1, Form, C, Branch, Rule), !.

get_form([First| Others], _, Constants, Form, C, Branch, Rule) :-
    is_list(First),
    find_sub_branches([First| Others], _, B2),
    find_sub_branches(Constants, _, C2),
    \+conflict_exists(B2),
    get_form(B2, B2, C2, Form, C, Branch, Rule), !.

% ----------------------------------------------------
% Prédicat de marquage des formules utilisées
% ----------------------------------------------------

mark_form(Form, [First| Others], New_Marked) :-
    \+is_list(First),
    \+Form == First,
    mark_form(Form, Others, Tmp),
    append([First], Tmp, New_Marked).

mark_form(Form, [First| Others], New_Marked) :-
    \+is_list(First),
    \+rule(Form, _, _, forall),
    Form == First,
    New_Form = marked (Form),
    append([New_Form], Others, New_Marked).

mark_form(Form, [First| Others], New_Marked) :-
    \+is_list(First),
    Form == First,
    rule(Form, Var, F, forall),
    arg(3, Form, Mult),
    arg(4, Form, Const),

    New_Mult is Mult - 1,
    Tmp = forall(Var, F, New_Mult, Const),

    (
        New_Mult == 0, New_Form = marked (Tmp)
        ;
        New_Form = Tmp
    ),
    append([New_Form], Others, New_Marked).

% ----------------------------------------------------
% Prédicats check_free_var_in_tree rend vrai s'il n'y a pas de variables libres dans l'arbre
% ----------------------------------------------------

check_free_var_in_tree(Var) :-
    var(Var), fail.

check_free_var_in_tree(Tree) :- Tree == [].

check_free_var_in_tree([First| Others]) :-
    \+var(First),
    \+is_list(First),
    check_free_var_in_formula(First, []),
    check_free_var_in_tree(Others).

check_free_var_in_tree([First| Others]) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    check_free_var_in_tree(B1),
    check_free_var_in_tree(B2).

% ----------------------------------------------------
% Prédicats check_free_var_in_formula rend vrai s'il n'y a pas de variables libres dans la formule
% ----------------------------------------------------

check_free_var_in_formula(Form, Closed_Var) :-
    var(Form), is_close(Form, Closed_Var).

check_free_var_in_formula(Form, Closed_Var) :-
    \+var(Form),
    \+rule(Form, _, _, _),
    check_free_var_in_function(Form, Closed_Var).

check_free_var_in_formula(Form, Closed_Var) :- 
    \+var(Form),
    \+rule(Form, _, _, _),
    check_free_var_in_function(Form, Closed_Var).

check_free_var_in_formula(Form, Closed_Var) :-
    \+var(Form),
    rule(Form, A, B, Rule),
    \+is_composed(Rule),
    check_free_var_in_formula(A, Closed_Var),
    check_free_var_in_formula(B, Closed_Var).

check_free_var_in_formula(Form, Closed_Var) :-
    \+var(Form),
    rule(Form, A, B, Rule),
    is_composed(Rule),
    append([A], Closed_Var, New_Closed_Var),
    check_free_var_in_formula(B, New_Closed_Var).


% ----------------------------------------------------
% Prédicats check_free_var_in_function rend vrai s'il n'y a pas de variables libres dans une fonction
% ----------------------------------------------------

check_free_var_in_function(Form, _) :- atomic(Form).
check_free_var_in_function(Form, Closed_Var) :- var(Form), is_close(Form, Closed_Var).
check_free_var_in_function(Form, Closed_Var) :- 
    compound(Form), 
    compound_name_arguments(Form, _, [F| A]), 
    check_free_var_in_arguments([F| A], Closed_Var).

% ----------------------------------------------------
% Prédicats check_free_var_in_arguments rend vrai s'il n'y a pas de variables libres dans une liste
% d'arguments
% ----------------------------------------------------

check_free_var_in_arguments([], _).
check_free_var_in_arguments([First| _], Closed_Var) :- var(First), is_close(First, Closed_Var).
check_free_var_in_arguments([First| Others], Closed_Var) :- atomic(First), check_free_var_in_arguments(Others, Closed_Var).
check_free_var_in_arguments([First| Others], Closed_Var) :- 
    compound(First), 
    check_free_var_in_function(First, Closed_Var), 
    check_free_var_in_arguments(Others, Closed_Var).

is_close(V, [First| Others]) :- 
    (
        V == First
        ;
        V \= First, is_close(V, Others)
    ).

% ----------------------------------------------------
% Prédicats format_form_in_tree : prédicat qui permet de formater les formules dans l'arbre
% pour par exemple transformer les pour tout afin de travailler plus facilement avec
% ----------------------------------------------------

format_form_in_tree([], _, New_Tree) :- New_Tree = [].

format_form_in_tree([First| Others], Mult, New_Tree) :-
    \+is_list(First),
    format_formula(First, Mult, New_Form),
    format_form_in_tree(Others, Mult, NT),
    append([New_Form], NT, New_Tree).

format_form_in_tree([First| Others], Mult, New_Tree) :-
    is_list(First),
    find_sub_branches([First| Others], B1, B2),
    format_form_in_tree(B1, Mult, NewB1),
    format_form_in_tree(B2, Mult, NewB2),
    append([NewB1], [NewB2], New_Tree).

% ----------------------------------------------------
% Prédicats format_formula : prédicat qui permet de formater une formule
% ----------------------------------------------------

format_formula(Form, _, New_Form) :-
    var(Form),
    New_Form = Form.

format_formula(Form, _, New_Form) :-
    \+rule(Form, _, _, _),
    New_Form = Form.

format_formula(Form, Mult, New_Form) :-
    rule(Form, A, B, Rule),
    \+is_composed(Rule),
    format_formula(A, Mult, NewA),
    format_formula(B, Mult, NewB),
    recreate_formula(NewA, NewB, Mult, [], Rule, New_Form).

format_formula(Form, Mult, New_Form) :-
    rule(Form, A, B, Rule),
    is_composed(Rule),
    format_formula(B, Mult, NewB),
    recreate_formula(A, NewB, Mult, [], Rule, New_Form).

% ----------------------------------------------------
% Prédicats recreate_formula : prédicat qui permet de formater une formule
% ----------------------------------------------------

recreate_formula(A, B, _, _, or, Form)   :- Form = A v B.
recreate_formula(A, B, _, _, nor, Form)  :- Form = not (A v B).

recreate_formula(A, B, _, _,and, Form)  :- Form = A & B.
recreate_formula(A, B, _, _,nand, Form) :- Form = not (A & B).

recreate_formula(A, B, _, _,imp, Form)  :- Form = A => B.
recreate_formula(A, B, _, _,nimp, Form) :- Form = not (A => B).

recreate_formula(A, B, Mult, Const, forall, Form) :- Form = forall(A, B, Mult, Const).
recreate_formula(A, B, Mult, Const, unparsedForall, Form) :- Form = forall(A, B, Mult, Const).
recreate_formula(A, B, Mult, Const, nforall, Form) :- Form = not forall(A, B, Mult, Const).
recreate_formula(A, B, _, _, nexists, Form) :- Form = not exists(A, B).
recreate_formula(A, B, _, _, exists, Form)  :- Form = exists(A, B).

% ----------------------------------------------------
% Prédicats get_all_constants : prédicat qui permet de récupérer les constantes
% données par l'utilisateur
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
        ;
        \+atomic(Form), \+compound(Form), NewConstants = Constants
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
% Prédicats replace_var_by_const qui est vrai si New_Form est la formule avec Var
% remplacée par Const
% ----------------------------------------------------

replace_var_by_const(Form, Var, Const, New_Form) :-
    (var(Form); compound(Form); atomic(Form)), \+ rule(Form, _, _, _),
    replace_var_by_const_in_function(Form, Var, Const, New_Form).

replace_var_by_const(Form, Var, Const, New_Form) :-
    rule(Form, Var2, F, Rule),
    is_composed(Rule),
    (
        same_term(Var2, Var), New_Form = Form
        ;
        \+same_term(Var2, Var),
        (
            (Rule == forall; Rule == nforall),
            arg(3, Form, Mult),
            arg(4, Form, Constants),
            replace_var_by_const(F, Var, Const, New_F),
            recreate_formula(Var2, New_F, Mult, Constants, Rule, New_Form)
            ;
            Rule \= forall, Rule \= nforall,
            replace_var_by_const(F, Var, Const, New_F),
            recreate_formula(Var2, New_F, _, [], Rule, New_Form)
        )
    ).

replace_var_by_const(Form, Var, Const, New_Form) :-
    rule(Form, A, B, Rule),
    \+is_composed(Rule),
    replace_var_by_const(A, Var, Const, New_A),
    replace_var_by_const(B, Var, Const, New_B),
    recreate_formula(New_A, New_B, _, [], Rule, New_Form).

replace_var_by_const_in_function(Form, Var, Const, New_Form) :-
    compound(Form),
    compound_name_arguments(Form, Name, Args),
    replace_var_by_const_in_arguments(Args, Var, Const, New_Args),
    functor(Form, Name, Arity),
    set_arguments_in_function(Form, 0, Arity, New_Args),
    New_Form = Form.

replace_var_by_const_in_function(Form, Var, Const, New_Form) :-
    (var(Form); atomic(Form)),
    replace_var_by_const_in_arguments([Form], Var, Const, New_Form).

replace_var_by_const_in_arguments([First| Others], Var, Const, New_Args) :-
    var(First),
    same_term(First, Var),
    replace_var_by_const_in_arguments(Others, Var, Const, A),
    append([Const], A, New_Args).

replace_var_by_const_in_arguments([], _, _, New_Args) :- New_Args = [].

replace_var_by_const_in_arguments([First| Others], Var, Const, New_Args) :-
    (atomic(First);var(First), \+same_term(First, Var)),
    replace_var_by_const_in_arguments(Others, Var, Const, A),
    append([First], A, New_Args).

replace_var_by_const_in_arguments([First| Others], Var, Const, New_Args) :-
    compound(First),
    replace_var_by_const_in_function(First, Var, Const, New_Form),
    replace_var_by_const_in_arguments(Others, Var, Const, A),
    append([New_Form], A, New_Args).

set_arguments_in_function(_, Arg, Arity, _) :- Arg == Arity.

set_arguments_in_function(Form, Arg, Arity, [First| Others]) :-
    New_Arg is Arg + 1,
    setarg(New_Arg, Form, First),
    set_arguments_in_function(Form, New_Arg, Arity, Others).

% ----------------------------------------------------
% Prédicats solve: Permet de lancer l'algorithme des tableaux sémantiques
% ----------------------------------------------------

solve(Tree, Mult) :- 
    clr_echo,
    format_form_in_tree(Tree, Mult, New_Tree),
    get_all_constants(New_Tree, Constants),
    display_tree(Constants),
    close_tree(New_Tree, New_Tree, Closed_Tree), !,
    loop(Closed_Tree, Constants, _, Final_Tree, Mult),!,

    set_echo,
    display_tree(Final_Tree),!.

% ----------------------------------------------------
% Prédicats loop qui va gérer la boucle principale de l'algorithme
% ----------------------------------------------------

loop(Tree, _, _, Closed_Tree, _) :- conflict_exists(Tree), Closed_Tree = Tree.

loop(Tree, Constants, Final_Constants, Closed_Tree, Mult) :-
    get_form(Tree, Tree, Constants, Form, C, Branch, Rule), !,
    apply(Form, Branch, NewBranch, C, New_C, Mult, Rule),
    mark_form(Form, NewBranch, MarkedBranch),

    replace_branch(Tree, TempTree, Branch, MarkedBranch),
    replace_branch(Constants, TempConstants, C, New_C),

    close_tree(TempTree, TempTree, TempTree2), !,

    loop(TempTree2, TempConstants, Final_Constants, Closed_Tree, Mult), !.

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