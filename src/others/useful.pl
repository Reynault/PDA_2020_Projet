% ----------------------------------------------------
% TP - PDA - Groupe : Brandon Hornbeck, Reynault Sies
% ----------------------------------------------------

% Ce fichier contient des prédicats utiles pour parcourir et modifier un arbre.

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

% ----------------------------------------------------
% Prédicat qui permet de former les formules issues de la consommation
% de constantes pour un pour tout
% ----------------------------------------------------

consume_constants(_, _, [], New_Forms) :- New_Forms = [].

consume_constants(Form, Var, [First| Others], New_Forms) :-
    replace_var_by_const(Form, Var,First, New_Form),
    consume_constants(Form, Var, Others, NF),
    append([New_Form], NF, New_Forms).

% ----------------------------------------------------
% Prédicat qui permet de générer une nouvelle constante qui n'appartient
% pas au tableau des constantes
% ----------------------------------------------------

generate_constant(Constants, Nb_Constants, New_C) :-
    New_Constant is Nb_Constants + 1,
    contains_constant(Constants, New_Constant),
    generate_constant(Constants, New_Constant, New_C).

generate_constant(Constants, Nb_Constants, New_C) :-
    New_C is Nb_Constants + 1, \+contains_constant(Constants, New_C).

% ----------------------------------------------------
% Prédicat qui permet de compter le nombre de constantes
% ----------------------------------------------------

count_constants([], 0).
count_constants([First|Others], NbConstants):- \+is_list(First), count_constants(Others, NB), NbConstants is NB+1.
count_constants([First|Others], NbConstants):- is_list(First), count_constants(First, NB1), count_constants(Others, NB2), NbConstants is NB1+NB2.

% ----------------------------------------------------
% Prédicat qui est vrai si le tableau de constantes contient la constante C
% ----------------------------------------------------

contains_constant([First| Others], C) :- \+is_list(First), (First == C; First \= C, contains_constant(Others, C)).
contains_constant([First| Others], C) :- is_list(First), find_sub_branches([First| Others], B1, _), contains_constant(B1, C).
contains_constant([First| Others], C) :- is_list(First), find_sub_branches([First| Others], _, B2), contains_constant(B2, C).

% ----------------------------------------------------
% Prédicat qui est vrai si le tableau est vide
% ----------------------------------------------------

isEmpty([]).

% ----------------------------------------------------
% Prédicat de copie de tableau
% ----------------------------------------------------

copy([], []).
copy([H| L], [H| N]) :- copy(L, N).

% ----------------------------------------------------
% Prédicat permettant de remplacer une branche d'un arbre par une autre
% ----------------------------------------------------

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

% ----------------------------------------------------
% Prédicat permettant de remplacer une formule d'un arbre par une autre
% ----------------------------------------------------

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

% ----------------------------------------------------
% Prédicat permettant de reformer un arbre avec la branche principale et les deux sous branches
% ----------------------------------------------------

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

replace_var_by_const(not Form, Var, Const, New_Form) :-
    rule(Form, Var2, F, Rule),
    is_composed(Rule),
    (
        same_term(Var2, Var), New_Form =  not Form
        ;
        \+same_term(Var2, Var),
        (
            (Rule == forall; Rule == nforall),
            arg(3, Form, Mult),
            arg(4, Form, Constants),
            replace_var_by_const(F, Var, Const, New_F),
            recreate_formula(Var2, not New_F, Mult, Constants, Rule, New_Form)
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
    duplicate_term(Form, New_Form),
    set_arguments_in_function(New_Form, 0, Arity, New_Args).

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