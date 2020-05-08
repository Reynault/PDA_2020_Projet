% ----------------------------------------------------
% TP - PDA - Groupe : Brandon Hornbeck, Reynault Sies
% ----------------------------------------------------

% Fichier contenant les prédicats de vérification des données fournies par l'utilisateur.

% ----------------------------------------------------
% Prédicat de vérification des données fournies par l'utilisateur, on vérifie
% si elles correspondent bien à des formules propositionnelles
% ----------------------------------------------------

check_propositionnal([]).

check_propositionnal([First| Other]) :-
    \+is_list(First),
    \+rule(First, _, _, _),
    atomic(First),
    check_propositionnal(Other).

check_propositionnal([First| Other]) :-
    \+is_list(First),
    rule(First, A, B, Rule),
    \+is_composed(Rule),
    check_propositionnal(A),
    check_propositionnal(B),
    check_propositionnal(Other).

check_propositionnal([First| Other]) :-
    is_list(First),
    check_propositionnal(First),
    check_propositionnal(Other).

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