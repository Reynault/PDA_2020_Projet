% ----------------------------------------------------
% TP - PDA - Groupe : Brandon Hornbeck, Reynault Sies
% ----------------------------------------------------

% Fichier contenant les prédicats de vérification des données fournies par l'utilisateur.

% ----------------------------------------------------
% Prédicats de vérification des données fournies par l'utilisateur, on vérifie
% si elles correspondent bien à des formules propositionnelles
% ----------------------------------------------------

% Check propositionnal va parcourir l'arbre des formules
% et vérifier si elles sont valides
check_propositionnal([]).

check_propositionnal([First| Other]) :-
    \+is_list(First),
    check_propositionnal_formula(First),
    check_propositionnal(Other).

check_propositionnal([First| Other]) :-
    is_list(First),
    check_propositionnal(First),
    check_propositionnal(Other).

% Ce prédicat va vérifier si une formule est valide
check_propositionnal_formula(Form) :-
    rule(Form, A, B, Rule),
    \+is_composed(Rule),
    check_propositionnal_formula(A),
    check_propositionnal_formula(B).

check_propositionnal_formula(Form) :-
    \+rule(Form, _, _, _),
    atomic(Form).

% ----------------------------------------------------
% Prédicats de vérification des données fournies par l'utilisateur, on vérifie
% si elles correspondent bien à des formules du premier ordre
% ----------------------------------------------------

% Check propositionnal va parcourir l'arbre des formules
% et vérifier si elles sont valides
check_first_order([]).

check_first_order([First| Other]) :-
    \+is_list(First),
    check_propositionnal_formula(First),
    check_first_order(Other).

check_first_order([First| Other]) :-
    is_list(First),
    check_first_order(First),
    check_first_order(Other).

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