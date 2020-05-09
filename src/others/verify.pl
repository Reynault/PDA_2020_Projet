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
    (atomic(Form); Form = not F, atomic(F)).

% ----------------------------------------------------
% Prédicats de vérification des données fournies par l'utilisateur, on vérifie
% si elles correspondent bien à des formules du premier ordre
% ----------------------------------------------------

% Check propositionnal va parcourir l'arbre des formules
% et vérifier si elles sont valides
check_first_order(Tree, Constants) :- 
    check_first_order(Tree, [], P, [], F),
    check_intersection(Constants, P),
    check_intersection(Constants, F).

check_first_order([], Predicates, Predicates, Functions, Functions).

check_first_order([First| Other], Predicates, New_Pred, Functions, New_Funct) :-
    \+is_list(First),
    check_first_order_formula(First, Predicates, Tmp_New_Pred, Functions, Tmp_New_Funct, []),
    check_first_order(Other, Tmp_New_Pred, New_Pred, Tmp_New_Funct, New_Funct).

check_first_order([First| Other], Predicates, New_Pred, Functions, New_Funct) :-
    is_list(First),
    check_first_order(First, Predicates, Temp_New_Pred, Functions, Temp_New_Funct),
    check_first_order(Other, Temp_New_Pred, New_Pred, Temp_New_Funct, New_Funct).

check_first_order_formula(Form, Predicates, New_Pred, Functions, New_Funct, Var) :-
    rule(Form, A, B, Rule),
    \+is_composed(Rule),
    check_first_order_formula(A, Predicates, Tmp_New_Pred, Functions, Temp_New_Funct, Var),
    check_first_order_formula(B, Tmp_New_Pred, New_Pred, Temp_New_Funct, New_Funct, Var).

check_first_order_formula(Form, Predicates, New_Pred, Functions, New_Funct, Var) :-
    rule(Form, V, F, Rule),
    is_composed(Rule),
    append([V], Var, New_Var),
    check_first_order_formula(F, Predicates, New_Pred, Functions, New_Funct, New_Var).

check_first_order_formula(Form, Predicates, New_Pred, Functions, New_Funct, Var) :-
    \+rule(Form, _, _, _),
    compound(Form),
    functor(Form, Name, Arity),
    F = [Name, Arity],
    \+already_exists(F, Functions, _),
    (
        \+already_exists(F, Predicates, _), append([F], Predicates, Tmp_New_Pred)
        ;
        already_exists(F, Predicates, A), A == Arity, Tmp_New_Pred = Predicates
    ),
    compound_name_arguments(Form, _, Args),
    check_first_order_function(Args, Tmp_New_Pred, New_Pred, Functions, New_Funct, Var).

check_first_order_function([], Predicates, Predicates, Functions, Functions, _).

check_first_order_function([First| Others], Predicates, New_Pred, Functions, New_Funct, Var) :-
    \+compound(First),
    var(First),
    is_close(First, Var),
    check_first_order_function(Others, Predicates, New_Pred, Functions, New_Funct, Var).

check_first_order_function([First| Others], Predicates, New_Pred, Functions, New_Funct, Var) :-
    \+compound(First),
    atomic(First),
    check_first_order_function(Others, Predicates, New_Pred, Functions, New_Funct, Var).

check_first_order_function([First| Others], Predicates, New_Pred, Functions, New_Funct, Var) :-
    compound(First),
    functor(First, Name, Arity),
    F = [Name, Arity],
    \+already_exists(F, Predicates, _),
    (
        \+already_exists(F, Functions, _), append([F], Functions, Tmp_Functions1)
        ;
        already_exists(F, Functions, A), A == Arity, Tmp_Functions1 = Functions
    ),
    compound_name_arguments(First, _, Args),
    check_first_order_function(Args, Predicates, Tmp_New_Pred, Tmp_Functions1, Tmp_Functions2, Var),
    check_first_order_function(Others, Tmp_New_Pred, New_Pred, Tmp_Functions2, New_Funct, Var).

is_close(V, [First| Others]) :- 
    (
        same_term(V, First)
        ;
        \+same_term(V, First), is_close(V, Others)
    ).

already_exists([Name, _], [First| _], A) :-
    First = [N, A],
    Name == N.

already_exists([Name| Arity], [First| Others], A) :-
    First = [N, _],
    Name \= N,
    already_exists([Name| Arity], Others, A).


check_intersection([], _).

check_intersection([First| Other], P) :-
    \+is_list(First),
    F = [First, 0],
    \+already_exists(F, P, _),
    check_intersection(Other, P).

check_intersection([First| Other], P) :-
    is_list(First),
    check_intersection(First, P),
    check_intersection(Other, P).