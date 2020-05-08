% ----------------------------------------------------
% TP - PDA - Groupe : Brandon Hornbeck, Reynault Sies
% ----------------------------------------------------

:- include('others/conf.pl').
:- include('others/operators.pl').
:- include('others/useful.pl').
:- include('others/rules.pl').
:- include('others/apply.pl').
:- include('others/verify.pl').

% ----------------------------------------------------
% Paramètres utilisés:
%
%   - tree : Tableau qui correspond aux branches réalisées 
%     C'est un tableau qui contient l'arbre sous la forme de formules et de tableaux.
%     Sachant que lorsqu'un conflit est détécté, le premier élément du tableau correspondant
%     à la branche est la constante conflict. 
%     Avec le tableau principal qui correspond à la branche principale.
%
%   - Form : Une formule du système 
%     (une formule simple)
%
% Notation utilisée:
%   - conflict  : constante qui tagge si une branche a un conflit
%   - marked    : opérateur qui permet de noter une formule déjà utilisée
% ----------------------------------------------------

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
    find_sub_branches([First| Others], B1, _),
    find_sub_branches(Constants, C1, _),
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
