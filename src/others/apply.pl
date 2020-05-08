% ----------------------------------------------------
% TP - PDA - Groupe : Brandon Hornbeck, Reynault Sies
% ----------------------------------------------------

% Fichier contenant les prédicats d'application des règles

% ----------------------------------------------------
% Prédicats apply: Permet d'appliquer une règle sur une formule
% ----------------------------------------------------

%cas simples où la branche ne contient pas de sous branche
apply(Form, Branch, New_Branch, Constants, New_Constants,_, Form, or) :- 
    no_sub_branch(Branch),!,
    rule(Form, F1, F2, or),
    append(Branch, [[F1]], Branch_Temp),
    append(Branch_Temp, [[F2]], New_Branch),

    append(Constants, [Constants], Tmp_Const),
    append(Tmp_Const, [Constants], New_Constants).

apply(Form, Branch, New_Branch, Constants, Constants,_, Form, nor):- 
    no_sub_branch(Branch),!, rule(Form, F1, F2, nor), append(Branch, [not F1, not F2], New_Branch).

apply(Form, Branch, New_Branch, Constants, Constants,_, Form, and):- 
    no_sub_branch(Branch),!, rule(Form, F1, F2, and), append(Branch, [F1, F2], New_Branch).

apply(Form, Branch, New_Branch, Constants, New_Constants,_, Form, nand):- 
    no_sub_branch(Branch),!,
    rule(Form, F1, F2, nand),
    append(Branch, [[not F1]], Branch_Temp),
    append(Branch_Temp, [[not F2]], New_Branch),

    append(Constants, [Constants], Tmp_Const),
    append(Tmp_Const, [Constants], New_Constants).

apply(Form, Branch, New_Branch, Constants, New_Constants ,_, Form, imp):- 
    no_sub_branch(Branch),!,
    rule(Form, F1, F2, imp),
    append(Branch, [[not F1]], Branch_Temp),
    append(Branch_Temp, [[F2]], New_Branch),

    append(Constants, [Constants], Tmp_Const),
    append(Tmp_Const, [Constants], New_Constants).

apply(Form, Branch, New_Branch, Constants, Constants,_, Form, nimp):- 
    no_sub_branch(Branch),!, rule(Form, F1, F2, nimp), append(Branch, [F1, not F2], New_Branch).

apply(Form, Branch, New_Branch, Constants, New_Constants, _, Form, exists) :- 
    no_sub_branch(Branch),!,
    rule(Form, Var, F, exists),

    count_constants(Constants, N),
    generate_constant(Constants, N, New_Constant),
    replace_var_by_const(F, Var, New_Constant, New_Form),

    append(Branch, [New_Form], New_Branch),
    append(Constants, [New_Constant], New_Constants).

apply(Form, Branch, New_Branch, Constants, New_Constants, _, New_Forall, forall) :- 
    no_sub_branch(Branch),!,
    rule(Form, Var, F, forall),
    arg(3, Form, Mult),
    arg(4, Form, Consumed_Constants),
    get_before_sub_branches(Constants, BeforeBranches),
    subtract(BeforeBranches, Consumed_Constants, Constants_To_Consume),
    % Two cases
    (
        % When nothing to consume
        isEmpty(Constants_To_Consume),
        % Creating one
        count_constants(Constants, N),
        generate_constant(Constants, N, New_Constant),
        % Replacing var by const
        replace_var_by_const(F, Var, New_Constant, New_Form),
        % Then adding new for, and new constant
        append(Consumed_Constants, [New_Constant], New_Constants_For_Form),
        New_Forall = forall(Var, F, Mult, New_Constants_For_Form),
        replace_form_in_branch(Branch, Changed_Branch, Form, New_Forall),
        append(Changed_Branch, [New_Form], New_Branch),
        append(Constants, [New_Constant], New_Constants)
        ;
        % When constants to consume
        \+isEmpty(Constants_To_Consume),
        % Consuming constants
        consume_constants(F, Var, Constants_To_Consume, New_Forms),
        append(Consumed_Constants, Constants_To_Consume, New_Constants_For_Form),
        New_Forall = forall(Var, F, Mult, New_Constants_For_Form),
        replace_form_in_branch(Branch, Changed_Branch, Form, New_Forall),
        append(Changed_Branch, New_Forms, New_Branch),
        New_Constants = Constants
    ).

apply(Form, Branch, New_Branch, Constants, Constants, Mult, Form, nexists) :- 
    no_sub_branch(Branch),!,
    rule(Form, Var, F, nexists),
    New_Form = forall(Var, not F, Mult, []),
    append(Branch, [New_Form], New_Branch).

apply(Form, Branch, New_Branch, Constants, Constants, _, Form, nforall) :- 
    no_sub_branch(Branch),!,
    rule(Form, Var, not F, nforall),
    New_Form = exists(Var, F),
    append(Branch, [New_Form], New_Branch).

%cas où la branche contient des sous branches
apply(Form, Branch, New_Branch, Constants, New_Constants, Mult, New_Form,  Rule) :- 
    \+no_sub_branch(Branch), 
    rule(Form, _, _, Rule), 

    find_sub_branches(Branch, B1, B2), 
    find_sub_branches(Constants, C1, C2),

    apply(Form, B1, New_B1, C1, New_C1, Mult, New_Form, Rule),
    apply(Form, B2, New_B2, C2, New_C2, Mult, New_Form, Rule),

    replace_branch(Branch, TempBranch, B1, New_B1),
    replace_branch(TempBranch, New_Branch, B2, New_B2),

    replace_branch(Constants, TempConstants, C1, New_C1),
    replace_branch(TempConstants, New_Constants, C2, New_C2).