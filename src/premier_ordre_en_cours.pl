
:- op(1,fx ,not) . % not
:- op(2,xfy,&)   . % and
:- op(3,xfy,v)   . % or
:- op(4,xfy,=>)  . % implication
:- op(5,xfy,<=>) . % equality

%   forall(X, man(X))
%   exists(X, man(X))

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

apply(Form, Branch, New_Branch, _, _, _, _, nexists) :- no_sub_branch(Branch),!, rule(Form, Var, F, nexists), append(Branch, [F], New_Branch).
apply(Form, Branch, New_Branch, _, _, _, _, nforall) :- no_sub_branch(Branch),!, rule(Form, Var, F, nforall), append(Branch, [F], New_Branch).

apply(Form, Branch, New_Branch, Constants, ToConsume, New_Constants, New_ToConsume, forall) :-
    no_sub_branch(Branch),!, rule(Form, Var, F, forall).

apply(Form, Branch, New_Branch, Constants, ToConsume, New_Constants, New_ToConsume, exists) :-
    no_sub_branch(Branch),!, rule(Form, Var, F, exists),
    generateConstant(Constants, New_Constants, New_Constant),
    replaceVariable(Var, New_Constant, F, NewForm),
    append(Branch, [NewForm], Branch_Temp).

%cas où la branche contient des sous branches
apply(Form, Branch, New_Branch, Constants, New_Constants, Rule) :- 
    \+no_sub_branch(Branch), 
    rule(Form, _, _, Rule), 
    find_sub_branches(Branch, B1, B2), 
    apply(Form, B1, NB1, Rule), 
    apply(Form, B2, NB2, Rule),
    remove(B1, Branch, Branch_Temp1), remove(B2, Branch_Temp1, Branch_Temp2),
    append(Branch_Temp2, [NB1], Branch_Temp3), append(Branch_Temp3, [NB2], New_Branch).

replaceVariable(Var, Const, Form, NewForm) :-
    Var = Const,
    Form = NewForm.

generateConstant(Constants, NewConstants, NewConstant) :-
    nat(NewConstant),
    member(NewConstant, Constants),
    generateConstant(Constants, NewConstants, NewConstant).

generateConstant(Constants, NewConstants, NewConstant) :-
    nat(NewConstant),
    \+member(NewConstant, Constants),
    append(Constants, NewConstant, NewConstants).

findConstants(Tree, Constants).

findAndUpdateMarked(Form, Marked, New_Marked).




%--------------- EXISTE DEJA
get_before_sub_branches([First| _], BeforeBranches) :- 
    is_list(First),
    BeforeBranches = [].

get_before_sub_branches([First| Others], BeforeBranches) :- 
    \+is_list(First),
    get_before_sub_branches(Others, B),
    append([First], B, BeforeBranches).

no_sub_branch([]).
no_sub_branch([First|Others]) :- \+is_list(First), no_sub_branch(Others).

find_sub_branches([First|Others], B1, B2) :- is_list(First), B1 = First, find_sub_branches(Others, B2).
find_sub_branches([First|Others], B1, B2) :- \+is_list(First), find_sub_branches(Others, B1, B2).

find_sub_branches([First|_], B2) :- is_list(First), B2 = First.
find_sub_branches([First|Others], B2) :- \+is_list(First), find_sub_branches(Others, B2).

remove(_, [], []).
remove(List, List, []).
remove(X, [X|Others], R1) :- remove(X, Others, R1).
remove(X, [Y|Others], R1) :- X \== Y, length(Others, N), N > 0, remove(X, Others, R2), append([Y], R2, R1).
remove(X, [Y|Others], R1) :- X \== Y, length(Others, 0), R1 = [Y].