% ----------------------------------------------------
% TP - PDA - Groupe : Brandon Hornbeck, Reynault Sies
% ----------------------------------------------------

% Fichier contenant les prédicats de vérification des règles

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

rule(CF, A, B, nforall) :- \+var(CF), CF = not Form, rule(Form, A, B1, forall), B1 \= not _, B = not B1.
rule(CF, A, B, nexists) :- \+var(CF), CF = not Form, rule(Form, A, B1, exists), B1 \= not _, B = not B1.
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