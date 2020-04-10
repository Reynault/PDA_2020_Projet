:- op(20,xfy,?=).

% Prédicats d'affichage fournis

% set_echo: ce prédicat active l'affichage par le prédicat echo
set_echo :- assert(echo_on).

% clr_echo: ce prédicat inhibe l'affichage par le prédicat echo
clr_echo :- retractall(echo_on).

% echo(T): si le flag echo_on est positionné, echo(T) affiche le terme T
%          sinon, echo(T) réussit simplement en ne faisant rien.

echo(T) :- echo_on, !, write(T).
echo().

%debut du projet

%verifie si 2 fonctions ont le meme nom et la meme arité
check_name_arity(F1,F2) :- functor(F1, NAME, ARITY), functor(F2, NAME, ARITY).

%ajoute l'élément X à L pour construire L1
ajout_element_liste(L,L1,X) :- L1 = [X|L].

%concatene 2 listes
concat([X|LIST1], L, [X|LIST2]):- concat(LIST1, L, LIST2).
concat([], L, L).

occur_check(V,T) :- var(V), var(T), V == T.
occur_check(V,T) :- 
	var(V),
	compound(T),
	functor(T, _, NMAX),
	occur_check_side(V,T,NMAX).

occur_check_side(V,T,N) :- 
	arg(N, T, A),
	occur_check(V, A), !;
	N > 1, N1 is N-1,
	occur_check_side(V,T,N1), !.
	

%predicat regle
regle(X ?= X, identity) :- atomic(X),!. %cas special, tomberait dans clash sinon
regle(F1 ?= F2, clash) :- compound(F1), compound(F2), \+check_name_arity(F1,F2), !.
regle(F1 ?= F2, clash) :- compound(F1), atomic(F2),!.
regle(F1 ?= F2, clash) :- compound(F2), atomic(F1),!.
regle(X ?= Y, check) :- var(X), compound(Y), occur_check(X,Y), !.
regle(X ?= Y, rename) :- var(X), var(Y), !.
regle(X ?= Y, simplify) :- var(X), atomic(Y), !.
regle(Y ?= X, orient) :- var(X), nonvar(Y), !.
regle(F1 ?= F2, decompose) :- compound(F1), compound(F2), check_name_arity(F1,F2), !.
regle(X ?= Y, expand) :- var(X), compound(Y), \+occur_check(X,Y), !.

%predicat reduit

%pour chaque règle, le predicat reduit teste si la regle s'applique, si elle s'applique, on l'applique et enfin on récupère Q.
reduit(identity, X ?= X, [X ?= X|LIST], Q) :- regle(X ?= X, identity),!,X=X,Q=LIST.
reduit(clash, F1 ?= F2, [F1 ?= F2|_LIST], Q) :- regle(F1 ?= F2,clash),!,Q=bottom.
reduit(check, X ?= Y, [X ?= X|_LIST], Q) :- regle(X ?= Y, check), !, X\==Y,Q=bottom.
reduit(rename, X?=Y, [X?=Y|LIST],Q) :- regle(X?=Y, rename),!, X=Y, Q=LIST.
reduit(simplify, X?=Y, [X?=Y|LIST],Q) :- regle(X?=Y, simplify),!, X=Y, Q=LIST.
reduit(orient, Y ?= X, [Y ?= X|LIST],Q) :- regle(Y?=X, orient),!, Q = [X ?= Y|LIST].
reduit(decompose, F1 ?= F2, [F1 ?= F2|LIST], Q) :- regle(F1 ?= F2, decompose), !, decompose(F1?=F2,LIST,Q).
reduit(expand, X ?= Y, [X ?= Y|LIST],Q) :- regle(X?=Y, expand),!, X=Y, Q=LIST. 


%ici pas besoin de vérifier que F1 et F2 sont des fonctions de meme nom et de meme arite car elle ne peut etre appelee que si cette condition est remplie
decompose(F1 ?= F2,LIST,Q) :- 
functor(F1,_,NMAX),
decompose_side(F1, F2, NMAX,LIST,Q).


%predicat secondaire utilisé pour la décomposition (récursif)
%La liste LIST est mise à jour avec la nouvelle équation à chaque passage dans le prédicat, Q est unifié à LIST au dernier passage (n=0)
decompose_side(F1,F2,N,LIST,Q) :-
arg(N,F1,A1), arg(N,F2,A2),
ajout_element_liste(LIST,LIST1,A1 ?= A2),
N1 is N-1,
decompose_side(F1,F2,N1,LIST1,Q), !.


%si on cherche le 0e argument, on retourne la liste actuelle dans Q pour pouvoir continuer l'unification
decompose_side(_,_,0,LIST,Q) :- Q = LIST.

%clash ou check peuvent retourner bottom, ce cas évite de tester toutes les règles alors qu'on sait déjà que l'unification est impossible.
unifie(bottom) :- false.

unifie([X ?= X | LIST]) :- reduit(identity, X ?= X, [X ?= X|LIST],Q),echo(identity), echo('\n'), unifie(Q),!.
unifie([F1 ?= F2 | LIST]) :- reduit(clash, F1 ?= F2, [F1 ?= F2 | LIST], Q), echo(clash), echo('\n'), unifie(Q), !.
unifie([X ?= Y | LIST]) :- reduit(check, X ?= Y, [X ?= Y|LIST],Q), echo(check), echo('\n'), unifie(Q),!.
unifie([X ?= Y | LIST]) :- reduit(rename, X ?= Y, [X ?= Y|LIST],Q), echo(rename), echo('\n'), unifie(Q),!.
unifie([X ?= Y | LIST]) :-reduit(simplify, X ?= Y, [X ?= Y|LIST],Q), echo(simplify), echo('\n'),unifie(Q),!.
unifie([Y ?= X | LIST]) :-reduit(orient, Y ?= X, [Y ?= X|LIST],Q), echo(orient), echo('\n'), unifie(Q),!.
unifie([F1 ?= F2 | LIST]) :- reduit(decompose, F1 ?= F2, [F1 ?= F2|LIST], Q), echo(decompose), echo('\n'), unifie(Q),!.
unifie([X ?= Y | LIST]) :- reduit(expand, X ?= Y, [X ?= Y|LIST],Q), echo(expand), echo('\n'), unifie(Q),!.


%unifier une liste vide est toujours réussi
unifie([]).

unifie([], choix_premier).
unifie(P,choix_premier) :- unifie(P),!.

unifie([], choix_pondere).
unifie(P,choix_pondere) :- choix_pondere(P,Q1,E,R), echo(R), echo('\n'), ajout_element_liste(Q1, Q2, E),reduit(R,E,Q2,Q),!, unifie(Q,choix_pondere),!.

choix_pondere([DEBUT|LIST], Q, E, R) :-  choix_pondere_side(LIST, Q, [], DEBUT,E, R),!.

choix_pondere_side([], Q, LISTE_PROVISOIRE, EQUATION_ACTUELLE, E, R) :- E = EQUATION_ACTUELLE, regle(E, R), Q = LISTE_PROVISOIRE.

choix_pondere_side([DEBUT|LIST],Q, LISTE_PROVISOIRE, EQUATION_ACTUELLE, E, R) :- regle(EQUATION_ACTUELLE, R1), regle(DEBUT,R2), poids(R1,P1), poids(R2,P2), P1 >= P2,
 ajout_element_liste(LISTE_PROVISOIRE, L1, DEBUT),
 choix_pondere_side(LIST, Q, L1, EQUATION_ACTUELLE, E, R),!.

choix_pondere_side([DEBUT|LIST],Q, LISTE_PROVISOIRE, EQUATION_ACTUELLE, E, R) :- regle(EQUATION_ACTUELLE, R1), regle(DEBUT,R2), poids(R1,P1), poids(R2,P2), P1 < P2,
 ajout_element_liste(LISTE_PROVISOIRE, L1, EQUATION_ACTUELLE),
 choix_pondere_side(LIST, Q, L1, DEBUT, E, R),!.

poids(identity, P) :- P is 8.
poids(clash, P) :- P is 7.
poids(check, P) :- P is 6.
poids(rename, P) :- P is 5.
poids(simplify, P) :- P is 4.
poids(orient, P) :- P is 3.
poids(decompose, P) :- P is 2.
poids(expand, P) :- P is 1.