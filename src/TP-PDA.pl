% ----------------------------------------------------
% TP - PDA - Groupe : Brandon Hornbeck, Reynault Sies
% ----------------------------------------------------

% ----------------------------------------------------
% Opérateur ?=

:- op(20,xfy,?=).

% ----------------------------------------------------
% Prédicats d'affichage fournis

% set_echo: ce prédicat active l'affichage par le prédicat echo
set_echo :- assert(echo_on).

% clr_echo: ce prédicat inhibe l'affichage par le prédicat echo
clr_echo :- retractall(echo_on).

% echo(T): si le flag echo_on est positionné, echo(T) affiche le terme T
%          sinon, echo(T) réussit simplement en ne faisant rien.

echo(T) :- echo_on, !, write(T).
echo(_).

% ----------------------------------------------------
% Configuration pré-éxecution

:- style_check(-discontiguous).
:- set_echo.

% ----------------------------------------------------
% Question n°1 : Mise en place du prédicat Unifie avec les deux prédicats
% regle et reduit. (et occur_check)
% ----------------------------------------------------

% ----------------------------------------------------
% Prédicat Règle permettant de trouver la règle à appliquer
% ----------------------------------------------------

% ----------------------------------------------------
% Règle remove qui permet d'enlever une équation composée 
% des deux mêmes termes, telles que X ?= X, a ?= a, f(a) ?= f(a)
%
% Ce prédicat ne figurait pas dans les règles de bases, mais
% a été ajouté suite à la découverte des cas présentés.
% ----------------------------------------------------
regle(X ?= T, remove) :-
    X == T,
    !.

% ----------------------------------------------------
% Regle check associée au test d'occurence, qui est vrai 
% s'il y a X dans T
%
% Le prédicat Règle utilise le prédicat occur_check présenté
% en dessous
regle(X ?= T, check) :-
    \+occur_check(X, T),
    !.

% ----------------------------------------------------
% Test d'occurence (Vrai si V ne se trouve pas dans T)

% Si on compare (V) a une variable (T) alors on sait que V ne peut pas se trouver dans le
% terme T car c'est une variable, on peux donc stopper les autres prédicats avec !. Il faut alors vérifier
% si V != T, auquel cas le prédicat renvoie Vrai. Sinon, cela signifie qu'il y a une occurrence
% de V dans T.
occur_check(V, T) :-
    var(T),!,
    V \== T,
    !.

% Si T est un terme alors il faut parcourir ses éléments afin de vérifier que V ne se trouve pas dedans.
% Pour cela, on récupère le nombre d'arguments avec functor, puis on parcourt la fonction.
occur_check(V, T):-
    % Récupération du nombre de termes de la fonction
    functor(T, _, Termes),
    % Puis on parcourt dans le terme
    occur_check_parcours(V, T, Termes). 

% Prédicat de parcours d'occur_check, le cas initial arrête le parcours dans
% le cas où le numéro d'argument est égal à 0
occur_check_parcours(_, _, 0) :-
    !.

% Prédicat de parcours d'occur_check, on récupère le ième argument, puis on
% réalise la vérification grâce au prédicat occur_check.
% On vérifie également le ième argument moins un.
occur_check_parcours(V, Fonc, Arite) :-
    % Décrémentation du nombre d'arité pour vérifier un autre argument
    New is Arite - 1,
    % Vérification de l'argument - 1
    occur_check_parcours(V, Fonc, New),
    % Récupération de l'argument courant
    arg(Arite, Fonc, Arg),
    % Vérification avec le prédicat occur_check
    occur_check(V, Arg),
    !.



% ----------------------------------------------------
% Occur check avec des listes
%
% Cette version d'occur_check a été réalisée en
% utilisant uniquement les listes de prolog

% Si T est un terme alors il faut parcourir ses éléments afin de vérifier que V ne se trouve pas dedans.
% On transforme alors T en liste et on parcours la liste.

%occur_check(V, T):-
%    T =.. [ _| Termes],
%    occur_check_parcours(V, Termes).*/

% Prédicat qui permet de mettre fin à la récurrence quand la liste est vide.
%occur_check_parcours(_, []) :-
%    !.

% Prédicat de parcours d'une liste de paramètres qu'il faut alors tester un à un.

%occur_check_parcours(V, [Element | Termes]):-
%    occur_check(V, Element),
%    occur_check_parcours(V, Termes).*/
% ----------------------------------------------------



% ----------------------------------------------------
% Clash

% Règle clash, on vérifie deux choses, le nom des deux fonctions est différent ou le nombre
% d'arité est différent.

% Règle de vérification du nom
regle(Func1 ?= Func2, clash) :-
    % Vérification que les deux éléments sont des fonctions
    compound(Func1),
    compound(Func2),
    % Vérification du nom
    functor(Func1, Name1, _),
    functor(Func2, Name2, _),
    % Nom différent
    Name1 \== Name2,
    !.

% Règle de vérification du nombre d'arité
regle(Func1 ?= Func2, clash) :-
    % Vérification que les deux éléments sont deux fonctions
    compound(Func1),
    compound(Func2),
    % Récupération du nombre d'arité
    functor(Func1, _, Arity1),
    functor(Func2, _, Arity2),
    % Nombre d'arité différent
    Arity1 \== Arity2,
    !.

% ----------------------------------------------------
% Rename (Vrai si on peut appliquer la règle)

% On vérifie si les deux parties de l'équation sont deux variables
% auquel cas, on peut appliquer la règle.
regle(X ?= T, rename) :-
    var(X),
    var(T),
    !.

% ----------------------------------------------------
% Simplifie

% Règle de simplification, on vérifie si, le premier terme X, est une variable
% et si le terme T est une constante.
regle(X ?= T, simplify) :-
    var(X), atomic(T),
    !.

% ----------------------------------------------------
% Orient

% Règle orient, on vérifie si X est une variable et T n'en n'est pas une.
% 
% Le sens est important puisqu'il faut appliquer orient, dans le cas où
% ce qui se trouve à gauche n'est pas une variable, et ce qui est à droite
% en est une.
regle(T ?= X, orient) :-
    nonvar(T), var(X),
    !.

% ----------------------------------------------------
% Decompose

% Règle de décomposition, cette règle peut s'appliquer dans le cas où les deux
% symboles de fonction sont les mêmes. (même nom et même nombre de paramètres)
regle(Func1 ?= Func2, decompose) :-
    % Vérification que les deux éléments sont des fonctions
    compound(Func1),
    compound(Func2),
    % Application de functor pour récupérer le nom, et l'arité
    functor(Func1, Name1, Arity1),
    functor(Func2, Name2, Arity2),
    % Vérification du nom et de l'arité
    Name1 == Name2,
    Arity1 == Arity2,
    !.

% ----------------------------------------------------
% Expand

% La règle expand permet de savoir si on peut appliquer expand, pour cela
% il faut vérifier si X est une variable, si T est composé, et si X n'est pas
% dans T, avec l'occur check précédemment défini.
regle(X ?= T, expand) :-
    var(X),
    compound(T),
    occur_check(X, T),
    !.



% ----------------------------------------------------
% Prédicat Reduit permettant de réduire le système d'équation P en utilisant la règle R
% ----------------------------------------------------

% ----------------------------------------------------
% Reduit de la règle remove
%
% Ce prédicat ne réalise aucunes actions, puisque l'intérêt de la
% règle remove est uniquement d'enlever une équation telle que X ?= X, où a ?= a.
%
% Cette opération est déjà réalisée au moment de l'appel du prédicat réduit dans
% le prédicat unifie.
reduit(remove, _, P, Q) :-
    Q = P,
    !.

% ----------------------------------------------------
% Rename/ Expand/ Simplify

% Prédicat réduit pour la règle rename, il applique le renommage sur
% le programme P en fonction de l'équation E, et rend le résultat
% dans Q, il utilise le prédicat elimination qui réalise l'unification.
reduit(rename, X ?= T, P, Q) :-
    elimination(X ?= T, P, Q),
    !.

% Prédicat réduit pour la règle expand, il applique l'extension sur
% le programme P en fonction de l'équation E, et rend le résultat
% dans Q, il utilise le prédicat elimination qui réalise l'unification.
reduit(expand, X ?= T, P, Q) :-
    elimination(X ?= T, P, Q),
    !.

% Prédicat réduit pour la règle simplify, il applique la simplification sur
% le programme P en fonction de l'équation E, et rend le résultat
% dans Q, il utilise le prédicat elimination qui réalise l'unification.
reduit(simplify, X ?= T, P, Q) :-
    elimination(X ?= T, P, Q),
    !.

% Prédicat elimination qui permet d'appliquer l'unification nécéssaire 
% aux règles rename, expand et simplify
elimination(X ?= T, P, Q) :-
    % Unification avec la nouvelle valeur de X
    X = T,
    % Q devient alors le reste du programme
    Q = P,
    !.

% ----------------------------------------------------
% Decompose

% Prédicat reduit qui permet d'appliquer la règle decompose sur l'équation E.
% On ajoute alors au programme P les nouvelles équations, le résultat est placé dans Q.
reduit(decompose, Fonc1 ?= Fonc2, P, Q) :-
    % Récupération du nombre d'arguments
    functor(Fonc1, _, Arite),
    % Récupération des nouvelles équations
    decompose(Fonc1, Fonc2, Arite, Liste),
    % Ajout de celles-ci dans le programme P
    append(Liste, P, Q),
    !.

% Prédicat de decomposition, cas initial où l'argument
% des deux fonctions parcourues est 0. (On stoppe la récursion)
decompose(_, _, 0, _) :-
    !.

% Prédicat de decomposition, on prend deux fonctions et on récupère le ième argument
% afin d'ajouter l'équation Arg1 ?= Arg2 au programme.
decompose(Fonc1, Fonc2, Arite, Liste) :-
    % Décrémentation du numéro de l'argument parcouru
    New is Arite - 1,
    % Ajout de l'équation liée au ième - 1 argument
    decompose(Fonc1, Fonc2, New, Res),
    % Récupération de l'argument courant pour les deux fonctions
    arg(Arite, Fonc1, Arg1),
    arg(Arite, Fonc2, Arg2),
    % Ajout de l'équation arg1 ?= arg2
    append(Res, [Arg1 ?= Arg2], Liste),
    !.



% ----------------------------------------------------
% Decompose avec les listes


% Prédicat reduit qui permet d'appliquer la règle decompose sur l'équation E.
% On ajout alors au programme P les nouvelles équations, le résultat est placé dans Q.
/*reduit(decompose, Fonc1 ?= Fonc2, P, Q) :-
    % Récupération des arguments
    Fonc1 =.. [_| Param1],
    Fonc2 =.. [_| Param2],

    % Ajout des nouvelles équations
    decompose(Param1, Param2, Liste),
    % Ajout de la liste dans le programme P
    append(Liste, P, Q),
    !.
*/

% Prédicat de decomposition, cas initial où les deux listes des
% arguments sont vides.
/*decompose([], [], _) :-
    !.
*/

% Prédicat de decomposition, on prend deux listes correspondant aux paramètres des deux fonctions.
% On ajoute ensuite la nouvelle équations à une autre liste, de sorte à cumuler toutes les
% équations.
/*decompose([Arg1| Args1], [Arg2| Args2], Liste) :-
    decompose(Args1, Args2, Temp),
    append([Arg1 ?= Arg2], Temp, Liste),
    !.
*/
% ----------------------------------------------------



% ----------------------------------------------------
% Orient

% Prédicat reduit pour la règle orient, le prédicat prend l'équation E et l'inverse
% puis l'ajoute au programme P, le résulat est alors stocké dans Q
reduit(orient, X ?= T, P, Q) :-
    % Ajout dans P de l'équation inversée
    append([X ?= T], P, Q),
    !.

% ----------------------------------------------------
% Unifie
% ----------------------------------------------------

% Unifie sans stratégie (Question 1)

% Prédicat initial de l'unification, qui ne fait rien
% et arrête la récursion
%
% Prédicat Vrai lorsque le programme est vide
unifie([]) :-
    echo("\n"), echo("Yes"),
    !.

% Prédicat principal de l'unification, qui,
%
%   - Prend la première équation du programme P
%     et récupère la règle à appliquer avec règle.
%
%   - Puis applique cette règle avec reduit.
%
%   - Et recommence sur le reste du programme
%
unifie(Programme) :-
    % Récupération de la première équation
    Programme = [X| P],
    % Affichage
    echo("system:   "), echo(Programme), echo("\n"),
    % Récupération de la règle R à appliquer
    regle(X, R),
    % Affichage
    echo(R), echo(":   "), echo(X), echo("\n"),
    % Réduction du programme en appliquant la règle R
    reduit(R, X, P, Q),
    % Unification sur le reste du programme
    unifie(Q),
    !.



% ----------------------------------------------------
% Question n°2: ajout de la notion de stratégie à appliquer
% lors de l'unification.
%
% Plusieurs stratégies ont été implémentées:
%   - Choix_premier
%   - Choix_pondere
%   - Choix_inverse
%   - Choix_aleatoire
% ----------------------------------------------------

% Prédicat unifie de fin de récursion
% lorsque le programme est vide. 
unifie([], _) :-
    echo("\n"), echo("Yes"),
    !.



% ----------------------------------------------------
% Unifie avec choix_premier
% ----------------------------------------------------

% Unification avec choix_premier, on prend la première
% équation du programme, on récupère la règle à appliquer,
% puis on réduit le programme.
unifie(P, choix_premier) :-
    % Affichage
    echo("system:   "), echo(P), echo("\n"),
    % Récupération de la première équation et de la règle associée
    choix_premier(P, Q, E, R),
    % Affichage
    echo(R), echo(":   "), echo(E), echo("\n"),
    % Application de la règle sur le programme
    reduit(R, E, Q, Resultat),
    % Puis unification sur le reste
    unifie(Resultat, choix_premier),
    !.

% ----------------------------------------------------
% Choix_premier

% Le prédicat choix_premier récupère la première équation
% du programme P, puis choisi la règle de celle si.
%
% R devient la règle choisie sur l'équation E
% P devient le système Q
choix_premier([PremiereEquation| P], Q, E, R) :-
    % E devient la première équation
    E = PremiereEquation,
    % On retrouve la règle à effectuer
    regle(E, R),
    % Q devient le programme sans la première équation
    Q = P,
    !.



% ----------------------------------------------------
% Unifie avec choix_pondere
% ----------------------------------------------------

% Unification avec choix_pondere, cette stratégie associe
% à chaque règle un poids, et lors de chaque étape de l'unification,
% choisie l'équation avec la règle qui a le poids le plus important.
%
% Dans notre implémentation, plus le poids est petit, plus il est important.
unifie(P, choix_pondere) :-
    % Affichage
    echo("system:   "), echo(P), echo("\n"),
    % Récupération de l'équation et de sa règle
    choix_pondere(P, Q, E, R),
    % Affichage
    echo(R), echo(":   "), echo(E), echo("\n"),
    % Réduction
    reduit(R, E, Q, Resultat),
    % Puis unification sur le reste
    unifie(Resultat, choix_pondere),
    !.

% ----------------------------------------------------
% Choix_pondere

% Prédicat choix_pondere qui permet de prendre un programme P,
% d'associer pour chaque équation une règle avec son poids,
% de prendre l'équation avec la règle la plus importantes (E et R),
% et de la supprimer de P pour obtenir Q.
choix_pondere(P, Q, E, R) :-
    % Prédicat permettant de récupérer la liste des équations avec une pondération
    recupRegle(P, Regles),
    % Application du trie pour récupérer en premier élément, l'équation avec le poids le plus important (petit)
    sort(1, @=<, Regles, [Equation| _]),
    % E devient l'équation cible
    Equation = [Poids, E],
    % Récupération de la règle R avec la pondération
    ponderationVersRegle(Poids, R),
    % Suppression de l'équation E dans P pour obtenir Q
    delete(P, E, Q),
    !.

% ----------------------------------------------------
% recupRegle

% Prédicat de récupération des règles, cas initial lorsque
% le programme est vide
recupRegle([], Regles) :-
    Regles = [].

% Prédicat de récupération des règles, l'argument Regles
% devient une liste contenant des sous-listes de taille 2, avec
% [ Pondération, Équation ]
recupRegle([E| P], Regles) :-
    % Récupération pour le reste du programme
    recupRegle(P, New),
    % Récupération de la règle pour l'équation courante
    regle(E, R),
    % Pondération de l'équation courante
    ponderer(R, Poids),
    % Ajout dans la liste
    append([[Poids, E]], New, Regles),
    !.

% ----------------------------------------------------
% Ponderer

% Ponderer est un prédicat qui pour une règle donnée,
% fourni une pondération.
%
% Les pondérations ont été réalisées en suivant le sujet.
% Pour la règle ajoutée, le choix de pondération est
% expliqué dans le rapport.

ponderer(remove, Poids) :-
    Poids = 0,
    !.

ponderer(clash, Poids) :-
    Poids = 1,
    !.

ponderer(check, Poids) :-
    Poids = 2,
    !.

ponderer(rename, Poids) :-
    Poids = 3,
    !.

ponderer(simplify, Poids) :-
    Poids = 4,
    !.

ponderer(orient, Poids) :-
    Poids = 5,
    !.

ponderer(decompose, Poids) :-
    Poids = 6,
    !.

ponderer(expand, Poids) :-
    Poids = 7,
    !.

% ----------------------------------------------------
% ponderationVersRegle

% Ce prédicat permet de passer des pondérations aux règles
ponderationVersRegle(Num, R) :-
    ponderer(R, Num),
    !.



% ----------------------------------------------------
% Unifie avec choix aléatoire
% ----------------------------------------------------

% Prédicat d'unification en utilisant un choix aléatoire.
%
% Cette stratégie a pour but de voir si le choix
% aléatoire des règles permet d'avoir en moyenne
% une efficacité importante.
unifie(P, choix_aleatoire) :-
    % Affichage
    echo("system:   "), echo(P), echo("\n"),
    % Choix aléatoire de la règle R à appliquer dans le programme P
    choix_aleatoire(P, Q, E, R),
    % Affichage
    echo(R), echo(":   "), echo(E), echo("\n"),
    % Réduction du programme sur l'équation E avec la règle R
    reduit(R, E, Q, Resultat),
    % Unification sur le reste du programme P
    unifie(Resultat, choix_aleatoire),
    !.

% ----------------------------------------------------
% Choix aléatoire

% Le prédicat choix aléatoire récupère une valeur aléatoire entre
% 0 et la taille du programme.
%
% Il récupère ensuite l'équation E pointée par la valeur aléatoire
% et récupère la règle R qui peut s'appliquer sur E.
%
% Puis donne à Q le programme P sans l'équation E.
choix_aleatoire(P, Q, E, R) :-
    % Récupération de la taille de la liste
    length(P, Taille),
    % Pour récupérer un aléatoire qui indique une équation dans le programme
    random(0, Taille, Aleatoire),
    % On récupère ensuite cette équation
    recupElement(P, 0, Aleatoire, E),
    % Et on récupère la règle associée
    regle(E, R),
    % Q devient alors P moins E
    delete(P, E, Q),
    !.

% ----------------------------------------------------
% recupElement

% Le prédicat recupElement permet de récupérer l'élément pointé par
% l'entier Aleatoire dans le programme P.

% Cas initial dans lequel le programme P est vide
recupElement([], _, _, _).

% Cas principal dans lequel on regarde si la kième équation est 
% celle qu'on recherche avec le nombre aléatoire 
recupElement([E| P], K, Aleatoire, Element) :-
    % Si K est égal à Aleatoire, alors Element devient l'équation courante
    K == Aleatoire -> Element = E, !;
    % Sinon, incrémentation
    K1 is K + 1,
    % Et on cherche dans la suite du programme
    recupElement(P, K1, Aleatoire, Element),
    !.



% ----------------------------------------------------
% Unifie avec choix inversé
% ----------------------------------------------------

% ----------------------------------------------------
% Prédicat unifie avec stratégie choix_inverse

% Ce predicat permet de réaliser un choix inversé par rapport à la pondération
% proposée pour l'unification avec stratégie de choix pondéré.
%
% Unifie utilise le prédicat choix_inversé qui va trier dans le sens inverse
% les ponderations pour récupérer la règle avec la pondération la plus grande.
unifie(P, choix_inverse) :-
    % Affichage
    echo("system:   "), echo(P), echo("\n"),
    % Récupération de l'équation avec la règle avec le poids le moins important
    choix_inverse(P, Q, E, R),
    % Affichage
    echo(R), echo(":   "), echo(E), echo("\n"),
    % Réduction du programme
    reduit(R, E, Q, Resultat),
    % Puis unification du reste
    unifie(Resultat, choix_inverse),
    !.

% ----------------------------------------------------
% Choix inversé

% Choix_inverse permet de récupérer les pondération des règles
% associées pour chaque équations du programme P, puis de
% les trier par ordre décroissant sur la pondération.
%
% Enfin, E devient l'équation avec la pondération la plus grande,
% et R sa règle.
choix_inverse(P, Q, E, R) :-
    % Récupération des pondérations
    recupRegle(P, Regles),
    % Trie décroissant
    sort(1, @>=, Regles, [Equation| _]),
    % Récupération de l'équation avec le poids le plus grand
    Equation = [Poids, E],
    % Puis récupération de la règle avec le poids
    ponderationVersRegle(Poids, R),
    % Et suppression de E dans P pour obtenir Q
    delete(P, E, Q),
    !.



% ----------------------------------------------------
% Question n°3
% ----------------------------------------------------

% ----------------------------------------------------
% Prédicat unif

% Utilisation de l'algorithme sans l'affichage des echos
unif(P, S) :-
    % Appel du prédicat permettant d'enlever l'affichage des echo
    clr_echo,
    % Puis appel du prédicat unifie
    unifie(P, S).

% ----------------------------------------------------
% Prédicat trace_unif

% Utilisation de l'algorithme avec l'affichage
trace_unif(P, S) :-
    % Appel du prédicat permettant d'ajouter l'affichage des echo
    set_echo,
    % Puis appel du prédicat unifie
    unifie(P, S).


% ---------------------- FIN QUESTION N°1 : Execution de l'algorithme sur les deux exemples fournis dans le sujet

/*

Utilisation de la stratégie : Choix_premier

Commande :

    ?- unifie([f(X,Y) ?= f(g(Z),h(a)), Z ?= f(Y)], choix_premier).

Résultat :

    system:   [f(_4736,_4738)?=f(g(_4742),h(a)),_4742?=f(_4738)]
    decompose:   f(_4736,_4738)?=f(g(_4742),h(a))
    system:   [_4736?=g(_4742),_4738?=h(a),_4742?=f(_4738)]
    expand:   _4736?=g(_4742)
    system:   [_4738?=h(a),_4742?=f(_4738)]
    expand:   _4738?=h(a)
    system:   [_4742?=f(h(a))]
    expand:   _4742?=f(h(a))

    Yes
    X = g(f(h(a))),
    Y = h(a),
    Z = f(h(a)).

Commande :

    ?- unifie([f(X,Y) ?= f(g(Z),h(a)), Z ?= f(X)], choix_premier).

Résultat :

    system:   [f(_4736,_4738)?=f(g(_4742),h(a)),_4742?=f(_4736)]
    decompose:   f(_4736,_4738)?=f(g(_4742),h(a))
    system:   [_4736?=g(_4742),_4738?=h(a),_4742?=f(_4736)]
    expand:   _4736?=g(_4742)
    system:   [_4738?=h(a),_4742?=f(g(_4742))]
    expand:   _4738?=h(a)
    system:   [_4742?=f(g(_4742))]
    check:   _4742?=f(g(_4742))
    false.
*/