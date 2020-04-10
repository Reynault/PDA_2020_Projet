% Test File

% Rename
reduit(rename, Z ?= X, [Z ?= X, W ?= f(Z,c,b), Y ?= Z], Q).
reduit(rename, Z ?= X, [Z ?= X, X ?= f(Z,c,b), Y ?= Z], Q).

% Decompose
unifie([f(X, d, a) ?= f(Z, c, b), Z ?= X, Y ?= Z]).

% Orient
reduit(orient, f(a, b, c) ?= A, [f(a, b, c) ?= A, f(A, d, a) ?= f(Z, c, b), Z ?= X, Y ?= A], Q).

% Unifie
unifie([f(X,Y) ?= f(g(Z),h(a)), Z ?= f(Y)]).
unifie([f(X,Y) ?= f(g(Z),h(a)), Z ?= f(X)]).

% Clash
unifie([f(a,b,c) ?= g(a,b,c), f(X, g(Y, Z), a) ?= f(g(V, Z), X, Z)]).   % Bon exemple pour montrer la différence pondéré et inverse
unifie([g(b,c) ?= g(a,b,c)]).
unifie([f(b,a) ?= g(a,b,c)]).
unifie([g(b,X) ?= g(a,b,c)]).
unifie([f(Y,Z) ?= f(Y,X)]).

% effacement
unifie([f(X, g(Y, Z), a) ?= f(g(V, Z), X, Z)]).
unifie([f(X, g(Y, Z), a) ?= f(g(v, Z), X, Z)]).

% Boucle Orient
unifie([f(X, Y, g(a, a)) ?= f(g(Y, Y), Z, Z)]).
unifie([f(X, Y, g(a, a)) ?= f(Y, g(Z, Z), Z)]).

% Size
unifie([f(X1, X2, X3, X4, X5, X6, X7, X8, X9, X10) ?= f(g(X0, X0), g(X1, X1), g(X2, X2), g(X3, X3), g(X4, X4), g(X5, X5), g(X6, X6), g(X7, X7), g(X8, X8), g(X9, X9))]).