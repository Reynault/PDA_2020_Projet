% Fichier test: check_conflicts

% True

% tests simples
:- check_conflicts(
    [a v b, not a],
    a
).

:- check_conflicts(
    [not a],
    a
).

:- check_conflicts(
    [a v b, [conflict, c], [conflict, b]],
    a
).

:- check_conflicts(
    [a v b, [conflict, b, not b], [conflict, a, not a]],
    a
).

:- check_conflicts(
    [a v b, [b, not a], [conflict, a, not a]],
    a
).

:- check_conflicts(
    [a v b, [conflict, b, not b], [a, not a]],
    a
).

:- check_conflicts(
    [a v b, [a, not a, not b], [c, a, not a]],
    a
).

% tests difficiles
:- check_conflicts(
    [not a v b],
    a
).