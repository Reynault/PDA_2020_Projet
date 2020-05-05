% Fichier test: close_conflicts

% True

% tests simples
:- close_conflicts([a, b, [b, c, not c], [not b]], [a, b, [b, c, not c], [not b]], ClosedTree).