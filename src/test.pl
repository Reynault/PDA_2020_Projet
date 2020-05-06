% Tests pour la logique propositionnelle

% True

solve([a => b, b => c, not (a => c)]).
solve([not (((a => b) => a) => a)]).
solve([d, not a, not(d & (a=>b))]).
solve([not d, not(a v not d)]).
solve([r, p => (q & r), q => (not r), q]).

% False

solve([a => b, b => c, not (a => d)]).
solve([not(d & (a=>b))]).
solve([not a, not(d & (a=>b))]).
solve([(p v q) v r, p => (q & r), q => (not r)]).

% Tests pour la logique du premier ordre