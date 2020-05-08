% Tests pour la logique propositionnelle

% True

solve([a => b, b => c, not (a => c)],2).
solve([not (((a => b) => a) => a)],2).
solve([d, not a, not(d & (a=>b))],2).
solve([not d, not(a v not d)],2).
solve([r, p => (q & r), q => (not r), q],2).
solve([not b, not a, (a v b) v (a v b)],2).

% False

solve([a => b, b => c, not (a => d)],2).
solve([not(d & (a=>b))],2).
solve([not a, not(d & (a=>b))],2).
solve([(p v q) v r, p => (q & r), q => (not r)],2).

% Tests pour la logique du premier ordre