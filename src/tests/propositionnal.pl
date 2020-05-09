% Tests pour la logique propositionnelle

% True

solve([a => b, b => c, not (a => c)],propositionnal).
solve([not (((a => b) => a) => a)],propositionnal).
solve([d, not a, not(d & (a=>b))],propositionnal).
solve([not d, not(a v not d)],propositionnal).
solve([r, p => (q & r), q => (not r), q],propositionnal).
solve([not b, not a, (a v b) v (a v b)],propositionnal).

% False

solve([a => b, b => c, not (a => d)],propositionnal).
solve([not(d & (a=>b))],propositionnal).
solve([not a, not(d & (a=>b))],propositionnal).
solve([(p v q) v r, p => (q & r), q => (not r)],propositionnal).
solve([],propositionnal).