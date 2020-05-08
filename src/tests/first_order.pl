solve([not (exists(X,p(X) v q(X)) => ((exists(X, p(X)) v exists(X, q(X)))))], 2).
solve([not(exists(X, forall(Y, p(X) => p(Y))))], 2).
solve([not(exists(X, forall(Y, p(X, Y))) => forall(X, exists(Y, p(Y, X))))], 2).