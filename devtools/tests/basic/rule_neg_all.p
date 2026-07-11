fof(em, definition, ! [X]: (p(X) | ~p(X))).
fof(conj, conjecture, em).

fof(s0, plain, ~em, inference(notAll, [s1], $fot(c))).
fof(s1, plain, ~(p(c) | ~p(c)), inference(notOr, [s2])).
fof(s2, plain, ~~p(c), inference(notNot, [s3])).
fof(s3, plain, [p(c), ~p(c)], inference(hyp, [])).
