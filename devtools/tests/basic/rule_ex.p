fof(goal, definition, ? [X] : (p(X) & ~(p(X)))).
fof(conj, negated_conjecture, goal).

fof(s0, plain, goal, inference(exists, [s1], $fot(c))).
fof(s1, plain, p(c) & ~p(c), inference(and, [s2])).
fof(s2, plain, [p(c), ~p(c)], inference(hyp, [])).
