fof(goal, definition, ! [X] : (p(X) & ~(p(X)))).
fof(conj, negated_conjecture, goal).

fof(s0, plain, goal, inference(forall, [s1], $fot(X))).
fof(s1, plain, p(X) & ~(p(X)), inference(and, [s2])).
fof(s2, plain, [p(X), ~(p(X))], inference(hyp, [])).
