fof(nem, definition, a & ~a).
fof(goal, negated_conjecture, nem).

fof(s0, plain, nem, inference(and, [s1])).
fof(s1, plain, [a, ~a], inference(hyp, [])).
