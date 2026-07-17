fof(a_holds, axiom, p(a)).
fof(goal, definition, ? [X]: p(X)).
fof(conj, conjecture, goal).

fof(s, substitution, { X -> a }, outer).

fof(s0, plain, ~goal, inference(notEx, [s1], $fot(X))).
fof(s1, plain, [~p(X), p(a)], inference(hyp, [])).
