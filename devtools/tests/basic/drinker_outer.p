% foo bar foo
fof(drinker, definition, ? [X] : (d(X) => ! [Y] : d(Y))).
fof(drinker_conj, negated_conjecture, ~drinker).

fof(s, substitution, { Y -> f(X) }, outer).

fof(s0, plain, ~drinker, inference(leftNotEx, [s1], $fot(X))).
fof(s1, plain, ~(d(X) => ! [Y] : d(Y)), inference(leftNotImplies, [s2])).
fof(s2, plain, ~(! [Y] : d(Y)), inference(leftNotAll, [s3], $fot(f(X)))).
fof(s3, plain, ~drinker, inference(leftNotEx, [s4], $fot(Y))).
fof(s4, plain, ~(d(Y) => ! [Y] : d(Y)), inference(leftNotImplies, [s5])).
fof(s5, plain, [d(Y), ~d(f(X))], inference(leftHyp, [])).
