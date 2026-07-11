fof(drinker, definition, ? [X] : (d(X) => ! [Y] : d(Y))).
fof(drinker_conj, negated_conjecture, ~drinker).

fof(s, substitution, { X -> c }).

fof(s0, plain, ~drinker, inference(leftNotEx, [s1], $fot(X))).
fof(s1, plain, ~(d(X) => ! [Y] : d(Y)), inference(leftNotImplies, [s2])).
fof(s2, plain, ~(! [Y] : d(Y)), inference(leftNotAll, [s3], $fot(c))).
fof(s3, plain, [d(X), ~d(c)], inference(leftHyp, [])).
