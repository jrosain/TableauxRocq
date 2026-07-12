fof(conj, conjecture, a => a).

fof(s0, plain, ~(a => a), inference(notOr, [s1])).
fof(s1, plain, [~a, a], inference(hyp, [s0])).
