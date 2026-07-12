fof(conj, conjecture, a => a).

fof(s0, plain, ~(a => a), inference(notImplies, [s1])).
fof(s1, plain, [~a, a], inference(hyp, [])).
