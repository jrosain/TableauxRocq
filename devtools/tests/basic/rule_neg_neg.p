fof(a_does_not_hold, axiom, ~a).
fof(conj, conjecture, ~a).

fof(s0, plain, ~~a, inference(notNot, [s1])).
fof(s1, plain, [~a, a], inference(hyp, [])).
