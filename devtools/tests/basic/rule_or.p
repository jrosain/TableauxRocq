fof(em, definition, a | ~a).
fof(conj, conjecture, em).

fof(s0, plain, ~em, inference(notOr, [s1])).
fof(s1, plain, ~~a, inference(notNot, [s2])).
fof(s2, plain, [a, ~a], inference(hyp, [])).
