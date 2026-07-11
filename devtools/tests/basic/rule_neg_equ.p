fof(goal, definition, $true <=> (a => a)).
fof(conj, conjecture, goal).

fof(s0, plain, ~goal, inference(notIff, [s1, s2])).
fof(s1, plain, ~(a => a), inference(notImplies, [s3])).
fof(s3, plain, [~a, a], inference(hyp, [])).
fof(s2, plain, [], inference(notTrue, [])).

