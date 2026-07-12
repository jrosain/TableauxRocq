fof(ngoal, definition, $true <=> $false).
fof(conj, negated_conjecture, ngoal).

fof(s0, plain, ngoal, inference(iff, [s1, s2])).
fof(s1, plain, [], inference(notTrue, [])).
fof(s2, plain, [], inference(false, [])).
