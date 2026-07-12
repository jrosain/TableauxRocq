fof(falsity, negated_conjecture, $true => $false).

fof(s0, plain, $true => $false, inference(implies, [s1, s2])).
fof(s1, plain, [], inference(notTrue, [])).
fof(s2, plain, [], inference(false, [])).
