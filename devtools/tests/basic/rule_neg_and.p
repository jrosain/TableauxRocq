fof(conj, conjecture, $true & $true).

fof(s0, plain, ~($true & $true), inference(notAnd, [s1, s2])).
fof(s1, plain, [], inference(notTrue, [])).
fof(s2, plain, [], inference(notTrue, [])).
