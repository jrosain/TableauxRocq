fof(conj, conjecture, $true).

fof(s0, plain, ~$true, inference(notImplies, [s1])).
fof(s1, plain, [], inference(notTrue, [])).
