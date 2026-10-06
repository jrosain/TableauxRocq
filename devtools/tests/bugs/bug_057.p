% Implies wasn't properly compiled & basic test-suite didn't check that.

fof(c, conjecture, ((p => q) <=> (~q => ~p))).
fof(s0, plain, [~((p => q) <=> (~q => ~p))], inference(leftNotIff, [s1, s2])).
fof(s1, plain, [~(~q => ~p)], inference(leftNotImplies, [s3])).
fof(s3, plain, [~~p], inference(leftNotNot, [s4])).
fof(s4, plain, [(p => q)], inference(leftImplies, [s5, s6])).
fof(s5, plain, [~p,p], inference(leftHyp, [])).
fof(s6, plain, [q,~q], inference(leftHyp, [])).
fof(s2, plain, [~(p => q)], inference(leftNotImplies, [s7])).
fof(s7, plain, [(~q => ~p)], inference(leftImplies, [s8, s9])).
fof(s8, plain, [~~q], inference(leftNotNot, [s10])).
fof(s10, plain, [q,~q], inference(leftHyp, [])).
fof(s9, plain, [~p,p], inference(leftHyp, [])).
