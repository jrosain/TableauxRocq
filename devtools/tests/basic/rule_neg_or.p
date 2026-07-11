fof(goal, definition, ((a => (a | ~a)) | (~a | a))).
fof(conj, conjecture, goal).

fof(s0, plain, ~goal, inference(notOr, [s1])).
fof(s1, plain, ~(a => (a | ~a)), inference(notImplies, [s2])).
fof(s2, plain, ~(~a | a), inference(notOr, [s3])).
fof(s3, plain, [~a, a], inference(hyp, [])).
