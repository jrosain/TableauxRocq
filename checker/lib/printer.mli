open SyntaxInstance

val pr_form : (coq_Term -> Prelude.RocqStr.t) -> coq_Form -> Prelude.RocqStr.t

val pr_ctx : (coq_Term -> Prelude.RocqStr.t) -> coq_Form list -> Prelude.RocqStr.t
