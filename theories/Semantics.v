(** * Semantics: semantics of first-order logic. *)

From Stdlib Require Import Classical.

From Tableaux Require Import Prelude.All.
From Tableaux Require Import Syntax.

Section SemanticsDef.
  Context {pred func var : Atom}.

  Class Model :=
    { car :> Type
    ; interp_func : func -> list car -> car
    ; interp_pred : pred -> list car -> Prop
    ; non_empty : car
    ; eq_dec_car : EqDec car }.

  Definition env (M : Model) (A : Type) := A -> option M.

  Definition empty_env (M : Model) (A : Type) : env M A := fun _ => None.

  Class Interpret (M : Model) (A B : Type) :=
    interpret : list M -> env M var -> A -> B.

  #[global] Instance interpret_term `{M : Model} : Interpret M (Term_ func var) M :=
    fun rho sigma =>
      fix F (t : Term_ func var) : M :=
        match t with
        | Bound n => option_get non_empty (nth_error rho n)
        | Free  x => option_get non_empty (sigma x)
        | Fun f l => interp_func f (map F l)
        end.

  #[global] Instance interpret_form_ (M : Model) : Interpret M (Form_ pred func var) Prop :=
    fix rec (rho : list M) (sigma : env M var) (F : Form_ pred func var) : Prop :=
      match F with
      | Bot        => False
      | Pred p l => interp_pred p (map (interpret_term rho sigma) l)
      | Neg F      => ~ (rec rho sigma F)
      | Or F G   => rec rho sigma F \/ rec rho sigma G
      | All F    => forall (x : M), rec (x :: rho) sigma F
      end.

  Definition is_valid (F : Form_ pred func var) :=
    forall (M : Model), interpret_form_ M [] (empty_env M var) F.
End SemanticsDef.

Arguments Model : clear implicits.
Arguments Interpret {_ _ _} _ _ _.
Arguments interpret {_ _ _} _ {_ _ _} _ _ _.

Notation "\models F" := (is_valid F) (at level 40).
Notation "[[ M # rho # sigma |- F ]]" := (interpret M rho sigma F).
