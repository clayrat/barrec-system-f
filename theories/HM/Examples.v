(** * Shared Hindley--Milner examples *)

From SystemF.HM Require Import Infer.

(** [fun f -> fun x -> let y = f x in f x], using numeric names as in
    W-in-Coq.  The bound occurrence of [y] is deliberately unused. *)
Definition repeated_application : term :=
  lam_t 0 (lam_t 1
    (let_t 2 (app_t (var_t 0) (var_t 1))
      (app_t (var_t 0) (var_t 1)))).

Definition infer_succeeds (e : term) : bool :=
  match runW e nil with
  | inl _ => true
  | inr _ => false
  end.

Definition infer_exec_succeeds (e : term) : bool :=
  match runW_exec e nil with
  | inferred _ _ => true
  | inference_rejected => false
  end.
