(** * Shared Hindley--Milner examples *)

From SystemF.HM Require Import Infer.

(** [fun f -> fun x -> let y = f x in f x], using numeric names as in
    W-in-Coq.  The bound occurrence of [y] is deliberately unused. *)
Definition repeated_application : term :=
  lam_t 0 (lam_t 1
    (let_t 2 (app_t (var_t 0) (var_t 1))
      (app_t (var_t 0) (var_t 1)))).

(** Church encoding of a pair constructor at the HM term level:
    [fun left right consumer => consumer left right]. *)
Definition hm_pair : term :=
  lam_t 2 (lam_t 3 (lam_t 4
    (app_t (app_t (var_t 4) (var_t 2)) (var_t 3)))).

(** Main W trace example from the plan:

    [let pair = fun left right consumer => consumer left right in
     let id = fun x => x in pair (id 0) (id true)]

    Constants [0] and [1] are distinct type markers [con 0] and [con 1].
    There is no primitive product in the imported HM syntax. *)
Definition polymorphic_pair_application : term :=
  let_t 0 hm_pair
    (let_t 1 (lam_t 2 (var_t 2))
      (app_t
        (app_t (var_t 0) (app_t (var_t 1) (const_t 0)))
        (app_t (var_t 1) (const_t 1)))).

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
