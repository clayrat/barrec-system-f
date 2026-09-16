(** * Proof-free computational core of Algorithm W

    The adapted upstream [W] carries its Hoare contract in dependent results.
    This module repeats only its computational branches with an explicit
    state and the proof-free unifier.  It is intended for kernel evaluation
    and extraction; the original [W] remains the checked specification. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.

From SystemF.HM Require Import Unify.
From SystemF.HM.W Require Import
  Context Gen Schemes SubstSchm Typing.

Inductive w_state_result : Set :=
| w_state_success : ty -> substitution -> id -> w_state_result
| w_state_rejected.

Inductive w_result : Set :=
| inferred : ty -> substitution -> w_result
| inference_rejected.

(** Pure counterpart of [computeInitialState]. *)
Fixpoint initial_state_exec (G : hmctx) : id :=
  match G with
  | [] => 0
  | (_, sigma) :: G' =>
      let st := initial_state_exec G' in
      if Nat.ltb (max_vars_schm sigma) st
      then st
      else S (max_vars_schm sigma)
  end.

(** The five branches and the order of state/substitution composition are the
    same as in [SystemF.HM.W.Infer.W]. *)
Fixpoint W_exec (e : hmterm) (G : hmctx) (st : id) : w_state_result :=
  match e with
  | const_t c => w_state_success (con c) [] st

  | var_t x =>
      match in_ctx x G with
      | None => w_state_rejected
      | Some sigma =>
          let count := max_gen_vars sigma in
          match apply_inst_subst (compute_inst_subst st count) sigma with
          | None => w_state_rejected
          | Some tau => w_state_success tau [] (st + count)
          end
      end

  | lam_t x body =>
      let alpha := st in
      match W_exec body
        ((x, ty_to_schm (var alpha)) :: G) (S st) with
      | w_state_rejected => w_state_rejected
      | w_state_success tau s st' =>
          w_state_success
            (arrow (apply_subst s (var alpha)) tau) s st'
      end

  | app_t function argument =>
      match W_exec function G st with
      | w_state_rejected => w_state_rejected
      | w_state_success tau1 s1 st1 =>
          match W_exec argument (apply_subst_ctx s1 G) st1 with
          | w_state_rejected => w_state_rejected
          | w_state_success tau2 s2 st2 =>
              let alpha := st2 in
              match unify_exec
                (apply_subst s2 tau1)
                (arrow tau2 (var alpha)) with
              | rejected => w_state_rejected
              | unified s =>
                  w_state_success
                    (apply_subst s (var alpha))
                    (comp_subst s1 (comp_subst s2 s))
                    (S st2)
              end
          end
      end

  | let_t x bound body =>
      match W_exec bound G st with
      | w_state_rejected => w_state_rejected
      | w_state_success tau1 s1 st1 =>
          let G' := apply_subst_ctx s1 G in
          match W_exec body ((x, gen_ty tau1 G') :: G') st1 with
          | w_state_rejected => w_state_rejected
          | w_state_success tau2 s2 st2 =>
              w_state_success tau2 (comp_subst s1 s2) st2
          end
      end
  end.

Definition runW_exec (e : hmterm) (G : hmctx) : w_result :=
  match W_exec e G (initial_state_exec G) with
  | w_state_success tau s _ => inferred tau s
  | w_state_rejected => inference_rejected
  end.
