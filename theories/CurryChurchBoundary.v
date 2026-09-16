(** * Executable boundary between Curry and Church presentations

    Erasure from Church-style System F is intentionally many-to-one: it drops
    lambda annotations, type abstractions, and type applications.  The small
    witnesses below make both kinds of information loss executable.  They are
    not an attempted algorithm for full Curry-style System F reconstruction
    (which is undecidable); the two supported ways back across the boundary
    are instead explicit Church input and rank-1 HM inference. *)

From Stdlib Require Import List.
Import ListNotations.

From SystemF.F Require Import Syntax Check.
From SystemF.HM.W Require Import SimpleTypes Typing.
From SystemF Require Import HMElab.

(** The Curry term [fun x => x]. *)
Definition boundary_curry_identity : SystemF.F.Syntax.term :=
  Lam (Var 0).

Definition boundary_identity_type : type :=
  TForall (TArrow (TVar 0) (TVar 0)).

Definition boundary_identity_arrow_type : type :=
  TArrow boundary_identity_type boundary_identity_type.

(** Two explicit Church choices for the same Curry identity:

      Lambda X. fun x : X => x
      fun x : (forall X. X -> X) => x

    Their types differ, so erasure alone cannot tell the checker which one the
    programmer intended. *)
Definition boundary_raw_polymorphic_identity : fterm :=
  FTLam (FLam (TVar 0) (FVar 0)).

Definition boundary_raw_identity_at_identity_type : fterm :=
  FLam boundary_identity_type (FVar 0).

(** These two terms also erase to the same Curry application.  The first uses
    an explicit type application; the second uses a term lambda annotation. *)
Definition boundary_raw_type_application : fterm :=
  FApp
    (FTApp boundary_raw_polymorphic_identity boundary_identity_type)
    boundary_raw_polymorphic_identity.

Definition boundary_raw_annotated_application : fterm :=
  FApp
    (FLam boundary_identity_type (FVar 0))
    boundary_raw_polymorphic_identity.

Definition boundary_checked_type (raw : fterm) : option type :=
  match checkClosed raw with
  | Ok checked => Some (projT1 checked)
  | Err _ => None
  end.

Theorem boundary_identity_church_choices_check :
  boundary_checked_type boundary_raw_polymorphic_identity =
    Some boundary_identity_type /\
  boundary_checked_type boundary_raw_identity_at_identity_type =
    Some boundary_identity_arrow_type.
Proof. split; reflexivity. Qed.

Theorem boundary_identity_erasure_is_many_to_one :
  fterm_to_term boundary_raw_polymorphic_identity = boundary_curry_identity /\
  fterm_to_term boundary_raw_identity_at_identity_type = boundary_curry_identity /\
  boundary_identity_type <> boundary_identity_arrow_type.
Proof.
  repeat split; try reflexivity.
  discriminate.
Qed.

Theorem boundary_type_application_disappears :
  fterm_to_term boundary_raw_type_application =
    fterm_to_term boundary_raw_annotated_application /\
  boundary_checked_type boundary_raw_type_application =
    Some boundary_identity_type /\
  boundary_checked_type boundary_raw_annotated_application =
    Some boundary_identity_type /\
  boundary_raw_type_application <>
    boundary_raw_annotated_application.
Proof.
  repeat split; try reflexivity.
  discriminate.
Qed.

(** The rank-1 route starts from a separate HM AST.  W supplies a principal
    scheme, and the existing elaborator inserts exactly the type abstraction
    and lambda annotation needed by the Church checker. *)
Definition boundary_hm_identity : hmterm :=
  lam_t 0 (var_t 0).

Definition boundary_constant_type
    (_ : SystemF.HM.W.SimpleTypes.id) : type :=
  boundary_identity_type.

Definition boundary_hm_identity_church_view : option (type * fterm) :=
  match runWChurch boundary_constant_type boundary_hm_identity with
  | Ok elaboration =>
      Some
        (church_systemf_type elaboration,
         church_term elaboration)
  | Err _ => None
  end.

Theorem boundary_HM_restores_rank1_annotations :
  boundary_hm_identity_church_view =
  Some
    (boundary_identity_type,
     boundary_raw_polymorphic_identity).
Proof. reflexivity. Qed.

Theorem boundary_HM_restored_term_has_original_erasure :
  fterm_to_term boundary_raw_polymorphic_identity = boundary_curry_identity.
Proof. reflexivity. Qed.
