(** * System F syntax and erasure

    These definitions are copied without semantic changes from Valentin
    Blot's 2018 artifact, Coq/f.v. The original file and its license are
    retained in vendor/blot/.

    Type variables and term variables use separate de Bruijn indices.
    [fterm] records typing, but does not enforce type-variable scope;
    that additional invariant belongs to F.Scope and F.Check.

    The artifact's simultaneous [term_subst] is not copied: the reducer in
    F.OperationalSemantics uses its own [term_subst1], and the artifact's
    substitution defect is repaired separately in
    patches/blot-f.v-bound.patch for the bound experiments. *)

From Stdlib Require Import Arith List.
Import ListNotations.

(** ** Types *)

(** Type variables are represented by de Bruijn indices. *)
Inductive type : Type :=
| TVar : nat -> type
| TArrow : type -> type -> type
| TForall : type -> type.

Implicit Types
  (n m : nat)
  (T U : type)
  (context : list type).

(** [type_lift n T] increments every free variable of [T] whose index is
    greater than or equal to [n]. *)
Fixpoint type_lift (n : nat) (T : type) : type :=
  match T with
  | TVar m => if m <? n then TVar m else TVar (S m)
  | TArrow T U => TArrow (type_lift n T) (type_lift n U)
  | TForall T => TForall (type_lift (S n) T)
  end.

(** [type_subst n T U] is [T[U/n]].  Every free variable of [T] whose
    index is greater than [n] is decremented. *)
Fixpoint type_subst (n : nat) (T : type) (U : type) : type :=
  match T with
  | TVar m =>
      match m ?= n with
      | Lt => TVar m
      | Eq => U
      | Gt => TVar (pred m)
      end
  | TArrow T1 T2 => TArrow (type_subst n T1 U) (type_subst n T2 U)
  | TForall T => TForall (type_subst (S n) T (type_lift 0 U))
  end.

(** ** Intrinsically typed System F terms *)

(** Term variables also use de Bruijn indices. *)
Inductive fvar : list type -> type -> Type :=
| FVar0 : forall {context} T, fvar (T :: context) T
| FVarS : forall {context T U},
    fvar context T ->
    fvar (U :: context) T.

Inductive fterm : list type -> type -> Type :=
| FVar : forall {context T},
    fvar context T ->
    fterm context T
| FAbs : forall {context T U},
    fterm (T :: context) U ->
    fterm context (TArrow T U)
| FApp : forall {context T U},
    fterm context (TArrow T U) ->
    fterm context T ->
    fterm context U
| FTAbs : forall {context T},
    fterm (map (type_lift 0) context) T ->
    fterm context (TForall T)
| FTApp : forall {context T},
    fterm context (TForall T) ->
    forall U, fterm context (type_subst 0 T U).

Definition fterm_get_context {context T} (t : fterm context T) :=
  context.

Definition fterm_get_type {context T} (t : fterm context T) :=
  T.

(** ** Untyped lambda terms *)

Inductive term : Type :=
| Var : nat -> term
| Abs : term -> term
| App : term -> term -> term.

Implicit Types (t u : term).

(** Erasure from Church-style System F terms to untyped Curry-style
    lambda terms. *)
Fixpoint fvar_to_nat {context T} (variable : fvar context T) : nat :=
  match variable with
  | FVar0 _ => 0
  | FVarS variable' => S (fvar_to_nat variable')
  end.

Fixpoint fterm_to_term {context T} (t : fterm context T) : term :=
  match t with
  | FVar variable => Var (fvar_to_nat variable)
  | FAbs body => Abs (fterm_to_term body)
  | FApp function argument =>
      App (fterm_to_term function) (fterm_to_term argument)
  | FTAbs body => fterm_to_term body
  | FTApp function _ => fterm_to_term function
  end.

(** Boolean syntactic equality of untyped terms. *)
Fixpoint term_equal (t : term) (u : term) : bool :=
  match t, u with
  | Var m, Var n => m =? n
  | Abs t, Abs u => term_equal t u
  | App t1 t2, App u1 u2 =>
      andb (term_equal t1 u1) (term_equal t2 u2)
  | _, _ => false
  end.

(** [term_lift n t] increments every free variable of [t] whose index is
    greater than or equal to [n]. *)
Fixpoint term_lift (n : nat) (t : term) : term :=
  match t with
  | Var m => if m <? n then Var m else Var (S m)
  | Abs t => Abs (term_lift (S n) t)
  | App t u => App (term_lift n t) (term_lift n u)
  end.
