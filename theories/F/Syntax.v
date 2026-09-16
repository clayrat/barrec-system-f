(** * System F syntax and erasure

    These definitions are copied without semantic changes from Valentin
    Blot's 2018 artifact, Coq/f.v. The original file and its license are
    retained in vendor/blot/.  Only the names differ: the artifact's
    intrinsically typed [fterm]/[fvar], with constructors
    [FVar]/[FAbs]/[FApp]/[FTAbs]/[FTApp] and [FVar0]/[FVarS], are called
    [fderiv]/[dvar] with [DVar]/[DLam]/[DApp]/[DTLam]/[DTApp] and
    [DVar0]/[DVarS] here; its [fterm_to_term] is [fderiv_to_term], and its
    untyped [Abs] is [Lam].  A value of [fderiv ctx T] is a typing
    derivation; the name [fterm] belongs to the annotated Church-style terms
    of F.Check.

    Type variables and term variables use separate de Bruijn indices.
    [fderiv] records typing, but does not enforce type-variable scope;
    that additional invariant belongs to F.Scope and F.Check.

    The artifact's simultaneous [term_subst] is not part of this shared
    syntax: the reducer in [F.OperationalSemantics] uses its independent
    [term_subst1], while [BarRec.Bound] contains the repaired simultaneous
    substitution needed by the extracted bound. *)

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
  (ctx : list type).

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
Inductive dvar : list type -> type -> Type :=
| DVar0 : forall {ctx} T, dvar (T :: ctx) T
| DVarS : forall {ctx T U},
    dvar ctx T ->
    dvar (U :: ctx) T.

Inductive fderiv : list type -> type -> Type :=
| DVar : forall {ctx T},
    dvar ctx T ->
    fderiv ctx T
| DLam : forall {ctx T U},
    fderiv (T :: ctx) U ->
    fderiv ctx (TArrow T U)
| DApp : forall {ctx T U},
    fderiv ctx (TArrow T U) ->
    fderiv ctx T ->
    fderiv ctx U
| DTLam : forall {ctx T},
    fderiv (map (type_lift 0) ctx) T ->
    fderiv ctx (TForall T)
| DTApp : forall {ctx T},
    fderiv ctx (TForall T) ->
    forall U, fderiv ctx (type_subst 0 T U).

Definition fderiv_get_ctx {ctx T} (t : fderiv ctx T) :=
  ctx.

Definition fderiv_get_type {ctx T} (t : fderiv ctx T) :=
  T.

(** ** Untyped lambda terms *)

Inductive term : Type :=
| Var : nat -> term
| Lam : term -> term
| App : term -> term -> term.

Implicit Types (t u : term).

(** Erasure from Church-style System F terms to untyped Curry-style
    lambda terms. *)
Fixpoint dvar_to_nat {ctx T} (variable : dvar ctx T) : nat :=
  match variable with
  | DVar0 _ => 0
  | DVarS variable' => S (dvar_to_nat variable')
  end.

Fixpoint fderiv_to_term {ctx T} (t : fderiv ctx T) : term :=
  match t with
  | DVar variable => Var (dvar_to_nat variable)
  | DLam body => Lam (fderiv_to_term body)
  | DApp function argument =>
      App (fderiv_to_term function) (fderiv_to_term argument)
  | DTLam body => fderiv_to_term body
  | DTApp function _ => fderiv_to_term function
  end.

(** Boolean syntactic equality of untyped terms. *)
Fixpoint term_equal (t : term) (u : term) : bool :=
  match t, u with
  | Var m, Var n => m =? n
  | Lam t, Lam u => term_equal t u
  | App t1 t2, App u1 u2 =>
      andb (term_equal t1 u1) (term_equal t2 u2)
  | _, _ => false
  end.

(** [term_lift n t] increments every free variable of [t] whose index is
    greater than or equal to [n]. *)
Fixpoint term_lift (n : nat) (t : term) : term :=
  match t with
  | Var m => if m <? n then Var m else Var (S m)
  | Lam t => Lam (term_lift (S n) t)
  | App t u => App (term_lift n t) (term_lift n u)
  end.
