(** * Repaired bar-recursive normalization bound

    This is the project-native port of Valentin Blot's 2018 [f.v] bound.
    It reuses the common System F syntax and erasure from [F.Syntax] and
    incorporates the reviewed semantic repairs recorded in
    [patches/blot-f.v-bound.patch]:

    - simultaneous substitution shifts variables beyond the substituted block;
    - the [TArrow] branch uses explicit projections to keep dependent
      extraction from aliasing its two recursive realizers;
    - the inner [TForall] elimination instantiates [rc] with the run-time term;
    - the abstraction case constructs its key before extending the context.

    [brec] remains the explicit extraction boundary from the artifact: it is
    a Rocq parameter with a specified OCaml implementation.  The implementation
    memoizes repeated pure oracle calls within one [brec_aux] state; this is
    call-by-need sharing of the same BBC equation, not a logical-state update.
    The extracted implementation also emits optional observations through the
    hand-written [Barrec_trace] runtime module.  With tracing disabled these
    hooks are silent and do not construct printable keys.
    Therefore this module exposes the executable bound but does not claim a
    kernel proof of adequacy for that external bar-recursion operator.  The untouched
    source, compatibility patch, repaired patch, and recorded differential
    runs remain under [vendor/], [patches/], and [bench/]. *)

From Stdlib Require Import Extraction Program.Wf JMeq Arith List.
Import ListNotations.
Import EqNotations.

From SystemF.F Require Import Syntax.

(* "term_subst n t p" is t[p/n]. Every
   free variable of t with index > n + |p|
   is decremented by |p|. *)
Fixpoint term_subst (n : nat) (t : term) (p : list term) : term :=
 match t with
  | Var m =>
    if m <? n then Var m
    else nth (m - n) p (Var (m - length p))
  | Lam t => Lam (term_subst (S n) t (map (term_lift 0) p))
  | App t u => App (term_subst n t p) (term_subst n u p)
 end.

(* Formulas of the logic. LVar is a constant
   in the sense of the logic (it can't be
   substituted), while LMetaVar is a variable
   in the sense of the logic (it can be
   substituted with a term of the logic).
   LMetaSubst is the simbol of the logic that
   allows to talk formally about substitutions.
   LLVar is also a variable in the sense of the
   logic, but of sort "list of terms". LLList
   is a list of terms of the logic. *)
Inductive logterm : Type :=
 | LVar : nat -> logterm
 | LLam : logterm -> logterm
 | LApp : logterm -> logtermlist -> logterm
 | LMetavar : nat -> logterm
 | LMetasubst : logterm -> logtermlist -> logterm
with logtermlist : Type :=
 | LLVar : nat -> logtermlist
 | LLList : list logterm -> logtermlist.
(* This embeds untyped terms in the logic. *)
Fixpoint term_to_logterm (t : term) : logterm :=
 match t with
  | Var m => LVar m
  | Lam t => LLam (term_to_logterm t)
  | App t u => LApp (term_to_logterm t) (LLList [term_to_logterm u])
 end.
(* This embeds lists of untyped terms
   in the logic. *)
Fixpoint termlist_to_logtermlist (p : list term) : logtermlist :=
 LLList (map term_to_logterm p).
(* "logterm_liftt n t" increments all the
   term meta-variables of t of with
   index >= n. *)
Fixpoint logterm_liftt (n : nat) (t : logterm) : logterm :=
 match t with
  | LVar m => LVar m
  | LLam t => LLam (logterm_liftt n t)
  | LApp t p => LApp (logterm_liftt n t) (logtermlist_liftt n p)
  | LMetavar m => if m <? n then LMetavar m else LMetavar (S m)
  | LMetasubst t p => LMetasubst (logterm_liftt n t) (logtermlist_liftt n p)
 end
with logtermlist_liftt (n : nat) (p : logtermlist) : logtermlist :=
 match p with
  | LLVar m => LLVar m
  | LLList p => LLList (map (logterm_liftt n) p)
 end.
(* "logterm_liftp n t" increments all the
   stack meta-variables of t with
   index >= n. *)
Fixpoint logterm_liftp (n : nat) (t : logterm) : logterm :=
 match t with
  | LVar m => LVar m
  | LLam t => LLam (logterm_liftp n t)
  | LApp t p => LApp (logterm_liftp n t) (logtermlist_liftp n p)
  | LMetavar m => LMetavar m
  | LMetasubst t p => LMetasubst (logterm_liftp n t) (logtermlist_liftp n p)
 end
with logtermlist_liftp (n : nat) (p : logtermlist) : logtermlist :=
 match p with
  | LLVar m => if m <? n then LLVar m else LLVar (S m)
  | LLList p => LLList (map (logterm_liftp n) p)
 end.
(* "logterm_substt n t u" is t[u/n].
   Term meta-variables of t with
   index >= n are decremented. *)
Fixpoint logterm_substt (n : nat) (t : logterm) (u : logterm) : logterm :=
 match t with
  | LVar n => LVar n
  | LLam t => LLam (logterm_substt n t u)
  | LApp t p => LApp (logterm_substt n t u) (logtermlist_substt n p u)
  | LMetavar m =>
   match m ?= n with
    | Lt => LMetavar m
    | Eq => u
    | Gt => LMetavar (pred m)
   end
  | LMetasubst t p => LMetasubst (logterm_substt n t u) (logtermlist_substt n p u)
 end
with logtermlist_substt (n : nat) (p : logtermlist) (u : logterm) : logtermlist :=
 match p with
  | LLVar m => LLVar m
  | LLList p => LLList (map (fun t => logterm_substt n t u) p)
 end.
(* "logterm_substp n t p" is t[p/n].
   Stack meta-variables of t with
   index >= n are decremented. *)
Fixpoint logterm_substp (n : nat) (t : logterm) (p : logtermlist) : logterm :=
 match t with
  | LVar n => LVar n
  | LLam t => LLam (logterm_substp n t p)
  | LApp t q => LApp (logterm_substp n t p) (logtermlist_substp n q p)
  | LMetavar m => LMetavar m
  | LMetasubst t q => LMetasubst (logterm_substp n t p) (logtermlist_substp n q p)
 end
with logtermlist_substp (n : nat) (q : logtermlist) (p : logtermlist) : logtermlist :=
 match q with
  | LLVar m =>
   match m ?= n with
    | Lt => LLVar m
    | Eq => p
    | Gt => LLVar (pred m)
   end
  | LLList q => LLList (map (fun t => logterm_substp n t p) q)
 end.
(* "logterm_to_term t" maps a term of
   the logic into an untyped lambda-term. *)
Fixpoint logterm_to_term (t : logterm) : term :=
 match t with
  | LVar n => Var n
  | LLam t => Lam (logterm_to_term t)
  | LApp t p =>
   match p with
    | LLVar m => Var 0
    | LLList p => fold_right (fun u t => App t u) (logterm_to_term t) (map logterm_to_term p)
   end
  | LMetavar m => Var 0
  | LMetasubst t p =>
   match p with
    | LLVar m => Var 0
    | LLList p => term_subst 0 (logterm_to_term t) (map logterm_to_term p)
   end
 end.

(* Formulas of the logic.
   FIn t n is the atom "t∈X"
   where X is the 2nd-order variable
   with de Bruijn index 0. *)
Inductive form : Type :=
 | FIn : logterm -> nat -> form
 | FBool : form
 | FImp : form -> form -> form
 | FConj : form -> form -> form
 | FForallt : form -> form
 | FForallp : form -> form
 | FForall2 : form -> form.
(*Fixpoint form_liftt (n : nat) (f : form) : form :=
 match f with
  | FIn t m => FIn (logterm_liftt n t) m
  | FBool => FBool
  | FImp f g => FImp (form_liftt n f) (form_liftt n g)
  | FConj f g => FConj (form_liftt n f) (form_liftt n g)
  | FForallt f => FForallt (form_liftt (S n) f)
  | FForallp f => FForallp (form_liftt n f)
  | FForall2 f => FForall2 (form_liftt n f)
 end.
Fixpoint form_liftp (n : nat) (f : form) : form :=
 match f with
  | FIn t m => FIn (logterm_liftp n t) m
  | FBool => FBool
  | FImp f g => FImp (form_liftp n f) (form_liftp n g)
  | FConj f g => FConj (form_liftp n f) (form_liftp n g)
  | FForallt f => FForallt (form_liftp n f)
  | FForallp f => FForallp (form_liftp (S n) f)
  | FForall2 f => FForall2 (form_liftp n f)
 end.*)
(* "form_substt n f t" is f[t/n].
   Term meta-variables of f with
   index >= n are decremented. *)
Fixpoint form_substt (n : nat) (f : form) (t : logterm) : form :=
 match f with
  | FIn u m => FIn (logterm_substt n u t) m
  | FBool => FBool
  | FImp f g => FImp (form_substt n f t) (form_substt n g t)
  | FConj f g => FConj (form_substt n f t) (form_substt n g t)
  | FForallt f => FForallt (form_substt (S n) f (logterm_liftt 0 t))
  | FForallp f => FForallp (form_substt n f t)
  | FForall2 f => FForall2 (form_substt n f t)
 end.
(* "form_substp n f p" is f[p/n].
   Stack meta-variables of f with
   index >= n are decremented. *)
Fixpoint form_substp (n : nat) (f : form) (p : logtermlist) : form :=
 match f with
  | FIn t m => FIn (logterm_substp n t p) m
  | FBool => FBool
  | FImp f g => FImp (form_substp n f p) (form_substp n g p)
  | FConj f g => FConj (form_substp n f p) (form_substp n g p)
  | FForallt f => FForallt (form_substp n f p)
  | FForallp f => FForallp (form_substp (S n) f (logtermlist_liftp 0 p))
  | FForall2 f => FForall2 (form_substp n f p)
 end.
(* "form_lift2 n f" increments all the
   2nd-order variables of f with
   index >= n. *)
Fixpoint form_lift2 (n : nat) (f : form) : form :=
 match f with
  | FIn t m => if m <? n then FIn t m else FIn t (S m)
  | FBool => FBool
  | FImp f g => FImp (form_lift2 n f) (form_lift2 n g)
  | FConj f g => FConj (form_lift2 n f) (form_lift2 n g)
  | FForallt f => FForallt (form_lift2 n f)
  | FForallp f => FForallp (form_lift2 n f)
  | FForall2 f => FForall2 (form_lift2 (S n) f)
 end.
Lemma form_lift2_substt : forall m n f t, form_lift2 m (form_substt n f t) = form_substt n (form_lift2 m f) t.
intros m n f; revert m n; induction f; intros m p t; simpl.
destruct (n <? m); reflexivity.
reflexivity.
rewrite IHf1.
rewrite IHf2.
reflexivity.
rewrite IHf1.
rewrite IHf2.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
Qed.
(* "form_subst2 n f g" is f[g/n].
   2nd-order variables of f with
   index >= n are decremented. *)
Fixpoint form_subst2 (n : nat) (f : form) (g : form) : form :=
 match f with
  | FIn t m =>
   match m ?= n with
    | Lt => FIn t m
    | Eq => form_substt 0 g t
    | Gt => FIn t (pred m)
   end
  | FBool => FBool
  | FImp f1 f2 => FImp (form_subst2 n f1 g) (form_subst2 n f2 g)
  | FConj f1 f2 => FConj (form_subst2 n f1 g) (form_subst2 n f2 g)
  | FForallt f => FForallt (form_subst2 n f g)
  | FForallp f => FForallp (form_subst2 n f g)
  | FForall2 f => FForall2 (form_subst2 (S n) f (form_lift2 0 g))
 end.

(* This is the skeleton of the "norm" formula.
   The formula itself is M↓ ≡ ¬∀i M̷↓i. *)
Definition norm : form := FImp (FImp FBool FBool) FBool.

(* This is the formula RedCand(X) ≡
   (∀π (̲0π ∈ X) ∧ ∀t (t ∈ X ⇒ t↓))
   ∧ ∀t ∀u ∀π (t[u/0]π ∈ X ⇒ (λ.t)uπ ∈ X)) *)
Definition redcand : form :=
 FConj
  (FConj
   (FForallp (FIn (LApp (LVar 0) (LLVar 0)) 0))
   (FForallt (FImp (FIn (LMetavar 0) 0) (norm)))
  )
  (FForallt (FForallt (FForallp
   (FImp
    (FIn (LApp (LMetasubst (LMetavar 1) (LLList [LMetavar 0])) (LLVar 0)) 0)
    (FIn (LApp (LApp (LLam (LMetavar 1)) (LLList [LMetavar 0])) (LLVar 0)) 0)
   )
  ))).

(* "rc T" is the formula RC_T with
    one free term meta-variable. *)
Fixpoint rc (T : type) : form :=
 match T with
  | TVar m => FIn (LMetavar 0) m
  | TArrow T U => FForallt (FImp (rc T) (form_substt 0 (rc U) (LApp (LMetavar 1) (LLList [LMetavar 0]))))
  | TForall T => FForall2 (FImp redcand (rc T))
 end.
Lemma form_lift2_rc : forall n U, form_lift2 n (rc U) = rc (type_lift n U).
intros n U; revert n; induction U; intro m; simpl.
destruct (n <? m); reflexivity.
f_equal.
f_equal.
apply IHU1.
rewrite form_lift2_substt.
rewrite IHU2.
reflexivity.
rewrite IHU.
reflexivity.
Qed.
Lemma form_subst2_lift2 : forall m T n U, form_subst2 m (rc T) (form_lift2 n (rc U)) = form_subst2 m (rc T) (rc (type_lift n U)).
intros m T; revert m; induction T; intros m p U; simpl.
destruct (n ?= m).
rewrite form_lift2_rc.
reflexivity.
reflexivity.
reflexivity.
rewrite IHT1.
rewrite form_lift2_rc.
reflexivity.
rewrite IHT.
rewrite form_lift2_rc.
rewrite form_lift2_rc.
reflexivity.
Qed.

(* "form_to_type f" is the type of
   realizers of f. *)
Fixpoint form_to_type (f : form) : Type :=
 match f with
  | FIn t m => nat
  | FBool => nat
  | FImp f g => form_to_type f -> form_to_type g
  | FConj f g => form_to_type f * form_to_type g
  | FForallt f => term -> form_to_type f
  | FForallp f => list term -> form_to_type f
  | FForall2 f => form_to_type f
 end.
Lemma form_to_type_substt : forall (f : form) (n : nat) (t : logterm), form_to_type (form_substt n f t) = form_to_type f.
intro f; induction f; intros t m; simpl.
reflexivity.
reflexivity.
rewrite IHf1; rewrite IHf2.
reflexivity.
rewrite IHf1; rewrite IHf2.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
Qed.
(*Lemma form_to_type_liftt : forall (f : form) (n : nat), form_to_type (form_liftt n f) = form_to_type f.
intro f; induction f; intro m; simpl.
reflexivity.
reflexivity.
rewrite IHf1; rewrite IHf2.
reflexivity.
rewrite IHf1; rewrite IHf2.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
Qed.
Lemma form_to_type_liftp : forall (f : form) (n : nat), form_to_type (form_liftp n f) = form_to_type f.
intro f; induction f; intro m; simpl.
reflexivity.
reflexivity.
rewrite IHf1; rewrite IHf2.
reflexivity.
rewrite IHf1; rewrite IHf2.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
Qed.*)
Lemma form_to_type_lift2 : forall (f : form) (n : nat), form_to_type (form_lift2 n f) = form_to_type f.
intro f; induction f; intro m; simpl.
destruct (n <? m); reflexivity.
reflexivity.
rewrite IHf1; rewrite IHf2.
reflexivity.
rewrite IHf1; rewrite IHf2.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
Qed.
Lemma form_to_type_subst2 : forall (f : form) (n : nat) (g : form) (h : form), form_to_type g = form_to_type h -> form_to_type (form_subst2 n f g) = form_to_type (form_subst2 n f h).
intro f; induction f; intros m g h Heq; simpl.
destruct (n ?= m); try reflexivity.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
assumption.
reflexivity.
rewrite (IHf1 _ _ _ Heq); rewrite (IHf2 _ _ _ Heq).
reflexivity.
rewrite (IHf1 _ _ _ Heq); rewrite (IHf2 _ _ _ Heq).
reflexivity.
rewrite (IHf _ g h).
reflexivity.
apply Heq.
rewrite (IHf _ g h).
reflexivity.
apply Heq.
rewrite (IHf _ (form_lift2 0 g) (form_lift2 0 h)).
reflexivity.
rewrite form_to_type_lift2.
rewrite form_to_type_lift2.
apply Heq.
Qed.
Lemma form_to_type_subst2_substt : forall (f : form) (n : nat) (i : nat) (t : logterm) (g : form), form_to_type (form_subst2 n (form_substt i f t) g) = form_to_type (form_subst2 n f g).
intro f; induction f; intros m i t g; simpl.
destruct (n ?= m); try reflexivity.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
reflexivity.
reflexivity.
rewrite IHf1.
rewrite IHf2.
reflexivity.
rewrite IHf1.
rewrite IHf2.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
Qed.
Lemma form_to_type_subst2_substp : forall (f : form) (n : nat) (i : nat) (p : logtermlist) (g : form), form_to_type (form_subst2 n (form_substp i f p) g) = form_to_type (form_subst2 n f g).
intro f; induction f; intros m i t g; simpl.
destruct (n ?= m); try reflexivity.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
reflexivity.
reflexivity.
rewrite IHf1.
rewrite IHf2.
reflexivity.
rewrite IHf1.
rewrite IHf2.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
Qed.
Lemma form_to_type_subst2_fin : forall (f : form) (n : nat) (m : nat) (t : logterm), form_to_type (form_subst2 n f (FIn t m)) = form_to_type f.
intro f; induction f; intros m i t; simpl.
destruct (n ?= m); reflexivity.
reflexivity.
rewrite IHf1.
rewrite IHf2.
reflexivity.
rewrite IHf1.
rewrite IHf2.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
Qed.
Lemma form_to_type_subst2_type_subst : forall T U n, form_to_type (form_subst2 n (rc T) (rc U)) = form_to_type (rc (type_subst n T U)).
intro t; induction t; intros U m; simpl.
destruct (n ?= m); simpl.
apply form_to_type_substt.
reflexivity.
reflexivity.
rewrite IHt1.
rewrite form_to_type_substt.
rewrite form_to_type_subst2_substt.
rewrite IHt2.
reflexivity.
rewrite <- IHt.
rewrite form_subst2_lift2.
reflexivity.
Qed.
(*Lemma form_to_type_subst2_fin2 : forall (f : form) (n : nat) (t : logterm), form_to_type (form_subst2 n (FIn t n) f) = form_to_type f.
intros f n t; simpl.
rewrite Nat.compare_refl.
rewrite form_to_type_substt.
reflexivity.
Qed.*)

(* This is the measure decreasing
   in the definition of repl. *)
Fixpoint form_measure (f : form) : nat :=
 match f with
  | FIn t m => 0
  | FBool => 0
  | FImp f1 f2 => S ((form_measure f1) + (form_measure f2))
  | FConj f1 f2 => S ((form_measure f1) + (form_measure f2))
  | FForallt f => S (form_measure f)
  | FForallp f => S (form_measure f)
  | FForall2 f => S (form_measure f)
 end.
Lemma form_measure_substt : forall (f : form) (n : nat) (t : logterm), form_measure (form_substt n f t) = form_measure f.
intro f; induction f; intros m t; simpl.
reflexivity.
reflexivity.
rewrite IHf1.
rewrite IHf2.
reflexivity.
rewrite IHf1.
rewrite IHf2.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
Qed.
Lemma form_measure_substp : forall (f : form) (n : nat) (p : logtermlist), form_measure (form_substp n f p) = form_measure f.
intro f; induction f; intros m t; simpl.
reflexivity.
reflexivity.
rewrite IHf1.
rewrite IHf2.
reflexivity.
rewrite IHf1.
rewrite IHf2.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
rewrite IHf.
reflexivity.
Qed.

(* "repl n f g h" is the realizer of:
   ∀t (g(t) ⇔ h(t)) ⇒ g[f/n] ⇔ h[f/n] *)
Program Fixpoint repl (n : nat) (f : form) {g h : form} (real : form_to_type (FForallt (FConj (FImp g h) (FImp h g)))) {measure (form_measure f)}
 : form_to_type (FConj (FImp (form_subst2 n f g) (form_subst2 n f h)) (FImp (form_subst2 n f h) (form_subst2 n f g))) :=
 match f with
  | FIn t m =>
   match m ?= n as c
   return
    let subst := fun f : form => match c with Eq => form_substt 0 f t | Lt => FIn t m | Gt => FIn t (pred m) end in
    form_to_type (FConj (FImp (subst g) (subst h)) (FImp (subst h) (subst g)))
   with
    | Eq =>
     let r := real (logterm_to_term t) in
     (fun y => rew [id] _ in fst r (rew [id] _ in y), fun y => rew [id] _ in snd r (rew [id] _ in y))
    | _ => (id, id)
   end
  | FBool => (id, id)
  | FImp f1 f2 =>
   let (r11, r12) := repl n f1 real in
   let (r21, r22) := repl n f2 real in
   (fun y z => r21 (y (r12 z)), fun y z => r22 (y (r11 z)))
  | FConj f1 f2 =>
   let (r11, r12) := repl n f1 real in
   let (r21, r22) := repl n f2 real in
   (fun y => (r11 (fst y), r21 (snd y)), fun y => (r12 (fst y), r22 (snd y)))
  | FForallt f =>
   (fun y t => rew [id] _ in fst (repl n (form_substt 0 f (term_to_logterm t)) real) (rew [id] _ in (y t)),
    fun y t => rew [id] _ in snd (repl n (form_substt 0 f (term_to_logterm t)) real) (rew [id] _ in (y t)))
  | FForallp f =>
   (fun y p => rew [id] _ in fst (repl n (form_substp 0 f (termlist_to_logtermlist p)) real) (rew [id] _ in y p),
    fun y p => rew [id] _ in snd (repl n (form_substp 0 f (termlist_to_logtermlist p)) real) (rew [id] _ in y p))
  | FForall2 f =>
   let r := repl (S n) f real in
     (fun y => rew [id] _ in fst r (rew [id] _ in y), fun y => rew [id] _ in snd r (rew [id] _ in y))
 end.
Next Obligation.
apply form_to_type_substt.
Qed.
Next Obligation.
rewrite form_to_type_substt.
reflexivity.
Qed.
Next Obligation.
apply form_to_type_substt.
Qed.
Next Obligation.
rewrite form_to_type_substt.
reflexivity.
Qed.
Next Obligation.
fold (m ?= n).
destruct (m ?= n); reflexivity.
Qed.
Next Obligation.
fold (m ?= n).
destruct (m ?= n); reflexivity.
Qed.
Next Obligation.
fold (m ?= n).
destruct (m ?= n); reflexivity.
Qed.
Next Obligation.
fold (m ?= n).
destruct (m ?= n); reflexivity.
Qed.
Next Obligation.
simpl.
apply le_n_S.
apply Nat.le_add_r.
Qed.
Next Obligation.
simpl.
apply le_n_S.
apply Nat.le_add_l.
Qed.
Next Obligation.
simpl.
apply le_n_S.
apply Nat.le_add_r.
Qed.
Next Obligation.
simpl.
apply le_n_S.
apply Nat.le_add_l.
Qed.
Next Obligation.
simpl.
rewrite form_measure_substt.
constructor.
Qed.
Next Obligation.
rewrite form_to_type_subst2_substt.
apply form_to_type_subst2.
reflexivity.
Qed.
Next Obligation.
rewrite form_to_type_subst2_substt.
apply form_to_type_subst2.
reflexivity.
Qed.
Next Obligation.
simpl.
rewrite form_measure_substt.
constructor.
Qed.
Next Obligation.
rewrite form_to_type_subst2_substt.
apply form_to_type_subst2.
reflexivity.
Qed.
Next Obligation.
rewrite form_to_type_subst2_substt.
apply form_to_type_subst2.
reflexivity.
Qed.
Next Obligation.
simpl.
rewrite form_measure_substp.
constructor.
Qed.
Next Obligation.
rewrite form_to_type_subst2_substp.
apply form_to_type_subst2.
reflexivity.
Qed.
Next Obligation.
rewrite form_to_type_subst2_substp.
apply form_to_type_subst2.
reflexivity.
Qed.
Next Obligation.
simpl.
rewrite form_measure_substp.
constructor.
Qed.
Next Obligation.
rewrite form_to_type_subst2_substp.
apply form_to_type_subst2.
reflexivity.
Qed.
Next Obligation.
rewrite form_to_type_subst2_substp.
apply form_to_type_subst2.
reflexivity.
Qed.
Next Obligation.
apply form_to_type_subst2.
apply form_to_type_lift2.
Qed.
Next Obligation.
apply form_to_type_subst2.
rewrite form_to_type_lift2.
reflexivity.
Qed.
Next Obligation.
apply form_to_type_subst2.
apply form_to_type_lift2.
Qed.
Next Obligation.
apply form_to_type_subst2.
rewrite form_to_type_lift2.
reflexivity.
Qed.

(* "dne f" is the realizer of ¬¬f ⇒ f *)
Fixpoint dne (f : form) : ((form_to_type f -> nat) -> nat) -> form_to_type f :=
 match f with
  | FIn t n => fun x => x id
  | FBool => fun x => x id
  | FImp f g => fun x y => dne g (fun z => x (fun u => z (u y)))
  | FConj f g => fun x => (dne f (fun y => x (fun z => y (fst z))), dne g (fun y => x (fun z => y (snd z))))
  | FForallt f => fun x y => dne f (fun z => x (fun u => z (u y)))
  | FForallp f => fun x y => dne f (fun z => x (fun u => z (u y)))
  | FForall2 f => dne f
 end.
(* "dne f" is the realizer of ⊥ ⇒ f *)
Definition exf (f : form) : nat -> form_to_type f := fun x => dne f (fun y => x).

(* This is the bar recursion operator.  We don't want to prove its termination
   in Coq, so it is a parameter with a specified extracted form.  Each
   [brec_aux] invocation caches the result of a term query.  Since the
   extracted realizers are pure, repeated uses observe the same value while
   avoiding call-by-name duplication. *)
Parameter brec : forall A : Type, ((A -> nat) -> A) -> ((term -> A) -> nat) -> (term -> option A) -> nat.
Extract Constant brec => "
 fun f g ->
  let tracing = Barrec_trace.enabled () in
  let brec_id = Barrec_trace.fresh_brec_id () in
  let rec trace_term = function
   | Var n -> Barrec_trace.key_var n
   | Lam body -> Barrec_trace.key_lam (trace_term body)
   | App (function_, argument) ->
       Barrec_trace.key_app (trace_term function_) (trace_term argument) in
  let trace action depth t =
   if tracing then action brec_id depth (trace_term t) in
  let rec brec_aux depth s =
   let cache = ref [] in
   let rec find t = function
    | [] -> None
    | (u, a) :: rest -> if term_equal u t then Some a else find t rest in
   g (fun t ->
    trace Barrec_trace.query depth t;
    match find t !cache with
    | Some a ->
        trace (Barrec_trace.hit Barrec_trace.Cache) depth t;
        a
    | None ->
        let a =
         match s t with
         | Some a ->
             trace (Barrec_trace.hit Barrec_trace.State) depth t;
             a
         | None ->
             trace Barrec_trace.miss depth t;
             let candidate_index = ref 0 in
             f (fun a ->
              let candidate =
               if !candidate_index = 0 then Barrec_trace.Exf
               else Barrec_trace.U in
              incr candidate_index;
              if tracing then
               Barrec_trace.update candidate brec_id (depth + 1)
                 (trace_term t);
              brec_aux (depth + 1)
               (fun u -> if term_equal u t then Some a else s u)) in
        cache := (t, a) :: !cache;
        a) in
  brec_aux 0
 ".
(* "equiv f" is ̲0 ∈ X ⇔ f *)
Definition equiv (f : form) : form := FConj (FImp (FIn (LVar 0) 0) f) (FImp f (FIn (LVar 0) 0)).
(* "comp f" is the realizer of
   the comprehnsion scheme:
   ¬∀X¬∀t(t ∈ X ⇔ f(t)) *)
Definition comp (f : form) : form_to_type (FImp (FForall2 (FImp (FForallt (equiv f)) FBool)) FBool) :=
 fun y => brec (form_to_type (equiv f)) (fun x => exf (equiv f) (x (exf f, fun u => x (fun v => u, fun v => 0)))) y (fun t => None).
Program Definition elim (f : form) (g : form) : form_to_type (FImp (FForall2 f) (form_subst2 0 f g)) :=
 fun x => dne (form_subst2 0 f g) (fun y => comp g (fun (z : form_to_type (FForallt (equiv g))) => y (fst (repl 0 f z) (rew [id] _ in x)))).
Next Obligation.
rewrite form_to_type_subst2_fin.
reflexivity.
Qed.

(* "normrc" is the realizer
   of RedCand ({ M | M ↓ }) *)
Definition normrc : form_to_type (form_subst2 0 redcand norm) :=
 (fun p x => x 0, fun t x => x, fun t u p x y => x (fun i => y (S i))).

(* "isrc tcontext T" is the realizer
   of RedCand(X_1) ⇒ ... ⇒ RedCand(X_n) ⇒ RedCand(T)
   where X_1...X_n is tcontext *)
Program Fixpoint isrc (tctx : list (form_to_type redcand)) (T : type) : form_to_type (form_subst2 0 redcand (rc T)) :=
 match T return form_to_type (form_subst2 0 redcand (rc T)) with
  | TVar m => rew [id] _ in nth m tctx (exf redcand 0)
  | TArrow T1 T2 =>
   let isrc1 := isrc tctx T1 in
   let isrc2 := isrc tctx T2 in
   (fun p t x => rew [id] _ in fst (fst isrc2) (t::p),
    fun t x => snd (fst isrc2) (App t (Var 0))
      (rew [id] _ in x (Var 0) (rew [id] _ in fst (fst isrc1) [])),
    fun t u p x v y => rew [id] _ in snd isrc2 t u (v::p)
      (rew [id] _ in x v (rew [id] _ in y)))
  | TForall T =>
   (fun p x => fst (fst (isrc (x::tctx) T)) p,
    fun t x => elim (FImp redcand (FForallt (FImp (rc T) norm))) norm (fun y => rew [id] _ in snd (fst (isrc (y::tctx) T))) normrc t (rew [id] _ in elim (FImp redcand (form_substt 0 (rc T) (term_to_logterm t))) norm (rew [id] _ in x) normrc),
    fun t u p y x => snd (isrc (x::tctx) T) t u p (y x))
 end.
Next Obligation.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
reflexivity.
Defined.
Next Obligation.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
reflexivity.
Defined.
Next Obligation.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
reflexivity.
Defined.
Next Obligation.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
reflexivity.
Defined.
Next Obligation.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
reflexivity.
Defined.
Next Obligation.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
reflexivity.
Defined.
Next Obligation.
rewrite form_to_type_substt.
reflexivity.
Qed.
Next Obligation.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
reflexivity.
Qed.
Next Obligation.
rewrite form_to_type_subst2_substt.
reflexivity.
Qed.

(* "adeq context tcontext t H" (where
   context is a list of (u, U, Hu) with
   Hu a realizer of u ∈ RC_U, tcontext is
   a list of realizers of RedCand(X_i) and
   H is a proof that t is well-typed
   in context context) is the realizer of
   RC_{(type_get context t)[U_1...U_n/0]}(t[u_1...u_n/0]) *)
Program Fixpoint adeq_var (tctx : list (form_to_type redcand)) (ctx : list (term * {T : type & form_to_type (rc T)})) (T : type) (t : dvar (map (@projT1 type (fun T => form_to_type (rc T))) (map snd ctx)) T) : form_to_type (rc T) :=
   match t with
    | DVar0 T => match ctx with [] => match _ : False with end | (t, existT _ T x)::ctx => x end
    | DVarS t => match ctx with [] => match _ : False with end | _::ctx => rew [id] _ in adeq_var tctx ctx T t end
   end.
Program Fixpoint adeq (tctx : list (form_to_type redcand)) (ctx : list (term * {T : type & form_to_type (rc T)})) (T : type) (t : fderiv (map (@projT1 type (fun T => form_to_type (rc T))) (map snd ctx)) T) : form_to_type (rc T) :=
 match t with
  | @DVar _ _ t => adeq_var tctx ctx _ t
  | @DLam _ T U t =>
   fun u y =>
    let body := term_subst 1 (fderiv_to_term t)
      (map (fun a => term_lift 0 (fst a)) ctx) in
    let ctx' := (u, existT _ T y)::ctx in
    rew [id] _ in snd (isrc tctx U) body u []
      (rew [id] _ in adeq tctx ctx' U t)
  | @DApp _ T U t u => rew [id] _ in adeq tctx ctx (TArrow T U) t (term_subst 0 (fderiv_to_term u) (map (fun a => fst a) ctx)) (adeq tctx ctx T u)
  | @DTLam _ T t => fun x => rew [id] _ in adeq (x::tctx) (map (fun a => (fst a, existT _ (type_lift 0 (projT1 (snd a))) (rew [id] _ in projT2 (snd a)))) ctx) T t
  | @DTApp _ T t U => rew [id] _ in elim (FImp redcand (form_substt 0 (rc T) (term_to_logterm (term_subst 0 (fderiv_to_term t) (map (fun a => fst a) ctx))))) (rc U) (rew [id] _ in adeq tctx ctx (TForall T) t) (isrc tctx U)
 end.
Next Obligation.
fold form_to_type.
rewrite form_to_type_substt.
reflexivity.
Qed.
Next Obligation.
fold form_to_type.
fold rc.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
reflexivity.
Qed.
Next Obligation.
fold form_to_type.
fold rc.
rewrite form_to_type_substt.
reflexivity.
Qed.
Next Obligation.
simpl.
generalize 0; clear; induction s; intro m; simpl.
destruct (n <? m); reflexivity.
rewrite form_to_type_substt.
rewrite form_to_type_substt.
rewrite <- IHs1.
rewrite <- IHs2.
reflexivity.
rewrite <- IHs.
reflexivity.
Qed.
Next Obligation.
rewrite map_map.
rewrite map_map.
rewrite map_map.
rewrite map_map.
apply map_ext.
reflexivity.
Qed.
Next Obligation.
rewrite form_to_type_substt.
reflexivity.
Qed.
Next Obligation.
fold form_to_type.
fold form_subst2.
rewrite form_to_type_subst2_substt.
rewrite form_to_type_subst2_type_subst.
reflexivity.
Qed.

(* "bound t H" (where H is a proof
   that t is well-typed in the empty
   context) computes a bound a bound
   on the number of reduction steps
   of t *)
Program Definition bound (T : type) (t : fderiv [] T) : nat :=
 snd (fst (isrc [] T)) (fderiv_to_term t) (rew [id] _ in adeq [] [] T t) id.
Next Obligation.
rewrite form_to_type_substt.
reflexivity.
Qed.
