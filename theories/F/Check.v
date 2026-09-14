(** * Church-style checker

    Raw Church terms carry every annotation needed by System F checking but
    deliberately carry no typing evidence.  [check_core] turns accepted
    inputs into intrinsically typed [fterm] values; [check]/[checkClosed]
    add a [Prop]-valued certificate ([Checked]) on top of the same result.
    The correctness statements are relative to [forget]: acceptance is
    equivalent to the existence of an intrinsic term with exactly the
    input's annotations, and rejection excludes every such term. *)

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

From SystemF.F Require Import Syntax Scope.

(** [type] itself is the raw type syntax: scope is checked separately. *)
Definition RawType : Type := type.

Inductive RawChurch : Type :=
| RCVar : nat -> RawChurch
| RCAbs : RawType -> RawChurch -> RawChurch
| RCApp : RawChurch -> RawChurch -> RawChurch
| RCTAbs : RawChurch -> RawChurch
| RCTApp : RawChurch -> RawType -> RawChurch.

Implicit Types
  (n m : nat)
  (raw : RawChurch).

(** [scoped n raw] checks only type-variable scope.  Term-variable indices
    are checked against the term context by the future intrinsic checker. *)
Fixpoint scoped (n : nat) (raw : RawChurch) : Prop :=
  match raw with
  | RCVar _ => True
  | RCAbs T body => closed n T /\ scoped n body
  | RCApp function argument =>
      scoped n function /\ scoped n argument
  | RCTAbs body => scoped (S n) body
  | RCTApp function T => scoped n function /\ closed n T
  end.

Fixpoint scoped_dec (n : nat) (raw : RawChurch) :
    {scoped n raw} + {~ scoped n raw}.
Proof.
  destruct raw as
      [index | T body | function argument | body | function T];
    cbn [scoped].
  - now left.
  - destruct (closed_dec n T) as [HT | HT];
      destruct (scoped_dec n body) as [Hbody | Hbody].
    + now left.
    + right. intros [_ H]. contradiction.
    + right. intros [H _]. contradiction.
    + right. intros [H _]. contradiction.
  - destruct (scoped_dec n function) as [Hfunction | Hfunction];
      destruct (scoped_dec n argument) as [Hargument | Hargument].
    + now left.
    + right. intros [_ H]. contradiction.
    + right. intros [H _]. contradiction.
    + right. intros [H _]. contradiction.
  - exact (scoped_dec (S n) body).
  - destruct (scoped_dec n function) as [Hfunction | Hfunction];
      destruct (closed_dec n T) as [HT | HT].
    + now left.
    + right. intros [_ H]. contradiction.
    + right. intros [H _]. contradiction.
    + right. intros [H _]. contradiction.
Defined.

Lemma scoped_mono : forall n m raw,
  n <= m -> scoped n raw -> scoped m raw.
Proof.
  intros n m raw.
  revert n m.
  induction raw as
      [index | T body IHbody | function IHfunction argument IHargument
       | body IHbody | function IHfunction T];
    intros n m Hnm Hscoped; cbn [scoped] in *.
  - exact I.
  - destruct Hscoped as [HT Hbody].
    split.
    + now apply closed_mono with n.
    + now apply IHbody with n.
  - destruct Hscoped as [Hfunction Hargument].
    split.
    + now apply IHfunction with n.
    + now apply IHargument with n.
  - apply IHbody with (n := S n); try assumption.
    lia.
  - destruct Hscoped as [Hfunction HT].
    split.
    + now apply IHfunction with n.
    + now apply closed_mono with n.
Qed.

(** ** Decidable type equality *)

(** Structural equality returns an equality proof for the dependent casts
    needed by application checking. *)
Fixpoint type_eq_dec (T U : type) : {T = U} + {T <> U}.
Proof.
  decide equality.
  apply Nat.eq_dec.
Defined.

(** ** Errors and dependent term-variable lookup *)

Inductive Result (E A : Type) : Type :=
| Ok : A -> Result E A
| Err : E -> Result E A.

Arguments Ok {E A} _.
Arguments Err {E A} _.

(** The two scope errors are separate so an extracted driver can distinguish
    a lambda annotation from an explicit type argument.  In [TypeMismatch],
    the first type is expected and the second one was inferred. *)
Inductive TypeError : Type :=
| UnboundTermVariable : nat -> TypeError
| TypeAnnotationOutOfScope : type -> TypeError
| TypeArgumentOutOfScope : type -> TypeError
| ExpectedArrow : type -> TypeError
| ExpectedForall : type -> TypeError
| TypeMismatch : type -> type -> TypeError.

(** Successful lookup packages both the type and its intrinsic membership
    witness. *)
Fixpoint find_fvar (context : list type) (index : nat)
    : option {T : type & fvar context T} :=
  match context as context'
        return option {T : type & fvar context' T} with
  | [] => None
  | T :: context' =>
      match index with
      | 0 => Some (existT _ T (@FVar0 context' T))
      | S index' =>
          match find_fvar context' index' with
          | None => None
          | Some (existT _ U variable) =>
              Some (existT _ U (@FVarS context' U T variable))
          end
      end
  end.

Definition lookup_fvar (context : list type) (index : nat)
    : Result TypeError {T : type & fvar context T} :=
  match find_fvar context index with
  | Some variable => Ok variable
  | None => Err (UnboundTermVariable index)
  end.

Lemma fvar_nth_error : forall context T (variable : fvar context T),
  nth_error context (fvar_to_nat variable) = Some T.
Proof.
  intros context T variable.
  induction variable; cbn [fvar_to_nat]; assumption || reflexivity.
Qed.

Lemma fvar_closed : forall n context T (variable : fvar context T),
  Forall (closed n) context -> closed n T.
Proof.
  intros n context T variable Hcontext.
  apply (closed_nth_error n context (fvar_to_nat variable) T Hcontext).
  apply fvar_nth_error.
Qed.

Lemma find_fvar_position : forall context index,
  match find_fvar context index with
  | Some (existT _ T variable) => fvar_to_nat variable = index
  | None => True
  end.
Proof.
  induction context as [| T context IH]; intros [| index];
    cbn [find_fvar].
  - exact I.
  - exact I.
  - reflexivity.
  - destruct (find_fvar context index) as [[U variable] |]
      eqn:Hfind.
    + cbn.
      specialize (IH index).
      rewrite Hfind in IH.
      cbn in IH.
      now f_equal.
    + exact I.
Qed.

Lemma find_fvar_complete : forall context T (variable : fvar context T),
  exists variable' : fvar context T,
    find_fvar context (fvar_to_nat variable) =
    Some (existT (fun T => fvar context T) T variable').
Proof.
  intros context T variable.
  induction variable as [context T | context T U variable IH].
  - exists (@FVar0 context T).
    reflexivity.
  - destruct IH as [variable' Hfind].
    exists (@FVarS context T U variable').
    cbn [find_fvar fvar_to_nat].
    now rewrite Hfind.
Qed.

(** ** Computational checking core *)

Definition Inferred (context : list type) : Type :=
  {T : type & fterm context T}.

(** Application checking needs to transport the inferred argument across the
    proof returned by [type_eq_dec]. *)
Definition cast_fterm {context A B}
    (equality : A = B) (t : fterm context B) : fterm context A :=
  eq_rect B (fun T => fterm context T) t A (eq_sym equality).

Fixpoint check_core
    (n : nat) (context : list type) (raw : RawChurch)
    : Result TypeError (Inferred context) :=
  match raw with
  | RCVar index =>
      match lookup_fvar context index with
      | Err error => Err error
      | Ok (existT _ T variable) =>
          Ok (existT _ T (FVar variable))
      end
  | RCAbs T body =>
      match closed_dec n T with
      | right _ => Err (TypeAnnotationOutOfScope T)
      | left _ =>
          match check_core n (T :: context) body with
          | Err error => Err error
          | Ok (existT _ U body') =>
              Ok (existT _ (TArrow T U) (FAbs body'))
          end
      end
  | RCApp function argument =>
      match check_core n context function with
      | Err error => Err error
      | Ok (existT _ function_type function') =>
          match function_type as function_type'
                return
                  fterm context function_type' ->
                  Result TypeError (Inferred context)
          with
          | TArrow T U =>
              fun function' =>
                match check_core n context argument with
                | Err error => Err error
                | Ok (existT _ V argument') =>
                    match type_eq_dec T V with
                    | left equality =>
                        Ok (existT _ U
                          (FApp function'
                            (cast_fterm equality argument')))
                    | right _ => Err (TypeMismatch T V)
                    end
                end
          | TVar index =>
              fun _ => Err (ExpectedArrow (TVar index))
          | TForall T =>
              fun _ => Err (ExpectedArrow (TForall T))
          end function'
      end
  | RCTAbs body =>
      match
        check_core (S n) (map (type_lift 0) context) body
      with
      | Err error => Err error
      | Ok (existT _ T body') =>
          Ok (existT _ (TForall T) (FTAbs body'))
      end
  | RCTApp function T =>
      match closed_dec n T with
      | right _ => Err (TypeArgumentOutOfScope T)
      | left _ =>
          match check_core n context function with
          | Err error => Err error
          | Ok (existT _ function_type function') =>
              match function_type as function_type'
                    return
                      fterm context function_type' ->
                      Result TypeError (Inferred context)
              with
              | TForall U =>
                  fun function' =>
                    Ok (existT _ (type_subst 0 U T)
                      (FTApp function' T))
              | TVar index =>
                  fun _ => Err (ExpectedForall (TVar index))
              | TArrow U V =>
                  fun _ => Err (ExpectedForall (TArrow U V))
              end function'
          end
      end
  end.

(** Forget intrinsic typing while retaining all Church-style annotations. *)
Fixpoint forget {context T} (t : fterm context T) : RawChurch :=
  match t with
  | FVar variable => RCVar (fvar_to_nat variable)
  | @FAbs _ A _ body => RCAbs A (forget body)
  | FApp function argument => RCApp (forget function) (forget argument)
  | FTAbs body => RCTAbs (forget body)
  | FTApp function U => RCTApp (forget function) U
  end.

(** Erasure of raw Church syntax removes types and type-level constructs. *)
Fixpoint erase_raw (raw : RawChurch) : term :=
  match raw with
  | RCVar index => Var index
  | RCAbs _ body => Abs (erase_raw body)
  | RCApp function argument =>
      App (erase_raw function) (erase_raw argument)
  | RCTAbs body => erase_raw body
  | RCTApp function _ => erase_raw function
  end.

Theorem erase_raw_forget : forall context T (t : fterm context T),
  erase_raw (forget t) = fterm_to_term t.
Proof.
  intros context T t.
  induction t; cbn [forget erase_raw fterm_to_term]; congruence.
Qed.

(** ** Soundness and completeness of the computational core *)

(** Completeness first records that rechecking a scoped intrinsic term
    succeeds with the same result type.  The concrete proof term may differ
    because variable lookup and equality casts reconstruct witnesses. *)
Theorem check_core_complete_type :
  forall n context T (t : fterm context T),
    scoped n (forget t) ->
    match check_core n context (forget t) with
    | Ok (existT _ U _) => U = T
    | Err _ => False
    end.
Proof.
  intros n context T t.
  revert n.
  induction t as
      [context T variable
       | context T U body IHbody
       | context T U function IHfunction argument IHargument
       | context T body IHbody
       | context T function IHfunction U];
    intros n Hscoped.
  - cbn [forget] in Hscoped |- *.
    destruct (find_fvar_complete context T variable)
      as [variable' Hfind].
    cbn [check_core].
    unfold lookup_fvar.
    rewrite Hfind.
    reflexivity.
  - cbn [forget scoped] in Hscoped.
    destruct Hscoped as [HT Hbody].
    specialize (IHbody n Hbody).
    cbn [forget check_core].
    destruct (closed_dec n T) as [HT' | HT']; [| contradiction].
    destruct (check_core n (T :: context) (forget body))
      as [[V body'] | error] eqn:Hcheck.
    + unfold RawType in *.
      rewrite Hcheck.
      cbn.
      now f_equal.
    + unfold RawType in *.
      rewrite Hcheck.
      exact IHbody.
  - cbn [forget scoped] in Hscoped.
    destruct Hscoped as [Hfunction Hargument].
    specialize (IHfunction n Hfunction).
    specialize (IHargument n Hargument).
    cbn [forget check_core].
    destruct (check_core n context (forget function))
      as [[function_type function'] | error]
      eqn:Hfunction_check.
    + cbn in IHfunction.
      subst function_type.
      destruct (check_core n context (forget argument))
        as [[argument_type argument'] | error]
        eqn:Hargument_check.
      * cbn in IHargument.
        subst argument_type.
        destruct (type_eq_dec T T) as [equality | inequality].
        -- reflexivity.
        -- contradiction.
      * exact IHargument.
    + exact IHfunction.
  - cbn [forget scoped] in Hscoped.
    specialize (IHbody (S n) Hscoped).
    cbn [forget check_core].
    destruct
      (check_core (S n) (map (type_lift 0) context) (forget body))
      as [[U body'] | error] eqn:Hcheck.
    + unfold RawType in *.
      cbn in IHbody.
      now f_equal.
    + exact IHbody.
  - cbn [forget scoped] in Hscoped.
    destruct Hscoped as [Hfunction HU].
    specialize (IHfunction n Hfunction).
    cbn [forget check_core].
    destruct (closed_dec n U) as [HU' | HU']; [| contradiction].
    destruct (check_core n context (forget function))
      as [[function_type function'] | error] eqn:Hcheck.
    + unfold RawType in *.
      cbn in IHfunction.
      subst function_type.
      reflexivity.
    + exact IHfunction.
Qed.

Definition InferredSpec n raw {context}
    (result : Inferred context) : Prop :=
  match result with
  | existT _ T t =>
      closed n T /\ scoped n raw /\ forget t = raw
  end.

Lemma forget_cast_fterm : forall context A B
    (equality : A = B) (t : fterm context B),
  forget (cast_fterm equality t) = forget t.
Proof.
  intros context A B equality t.
  destruct equality.
  reflexivity.
Qed.

(** Every successful result contains a scoped type and reconstructs exactly
    the annotated input.  The context invariant supplies scope for variables;
    the [RCTAbs] case transports it with [closed_context_lift]. *)
Theorem check_core_success :
  forall n context raw,
    Forall (closed n) context ->
    match check_core n context raw with
    | Ok result => InferredSpec n raw result
    | Err _ => True
    end.
Proof.
  intros n context raw.
  revert n context.
  induction raw as
      [index
       | T body IHbody
       | function IHfunction argument IHargument
       | body IHbody
       | function IHfunction T];
    intros n context Hcontext.
  - cbn [check_core lookup_fvar].
    destruct (find_fvar context index)
      as [[T variable] |] eqn:Hfind.
    + unfold lookup_fvar.
      rewrite Hfind.
      cbn [InferredSpec forget scoped].
      split.
      * exact (fvar_closed n context T variable Hcontext).
      * split.
        -- exact I.
        -- f_equal.
           pose proof (find_fvar_position context index) as Hposition.
           rewrite Hfind in Hposition.
           cbn in Hposition.
           exact Hposition.
    + unfold lookup_fvar.
      rewrite Hfind.
      exact I.
  - cbn [check_core].
    destruct (closed_dec n T) as [HT | HT].
    2: exact I.
    specialize (IHbody n (T :: context)).
    assert (Hbody_context : Forall (closed n) (T :: context)).
    { now constructor. }
    specialize (IHbody Hbody_context).
    destruct (check_core n (T :: context) body)
      as [[U body'] | error] eqn:Hcheck.
    + cbn [InferredSpec] in IHbody |- *.
      destruct IHbody as [HU [Hbody_scoped Hforget]].
      split.
      * cbn [closed].
        now split.
      * split.
        -- cbn [scoped].
           now split.
        -- cbn [forget].
           now f_equal.
    + exact I.
  - specialize (IHfunction n context Hcontext).
    specialize (IHargument n context Hcontext).
    cbn [check_core].
    destruct (check_core n context function)
      as [[function_type function'] | error]
      eqn:Hfunction_check.
    2: exact I.
    cbn [InferredSpec] in IHfunction.
    destruct IHfunction
      as [Hfunction_type [Hfunction_scoped Hfunction_forget]].
    destruct function_type as [index | A B | U].
    + exact I.
    + destruct (check_core n context argument)
        as [[argument_type argument'] | error]
        eqn:Hargument_check.
      2: exact I.
      cbn [InferredSpec] in IHargument.
      destruct IHargument
        as [Hargument_type [Hargument_scoped Hargument_forget]].
      destruct (type_eq_dec A argument_type)
        as [Hequality | Hinequality].
      * cbn [InferredSpec].
        cbn [closed] in Hfunction_type.
        destruct Hfunction_type as [HA HB].
        split.
        -- exact HB.
        -- split.
           ++ cbn [scoped].
              now split.
           ++ cbn [forget].
              rewrite forget_cast_fterm.
              now rewrite Hfunction_forget, Hargument_forget.
      * exact I.
    + exact I.
  - specialize
      (IHbody (S n) (map (type_lift 0) context)
        (closed_context_lift n context Hcontext)).
    cbn [check_core].
    destruct
      (check_core (S n) (map (type_lift 0) context) body)
      as [[T body'] | error] eqn:Hcheck.
    + cbn [InferredSpec] in IHbody |- *.
      destruct IHbody as [HT [Hbody_scoped Hbody_forget]].
      split.
      * cbn [closed].
        exact HT.
      * split.
        -- cbn [scoped].
           exact Hbody_scoped.
        -- cbn [forget].
           now f_equal.
    + exact I.
  - cbn [check_core].
    destruct (closed_dec n T) as [HT | HT].
    2: exact I.
    specialize (IHfunction n context Hcontext).
    destruct (check_core n context function)
      as [[function_type function'] | error]
      eqn:Hfunction_check.
    2: exact I.
    cbn [InferredSpec] in IHfunction.
    destruct IHfunction
      as [Hfunction_type [Hfunction_scoped Hfunction_forget]].
    destruct function_type as [index | A B | U].
    + exact I.
    + exact I.
    + cbn [InferredSpec].
      split.
      * apply closed_type_subst0.
        -- cbn [closed] in Hfunction_type.
           exact Hfunction_type.
        -- exact HT.
      * split.
        -- cbn [scoped].
           now split.
        -- cbn [forget].
           now f_equal.
Qed.

Theorem check_core_complete :
  forall n context raw T (t : fterm context T),
    scoped n raw ->
    forget t = raw ->
    exists t' : fterm context T,
      check_core n context raw =
      Ok (existT (fun U => fterm context U) T t').
Proof.
  intros n context raw T t Hscoped Hforget.
  subst raw.
  pose proof
    (check_core_complete_type n context T t Hscoped)
    as Hcomplete.
  destruct (check_core n context (forget t))
    as [[U t'] | error] eqn:Hcheck.
  - cbn in Hcomplete.
    subst U.
    now exists t'.
  - exact (False_rect _ Hcomplete).
Qed.

(** This theorem covers every error constructor at once: an error returned
    by the core rules out any scoped intrinsic typing whose annotations are
    the input term. *)
Theorem check_core_rejected_no_typing :
  forall n context raw error,
    check_core n context raw = Err error ->
    ~ exists T (t : fterm context T),
        scoped n raw /\ forget t = raw.
Proof.
  intros n context raw error Herror
    [T [t [Hscoped Hforget]]].
  destruct
    (check_core_complete n context raw T t Hscoped Hforget)
    as [t' Hsuccess].
  rewrite Herror in Hsuccess.
  discriminate.
Qed.

(** ** Proof-carrying public checker *)

Definition Checked n context raw : Type :=
  {T : type &
    {t : fterm context T |
      closed n T /\ scoped n raw /\ forget t = raw}}.

Definition checked_inferred {n context raw}
    (checked : Checked n context raw) : Inferred context :=
  match checked with
  | existT _ T (exist _ t _) => existT _ T t
  end.

(** [certify] adds only [Prop]-valued evidence to a core result. *)
Definition certify n context raw
    (result : Result TypeError (Inferred context))
    (sound :
      match result with
      | Ok inferred => InferredSpec n raw inferred
      | Err _ => True
      end)
    : Result TypeError (Checked n context raw) :=
  match result as result'
        return
          (match result' with
           | Ok inferred => InferredSpec n raw inferred
           | Err _ => True
           end) ->
          Result TypeError (Checked n context raw)
  with
  | Ok (existT _ T t) =>
      fun proof =>
        Ok (existT _ T (exist _ t proof))
  | Err error => fun _ => Err error
  end sound.

Definition check n context
    (Hcontext : Forall (closed n) context)
    (raw : RawChurch)
    : Result TypeError (Checked n context raw) :=
  certify n context raw
    (check_core n context raw)
    (check_core_success n context raw Hcontext).

Definition checkClosed (raw : RawChurch)
    : Result TypeError (Checked 0 [] raw) :=
  check 0 [] (Forall_nil _) raw.

(** Forgetting a public certificate recovers exactly the computational core,
    including its error. *)
Definition erase_checked_result {n context raw}
    (result : Result TypeError (Checked n context raw))
    : Result TypeError (Inferred context) :=
  match result with
  | Ok checked => Ok (checked_inferred checked)
  | Err error => Err error
  end.

Lemma erase_certify : forall n context raw
    (result : Result TypeError (Inferred context))
    (sound :
      match result with
      | Ok inferred => InferredSpec n raw inferred
      | Err _ => True
      end),
  erase_checked_result (certify n context raw result sound) = result.
Proof.
  intros n context raw [[T t] | error] sound.
  - reflexivity.
  - reflexivity.
Qed.

Theorem check_core_correspondence :
  forall n context (Hcontext : Forall (closed n) context) raw,
    erase_checked_result (check n context Hcontext raw) =
    check_core n context raw.
Proof.
  intros n context Hcontext raw.
  unfold check.
  apply erase_certify.
Qed.

Lemma certify_error : forall n context raw
    (result : Result TypeError (Inferred context))
    (sound :
      match result with
      | Ok inferred => InferredSpec n raw inferred
      | Err _ => True
      end)
    error,
  result = Err error ->
  certify n context raw result sound = Err error.
Proof.
  intros n context raw [[T t] | actual_error] sound error Hresult.
  - discriminate.
  - now inversion Hresult.
Qed.

Lemma certify_accepts : forall n context raw
    (result : Result TypeError (Inferred context))
    (sound :
      match result with
      | Ok inferred => InferredSpec n raw inferred
      | Err _ => True
      end)
    inferred,
  result = Ok inferred ->
  exists checked : Checked n context raw,
    certify n context raw result sound = Ok checked.
Proof.
  intros n context raw [[T t] | error] sound inferred Hresult.
  - inversion Hresult.
    eexists.
    reflexivity.
  - discriminate.
Qed.

Theorem check_error_iff_core :
  forall n context (Hcontext : Forall (closed n) context) raw error,
    check n context Hcontext raw = Err error <->
    check_core n context raw = Err error.
Proof.
  intros n context Hcontext raw error.
  split.
  - intro Hcheck.
    pose proof
      (f_equal erase_checked_result Hcheck)
      as Herased.
    rewrite check_core_correspondence in Herased.
    exact Herased.
  - intro Hcore.
    unfold check.
    now apply certify_error.
Qed.

Theorem checked_contract :
  forall n context raw (checked : Checked n context raw),
    match checked with
    | existT _ T (exist _ t _) =>
        closed n T /\ scoped n raw /\ forget t = raw
    end.
Proof.
  intros n context raw [T [t Hcontract]].
  exact Hcontract.
Qed.

Theorem check_complete :
  forall n context (Hcontext : Forall (closed n) context)
    raw T (t : fterm context T),
    scoped n raw ->
    forget t = raw ->
    exists checked : Checked n context raw,
      check n context Hcontext raw = Ok checked.
Proof.
  intros n context Hcontext raw T t Hscoped Hforget.
  destruct
    (check_core_complete n context raw T t Hscoped Hforget)
    as [t' Hcore].
  unfold check.
  apply certify_accepts
    with (inferred :=
      existT (fun U => fterm context U) T t').
  exact Hcore.
Qed.

Theorem check_rejected_no_typing :
  forall n context (Hcontext : Forall (closed n) context) raw error,
    check n context Hcontext raw = Err error ->
    ~ exists T (t : fterm context T),
        scoped n raw /\ forget t = raw.
Proof.
  intros n context Hcontext raw error Hcheck.
  apply check_core_rejected_no_typing with (error := error).
  now apply (proj1
    (check_error_iff_core n context Hcontext raw error)).
Qed.

Theorem check_accepts_iff_typing :
  forall n context (Hcontext : Forall (closed n) context) raw,
    (exists checked : Checked n context raw,
      check n context Hcontext raw = Ok checked) <->
    (exists T (t : fterm context T),
      scoped n raw /\ forget t = raw).
Proof.
  intros n context Hcontext raw.
  split.
  - intros [checked Hcheck].
    destruct checked as [T [t [HT [Hscoped Hforget]]]].
    now exists T, t.
  - intros [T [t [Hscoped Hforget]]].
    now apply check_complete with (T := T) (t := t).
Qed.

Corollary checkClosed_core_correspondence : forall raw,
  erase_checked_result (checkClosed raw) =
  check_core 0 [] raw.
Proof.
  intro raw.
  apply check_core_correspondence.
Qed.

Corollary checkClosed_accepts_iff_typing : forall raw,
  (exists checked : Checked 0 [] raw,
    checkClosed raw = Ok checked) <->
  (exists T (t : fterm [] T),
    scoped 0 raw /\ forget t = raw).
Proof.
  intro raw.
  unfold checkClosed.
  apply check_accepts_iff_typing.
Qed.

Corollary checkClosed_rejected_no_typing : forall raw error,
  checkClosed raw = Err error ->
  ~ exists T (t : fterm [] T),
      scoped 0 raw /\ forget t = raw.
Proof.
  intros raw error Hcheck.
  unfold checkClosed in Hcheck.
  now apply check_rejected_no_typing
    with (Hcontext := Forall_nil (closed 0)) (error := error).
Qed.

(** ** Consequences used on the lecture slides *)

(** Church-style typing is unique: two intrinsic terms with the same
    annotations have the same type. *)
Theorem church_typing_unique :
  forall n context T T' (t : fterm context T) (t' : fterm context T'),
    scoped n (forget t) ->
    forget t = forget t' ->
    T = T'.
Proof.
  intros n context T T' t t' Hscoped Hforget.
  pose proof (check_core_complete_type n context T t Hscoped) as Ht.
  rewrite Hforget in Ht, Hscoped.
  pose proof (check_core_complete_type n context T' t' Hscoped) as Ht'.
  destruct (check_core n context (forget t')) as [[U _] | error].
  - congruence.
  - contradiction.
Qed.

(** The term handed to [bound] and to the reducer is the erasure of the
    checked input. *)
Corollary checkClosed_erasure :
  forall raw T (t : fterm [] T) proof,
    checkClosed raw = Ok (existT _ T (exist _ t proof)) ->
    fterm_to_term t = erase_raw raw.
Proof.
  intros raw T t [_ [_ Hforget]] _.
  rewrite <- Hforget.
  symmetry.
  apply erase_raw_forget.
Qed.
