(** * Church-style checker

    Church-style [fterm] terms carry every annotation needed by System F
    checking but deliberately carry no typing evidence.  [check_core] turns
    accepted inputs into intrinsically typed derivations [fderiv];
    [check]/[checkClosed] add a [Prop]-valued certificate ([Checked]) on top
    of the same result.  The correctness statements are relative to
    [forget]: acceptance is equivalent to the existence of a derivation with
    exactly the input's annotations, and rejection excludes every such
    derivation. *)

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

From SystemF.F Require Import Syntax Scope.

Inductive fterm : Type :=
| FVar : nat -> fterm
| FLam : type -> fterm -> fterm
| FApp : fterm -> fterm -> fterm
| FTLam : fterm -> fterm
| FTApp : fterm -> type -> fterm.

Implicit Types
  (n m : nat)
  (raw : fterm).

(** [scoped n raw] checks only type-variable scope.  Term-variable indices
    are checked against the term context by the future intrinsic checker. *)
Fixpoint scoped (n : nat) (raw : fterm) : Prop :=
  match raw with
  | FVar _ => True
  | FLam T body => closed n T /\ scoped n body
  | FApp function argument =>
      scoped n function /\ scoped n argument
  | FTLam body => scoped (S n) body
  | FTApp function T => scoped n function /\ closed n T
  end.

Fixpoint scoped_dec (n : nat) (raw : fterm) :
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
Fixpoint find_dvar (ctx : list type) (index : nat)
    : option {T : type & dvar ctx T} :=
  match ctx as ctx'
        return option {T : type & dvar ctx' T} with
  | [] => None
  | T :: ctx' =>
      match index with
      | 0 => Some (existT _ T (@DVar0 ctx' T))
      | S index' =>
          match find_dvar ctx' index' with
          | None => None
          | Some (existT _ U variable) =>
              Some (existT _ U (@DVarS ctx' U T variable))
          end
      end
  end.

Definition lookup_dvar (ctx : list type) (index : nat)
    : Result TypeError {T : type & dvar ctx T} :=
  match find_dvar ctx index with
  | Some variable => Ok variable
  | None => Err (UnboundTermVariable index)
  end.

Lemma dvar_nth_error : forall ctx T (variable : dvar ctx T),
  nth_error ctx (dvar_to_nat variable) = Some T.
Proof.
  intros ctx T variable.
  induction variable; cbn [dvar_to_nat]; assumption || reflexivity.
Qed.

Lemma dvar_closed : forall n ctx T (variable : dvar ctx T),
  Forall (closed n) ctx -> closed n T.
Proof.
  intros n ctx T variable Hctx.
  apply (closed_nth_error n ctx (dvar_to_nat variable) T Hctx).
  apply dvar_nth_error.
Qed.

Lemma find_dvar_position : forall ctx index,
  match find_dvar ctx index with
  | Some (existT _ T variable) => dvar_to_nat variable = index
  | None => True
  end.
Proof.
  induction ctx as [| T ctx IH]; intros [| index];
    cbn [find_dvar].
  - exact I.
  - exact I.
  - reflexivity.
  - destruct (find_dvar ctx index) as [[U variable] |]
      eqn:Hfind.
    + cbn.
      specialize (IH index).
      rewrite Hfind in IH.
      cbn in IH.
      now f_equal.
    + exact I.
Qed.

Lemma find_dvar_complete : forall ctx T (variable : dvar ctx T),
  exists variable' : dvar ctx T,
    find_dvar ctx (dvar_to_nat variable) =
    Some (existT (fun T => dvar ctx T) T variable').
Proof.
  intros ctx T variable.
  induction variable as [ctx T | ctx T U variable IH].
  - exists (@DVar0 ctx T).
    reflexivity.
  - destruct IH as [variable' Hfind].
    exists (@DVarS ctx T U variable').
    cbn [find_dvar dvar_to_nat].
    now rewrite Hfind.
Qed.

(** ** Computational checking core *)

Definition Inferred (ctx : list type) : Type :=
  {T : type & fderiv ctx T}.

(** Application checking needs to transport the inferred argument across the
    proof returned by [type_eq_dec]. *)
Definition cast_fderiv {ctx A B}
    (equality : A = B) (t : fderiv ctx B) : fderiv ctx A :=
  eq_rect B (fun T => fderiv ctx T) t A (eq_sym equality).

Fixpoint check_core
    (n : nat) (ctx : list type) (raw : fterm)
    : Result TypeError (Inferred ctx) :=
  match raw with
  | FVar index =>
      match lookup_dvar ctx index with
      | Err error => Err error
      | Ok (existT _ T variable) =>
          Ok (existT _ T (DVar variable))
      end
  | FLam T body =>
      match closed_dec n T with
      | right _ => Err (TypeAnnotationOutOfScope T)
      | left _ =>
          match check_core n (T :: ctx) body with
          | Err error => Err error
          | Ok (existT _ U body') =>
              Ok (existT _ (TArrow T U) (DLam body'))
          end
      end
  | FApp function argument =>
      match check_core n ctx function with
      | Err error => Err error
      | Ok (existT _ function_type function') =>
          match function_type as function_type'
                return
                  fderiv ctx function_type' ->
                  Result TypeError (Inferred ctx)
          with
          | TArrow T U =>
              fun function' =>
                match check_core n ctx argument with
                | Err error => Err error
                | Ok (existT _ V argument') =>
                    match type_eq_dec T V with
                    | left equality =>
                        Ok (existT _ U
                          (DApp function'
                            (cast_fderiv equality argument')))
                    | right _ => Err (TypeMismatch T V)
                    end
                end
          | TVar index =>
              fun _ => Err (ExpectedArrow (TVar index))
          | TForall T =>
              fun _ => Err (ExpectedArrow (TForall T))
          end function'
      end
  | FTLam body =>
      match
        check_core (S n) (map (type_lift 0) ctx) body
      with
      | Err error => Err error
      | Ok (existT _ T body') =>
          Ok (existT _ (TForall T) (DTLam body'))
      end
  | FTApp function T =>
      match closed_dec n T with
      | right _ => Err (TypeArgumentOutOfScope T)
      | left _ =>
          match check_core n ctx function with
          | Err error => Err error
          | Ok (existT _ function_type function') =>
              match function_type as function_type'
                    return
                      fderiv ctx function_type' ->
                      Result TypeError (Inferred ctx)
              with
              | TForall U =>
                  fun function' =>
                    Ok (existT _ (type_subst 0 U T)
                      (DTApp function' T))
              | TVar index =>
                  fun _ => Err (ExpectedForall (TVar index))
              | TArrow U V =>
                  fun _ => Err (ExpectedForall (TArrow U V))
              end function'
          end
      end
  end.

(** Forget intrinsic typing while retaining all Church-style annotations. *)
Fixpoint forget {ctx T} (t : fderiv ctx T) : fterm :=
  match t with
  | DVar variable => FVar (dvar_to_nat variable)
  | @DLam _ A _ body => FLam A (forget body)
  | DApp function argument => FApp (forget function) (forget argument)
  | DTLam body => FTLam (forget body)
  | DTApp function U => FTApp (forget function) U
  end.

(** Erasure of raw Church syntax removes types and type-level constructs. *)
Fixpoint fterm_to_term (raw : fterm) : term :=
  match raw with
  | FVar index => Var index
  | FLam _ body => Lam (fterm_to_term body)
  | FApp function argument =>
      App (fterm_to_term function) (fterm_to_term argument)
  | FTLam body => fterm_to_term body
  | FTApp function _ => fterm_to_term function
  end.

Theorem fterm_to_term_forget : forall ctx T (t : fderiv ctx T),
  fterm_to_term (forget t) = fderiv_to_term t.
Proof.
  intros ctx T t.
  induction t; cbn [forget fterm_to_term fderiv_to_term]; congruence.
Qed.

(** ** Soundness and completeness of the computational core *)

(** Completeness first records that rechecking a scoped intrinsic term
    succeeds with the same result type.  The concrete proof term may differ
    because variable lookup and equality casts reconstruct witnesses. *)
Theorem check_core_complete_type :
  forall n ctx T (t : fderiv ctx T),
    scoped n (forget t) ->
    match check_core n ctx (forget t) with
    | Ok (existT _ U _) => U = T
    | Err _ => False
    end.
Proof.
  intros n ctx T t.
  revert n.
  induction t as
      [ctx T variable
       | ctx T U body IHbody
       | ctx T U function IHfunction argument IHargument
       | ctx T body IHbody
       | ctx T function IHfunction U];
    intros n Hscoped.
  - cbn [forget] in Hscoped |- *.
    destruct (find_dvar_complete ctx T variable)
      as [variable' Hfind].
    cbn [check_core].
    unfold lookup_dvar.
    rewrite Hfind.
    reflexivity.
  - cbn [forget scoped] in Hscoped.
    destruct Hscoped as [HT Hbody].
    specialize (IHbody n Hbody).
    cbn [forget check_core].
    destruct (closed_dec n T) as [HT' | HT']; [| contradiction].
    destruct (check_core n (T :: ctx) (forget body))
      as [[V body'] | error] eqn:Hcheck.
    + cbn.
      now f_equal.
    + exact IHbody.
  - cbn [forget scoped] in Hscoped.
    destruct Hscoped as [Hfunction Hargument].
    specialize (IHfunction n Hfunction).
    specialize (IHargument n Hargument).
    cbn [forget check_core].
    destruct (check_core n ctx (forget function))
      as [[function_type function'] | error]
      eqn:Hfunction_check.
    + cbn in IHfunction.
      subst function_type.
      destruct (check_core n ctx (forget argument))
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
      (check_core (S n) (map (type_lift 0) ctx) (forget body))
      as [[U body'] | error] eqn:Hcheck.
    + cbn in IHbody.
      now f_equal.
    + exact IHbody.
  - cbn [forget scoped] in Hscoped.
    destruct Hscoped as [Hfunction HU].
    specialize (IHfunction n Hfunction).
    cbn [forget check_core].
    destruct (closed_dec n U) as [HU' | HU']; [| contradiction].
    destruct (check_core n ctx (forget function))
      as [[function_type function'] | error] eqn:Hcheck.
    + cbn in IHfunction.
      subst function_type.
      reflexivity.
    + exact IHfunction.
Qed.

Definition InferredSpec n raw {ctx}
    (result : Inferred ctx) : Prop :=
  match result with
  | existT _ T t =>
      closed n T /\ scoped n raw /\ forget t = raw
  end.

Lemma forget_cast_fderiv : forall ctx A B
    (equality : A = B) (t : fderiv ctx B),
  forget (cast_fderiv equality t) = forget t.
Proof.
  intros ctx A B equality t.
  destruct equality.
  reflexivity.
Qed.

(** Every successful result contains a scoped type and reconstructs exactly
    the annotated input.  The context invariant supplies scope for variables;
    the [FTLam] case transports it with [closed_ctx_lift]. *)
Theorem check_core_success :
  forall n ctx raw,
    Forall (closed n) ctx ->
    match check_core n ctx raw with
    | Ok result => InferredSpec n raw result
    | Err _ => True
    end.
Proof.
  intros n ctx raw.
  revert n ctx.
  induction raw as
      [index
       | T body IHbody
       | function IHfunction argument IHargument
       | body IHbody
       | function IHfunction T];
    intros n ctx Hctx.
  - cbn [check_core lookup_dvar].
    destruct (find_dvar ctx index)
      as [[T variable] |] eqn:Hfind.
    + unfold lookup_dvar.
      rewrite Hfind.
      cbn [InferredSpec forget scoped].
      split.
      * exact (dvar_closed n ctx T variable Hctx).
      * split.
        -- exact I.
        -- f_equal.
           pose proof (find_dvar_position ctx index) as Hposition.
           rewrite Hfind in Hposition.
           cbn in Hposition.
           exact Hposition.
    + unfold lookup_dvar.
      rewrite Hfind.
      exact I.
  - cbn [check_core].
    destruct (closed_dec n T) as [HT | HT].
    2: exact I.
    specialize (IHbody n (T :: ctx)).
    assert (Hbody_ctx : Forall (closed n) (T :: ctx)).
    { now constructor. }
    specialize (IHbody Hbody_ctx).
    destruct (check_core n (T :: ctx) body)
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
  - specialize (IHfunction n ctx Hctx).
    specialize (IHargument n ctx Hctx).
    cbn [check_core].
    destruct (check_core n ctx function)
      as [[function_type function'] | error]
      eqn:Hfunction_check.
    2: exact I.
    cbn [InferredSpec] in IHfunction.
    destruct IHfunction
      as [Hfunction_type [Hfunction_scoped Hfunction_forget]].
    destruct function_type as [index | A B | U].
    + exact I.
    + destruct (check_core n ctx argument)
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
              rewrite forget_cast_fderiv.
              now rewrite Hfunction_forget, Hargument_forget.
      * exact I.
    + exact I.
  - specialize
      (IHbody (S n) (map (type_lift 0) ctx)
        (closed_ctx_lift n ctx Hctx)).
    cbn [check_core].
    destruct
      (check_core (S n) (map (type_lift 0) ctx) body)
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
    specialize (IHfunction n ctx Hctx).
    destruct (check_core n ctx function)
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
  forall n ctx raw T (t : fderiv ctx T),
    scoped n raw ->
    forget t = raw ->
    exists t' : fderiv ctx T,
      check_core n ctx raw =
      Ok (existT (fun U => fderiv ctx U) T t').
Proof.
  intros n ctx raw T t Hscoped Hforget.
  subst raw.
  pose proof
    (check_core_complete_type n ctx T t Hscoped)
    as Hcomplete.
  destruct (check_core n ctx (forget t))
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
  forall n ctx raw error,
    check_core n ctx raw = Err error ->
    ~ exists T (t : fderiv ctx T),
        scoped n raw /\ forget t = raw.
Proof.
  intros n ctx raw error Herror
    [T [t [Hscoped Hforget]]].
  destruct
    (check_core_complete n ctx raw T t Hscoped Hforget)
    as [t' Hsuccess].
  rewrite Herror in Hsuccess.
  discriminate.
Qed.

(** ** Proof-carrying public checker *)

Definition Checked n ctx raw : Type :=
  {T : type &
    {t : fderiv ctx T |
      closed n T /\ scoped n raw /\ forget t = raw}}.

Definition checked_inferred {n ctx raw}
    (checked : Checked n ctx raw) : Inferred ctx :=
  match checked with
  | existT _ T (exist _ t _) => existT _ T t
  end.

(** [certify] adds only [Prop]-valued evidence to a core result. *)
Definition certify n ctx raw
    (result : Result TypeError (Inferred ctx))
    (sound :
      match result with
      | Ok inferred => InferredSpec n raw inferred
      | Err _ => True
      end)
    : Result TypeError (Checked n ctx raw) :=
  match result as result'
        return
          (match result' with
           | Ok inferred => InferredSpec n raw inferred
           | Err _ => True
           end) ->
          Result TypeError (Checked n ctx raw)
  with
  | Ok (existT _ T t) =>
      fun proof =>
        Ok (existT _ T (exist _ t proof))
  | Err error => fun _ => Err error
  end sound.

Definition check n ctx
    (Hctx : Forall (closed n) ctx)
    (raw : fterm)
    : Result TypeError (Checked n ctx raw) :=
  certify n ctx raw
    (check_core n ctx raw)
    (check_core_success n ctx raw Hctx).

Definition checkClosed (raw : fterm)
    : Result TypeError (Checked 0 [] raw) :=
  check 0 [] (Forall_nil _) raw.

(** Forgetting a public certificate recovers exactly the computational core,
    including its error. *)
Definition erase_checked_result {n ctx raw}
    (result : Result TypeError (Checked n ctx raw))
    : Result TypeError (Inferred ctx) :=
  match result with
  | Ok checked => Ok (checked_inferred checked)
  | Err error => Err error
  end.

Lemma erase_certify : forall n ctx raw
    (result : Result TypeError (Inferred ctx))
    (sound :
      match result with
      | Ok inferred => InferredSpec n raw inferred
      | Err _ => True
      end),
  erase_checked_result (certify n ctx raw result sound) = result.
Proof.
  intros n ctx raw [[T t] | error] sound.
  - reflexivity.
  - reflexivity.
Qed.

Theorem check_core_correspondence :
  forall n ctx (Hctx : Forall (closed n) ctx) raw,
    erase_checked_result (check n ctx Hctx raw) =
    check_core n ctx raw.
Proof.
  intros n ctx Hctx raw.
  unfold check.
  apply erase_certify.
Qed.

Lemma certify_error : forall n ctx raw
    (result : Result TypeError (Inferred ctx))
    (sound :
      match result with
      | Ok inferred => InferredSpec n raw inferred
      | Err _ => True
      end)
    error,
  result = Err error ->
  certify n ctx raw result sound = Err error.
Proof.
  intros n ctx raw [[T t] | actual_error] sound error Hresult.
  - discriminate.
  - now inversion Hresult.
Qed.

Lemma certify_accepts : forall n ctx raw
    (result : Result TypeError (Inferred ctx))
    (sound :
      match result with
      | Ok inferred => InferredSpec n raw inferred
      | Err _ => True
      end)
    inferred,
  result = Ok inferred ->
  exists checked : Checked n ctx raw,
    certify n ctx raw result sound = Ok checked.
Proof.
  intros n ctx raw [[T t] | error] sound inferred Hresult.
  - inversion Hresult.
    eexists.
    reflexivity.
  - discriminate.
Qed.

Theorem check_error_iff_core :
  forall n ctx (Hctx : Forall (closed n) ctx) raw error,
    check n ctx Hctx raw = Err error <->
    check_core n ctx raw = Err error.
Proof.
  intros n ctx Hctx raw error.
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
  forall n ctx raw (checked : Checked n ctx raw),
    match checked with
    | existT _ T (exist _ t _) =>
        closed n T /\ scoped n raw /\ forget t = raw
    end.
Proof.
  intros n ctx raw [T [t Hcontract]].
  exact Hcontract.
Qed.

Theorem check_complete :
  forall n ctx (Hctx : Forall (closed n) ctx)
    raw T (t : fderiv ctx T),
    scoped n raw ->
    forget t = raw ->
    exists checked : Checked n ctx raw,
      check n ctx Hctx raw = Ok checked.
Proof.
  intros n ctx Hctx raw T t Hscoped Hforget.
  destruct
    (check_core_complete n ctx raw T t Hscoped Hforget)
    as [t' Hcore].
  unfold check.
  apply certify_accepts
    with (inferred :=
      existT (fun U => fderiv ctx U) T t').
  exact Hcore.
Qed.

Theorem check_rejected_no_typing :
  forall n ctx (Hctx : Forall (closed n) ctx) raw error,
    check n ctx Hctx raw = Err error ->
    ~ exists T (t : fderiv ctx T),
        scoped n raw /\ forget t = raw.
Proof.
  intros n ctx Hctx raw error Hcheck.
  apply check_core_rejected_no_typing with (error := error).
  now apply (proj1
    (check_error_iff_core n ctx Hctx raw error)).
Qed.

Theorem check_accepts_iff_typing :
  forall n ctx (Hctx : Forall (closed n) ctx) raw,
    (exists checked : Checked n ctx raw,
      check n ctx Hctx raw = Ok checked) <->
    (exists T (t : fderiv ctx T),
      scoped n raw /\ forget t = raw).
Proof.
  intros n ctx Hctx raw.
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
  (exists T (t : fderiv [] T),
    scoped 0 raw /\ forget t = raw).
Proof.
  intro raw.
  unfold checkClosed.
  apply check_accepts_iff_typing.
Qed.

Corollary checkClosed_rejected_no_typing : forall raw error,
  checkClosed raw = Err error ->
  ~ exists T (t : fderiv [] T),
      scoped 0 raw /\ forget t = raw.
Proof.
  intros raw error Hcheck.
  unfold checkClosed in Hcheck.
  now apply check_rejected_no_typing
    with (Hctx := Forall_nil (closed 0)) (error := error).
Qed.

(** ** Consequences used on the lecture slides *)

(** Church-style typing is unique: two intrinsic terms with the same
    annotations have the same type. *)
Theorem church_typing_unique :
  forall n ctx T T' (t : fderiv ctx T) (t' : fderiv ctx T'),
    scoped n (forget t) ->
    forget t = forget t' ->
    T = T'.
Proof.
  intros n ctx T T' t t' Hscoped Hforget.
  pose proof (check_core_complete_type n ctx T t Hscoped) as Ht.
  rewrite Hforget in Ht, Hscoped.
  pose proof (check_core_complete_type n ctx T' t' Hscoped) as Ht'.
  destruct (check_core n ctx (forget t')) as [[U _] | error].
  - congruence.
  - contradiction.
Qed.

(** The term handed to [bound] and to the reducer is the erasure of the
    checked input. *)
Corollary checkClosed_erasure :
  forall raw T (t : fderiv [] T) proof,
    checkClosed raw = Ok (existT _ T (exist _ t proof)) ->
    fderiv_to_term t = fterm_to_term raw.
Proof.
  intros raw T t [_ [_ Hforget]] _.
  rewrite <- Hforget.
  symmetry.
  apply fterm_to_term_forget.
Qed.
