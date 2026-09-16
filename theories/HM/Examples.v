(** * Shared Hindley--Milner examples *)

From SystemF.HM Require Import Infer UnifyFailure TypeDAG.

(** Ordinary tree size of the source AST, used to contrast the linear input
    family below with the expanded tree representation of its inferred type. *)
Fixpoint hm_term_tree_size (expression : hmterm) : nat :=
  match expression with
  | var_t _ | const_t _ => 1
  | app_t function argument =>
      1 + hm_term_tree_size function + hm_term_tree_size argument
  | let_t _ bound body =>
      1 + hm_term_tree_size bound + hm_term_tree_size body
  | lam_t _ body => 1 + hm_term_tree_size body
  end.

(** Observable size of the type tree returned by executable W. *)
Definition inferred_type_tree_size (expression : hmterm) : option nat :=
  match runW_exec expression nil with
  | inferred tau _ => Some (ty_size tau)
  | inference_rejected => None
  end.

(** The same W result with all structurally equal type nodes hash-consed. *)
Definition inferred_type_dag (expression : hmterm) : option TypeDAG :=
  match runW_exec expression nil with
  | inferred tau _ => Some (type_to_dag tau)
  | inference_rejected => None
  end.

Definition inferred_type_dag_size (expression : hmterm) : option nat :=
  match inferred_type_dag expression with
  | Some graph => Some (type_dag_size graph)
  | None => None
  end.

(** Compute both observables after one W run.  The extracted benchmark uses
    this entry point so measuring the DAG does not repeat inference. *)
Definition inferred_type_representation_sizes
    (expression : hmterm) : option (nat * nat) :=
  match runW_exec expression nil with
  | inferred tau _ =>
      Some (ty_size tau, type_dag_size (type_to_dag tau))
  | inference_rejected => None
  end.

Theorem inferred_type_dag_correct : forall expression tau substitution,
  runW_exec expression nil = inferred tau substitution ->
  inferred_type_dag expression = Some (type_to_dag tau) /\
  type_dag_decode (type_to_dag tau) = Some tau.
Proof.
  intros expression tau substitution Hinferred.
  split.
  - unfold inferred_type_dag.
    now rewrite Hinferred.
  - apply type_to_dag_correct.
Qed.

(** [fun f -> fun x -> let y = f x in f x], using numeric names as in
    W-in-Coq.  The bound occurrence of [y] is deliberately unused. *)
Definition repeated_application : hmterm :=
  lam_t 0 (lam_t 1
    (let_t 2 (app_t (var_t 0) (var_t 1))
      (app_t (var_t 0) (var_t 1)))).

(** Closed, constant-free end-to-end fixture for term elaboration:
    [let id = fun x => x in id id]. *)
Definition hm_let_identity_self_application : hmterm :=
  let_t 0 (lam_t 1 (var_t 1))
    (app_t (var_t 0) (var_t 0)).

(** A successful W term with an unconstrained type variable that occurs only
    in an internal annotation: [fun x -> (fun y -> x) (fun z -> z)]. *)
Definition hm_dead_internal_type_variable : hmterm :=
  lam_t 0
    (app_t
      (lam_t 1 (var_t 0))
      (lam_t 2 (var_t 2))).

(** Church encoding of a pair constructor at the HM term level:
    [fun left right consumer => consumer left right]. *)
Definition hm_pair : hmterm :=
  lam_t 2 (lam_t 3 (lam_t 4
    (app_t (app_t (var_t 4) (var_t 2)) (var_t 3)))).

(** Apply the shared Church pair constructor.  Identifier [0] is reserved
    for the outer [pair] binding in the generated examples below. *)
Definition hm_pair_application (left right : hmterm) : hmterm :=
  app_t (app_t (var_t 0) left) right.

(** The common tail of the classic bad family

      let x_(i+1) = (x_i, x_i) in ...

    [remaining] is the number of new bindings still to introduce and
    [current] is the source identifier of [x_i].  Names start at [1], since
    [0] denotes the single outer Church-pair binding.  This syntax is linear
    in [remaining]; it is the inferred type that may expand dramatically. *)
Fixpoint hm_pair_dup_lets (remaining current : nat) : hmterm :=
  match remaining with
  | 0 => var_t current
  | S remaining' =>
      let next := S current in
      let_t next
        (hm_pair_application (var_t current) (var_t current))
        (hm_pair_dup_lets remaining' next)
  end.

(** Monomorphic base:

      let pair = ... in
      fun x_0 => let x_1 = (x_0, x_0) in ... x_n

    Repeated occurrences of the type of [x_0] make its printed type tree
    exponential, although a representation that shares equal subtrees can
    retain a linear spine. *)
Definition hm_monomorphic_pair_dup_family (depth : nat) : hmterm :=
  let_t 0 hm_pair
    (lam_t 1 (hm_pair_dup_lets depth 1)).

(** Let-polymorphic base:

      let pair = ... in
      let x_0 = fun x => x in
      let x_1 = (x_0, x_0) in ... x_n

    Each use of a generalized [x_i] is instantiated freshly.  The identity
    binder is chosen above every generated [x_i] name merely to keep printed
    source names unambiguous; lexical scoping would also permit shadowing. *)
Definition hm_polymorphic_pair_dup_family (depth : nat) : hmterm :=
  let identity_name := S (S depth) in
  let_t 0 hm_pair
    (let_t 1 (lam_t identity_name (var_t identity_name))
      (hm_pair_dup_lets depth 1)).

(** A type-level control for the sharing experiment.  It models a genuinely
    monomorphic pair constructor whose result type is the fixed closed marker
    [con 0].  If [previous] is duplicated at every level, its ordinary tree is
    exponential; [type_to_dag] stores [previous] once and adds only three arrow
    nodes per level (plus the one shared result constant).

    The executable HM source above uses a Church pair because the imported
    language has no primitive products.  Its result variable is generalized at
    [let], so fresh instantiations can destroy some of precisely this sharing.
    Keeping this control next to the real W family makes that distinction
    observable rather than hiding it in a printer. *)
Definition hm_fixed_result_pair_type
    (result left right : ty) : ty :=
  arrow (arrow left (arrow right result)) result.

Fixpoint hm_monomorphic_shared_pair_type (depth : nat) : ty :=
  match depth with
  | 0 => var 0
  | S depth' =>
      let previous := hm_monomorphic_shared_pair_type depth' in
      hm_fixed_result_pair_type (con 0) previous previous
  end.

Definition hm_monomorphic_shared_pair_type_tree_size (depth : nat) : nat :=
  ty_size (hm_monomorphic_shared_pair_type depth).

Definition hm_monomorphic_shared_pair_type_dag_size (depth : nat) : nat :=
  type_dag_size (type_to_dag (hm_monomorphic_shared_pair_type depth)).

(** Main W trace example from the plan:

    [let pair = fun left right consumer => consumer left right in
     let id = fun x => x in pair (id 0) (id true)]

    Constants [0] and [1] are distinct type markers [con 0] and [con 1].
    There is no primitive product in the imported HM syntax. *)
Definition polymorphic_pair_application : hmterm :=
  let_t 0 hm_pair
    (let_t 1 (lam_t 2 (var_t 2))
      (app_t
        (app_t (var_t 0) (app_t (var_t 1) (const_t 0)))
        (app_t (var_t 1) (const_t 1)))).

Definition infer_succeeds (e : hmterm) : bool :=
  match runW e nil with
  | inl _ => true
  | inr _ => false
  end.

Definition infer_exec_succeeds (e : hmterm) : bool :=
  match runW_exec e nil with
  | inferred _ _ => true
  | inference_rejected => false
  end.
