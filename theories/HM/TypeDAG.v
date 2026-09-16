(** * Maximally shared DAGs for inferred HM types

    [ty] is intentionally the small tree datatype inherited from W-in-Coq.
    It is ideal for proofs, but a printed type can contain exponentially many
    repeated subtrees.  This module gives the extracted/demo boundary an
    explicit graph representation: every distinct node descriptor is interned
    once, arrows refer to their children by numeric node identifiers, and the
    root is another identifier.

    Nodes are emitted bottom-up.  Consequently every graph produced by
    [type_to_dag] is acyclic (an arrow only points to nodes that already
    existed).  [type_dag_height] is small decoding metadata; it bounds the
    recursive interpreter and does not duplicate the represented type. *)

From Stdlib Require Import List Arith Lia.
From SystemF.HM.W Require Import SimpleTypes.

Import ListNotations.

Set Implicit Arguments.

Inductive TypeDAGNode : Set :=
| type_dag_var : id -> TypeDAGNode
| type_dag_con : id -> TypeDAGNode
| type_dag_arrow : nat -> nat -> TypeDAGNode.

Definition type_dag_node_eq_dec :
  forall left right : TypeDAGNode, {left = right} + {left <> right}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Record TypeDAG : Set := {
  type_dag_nodes : list TypeDAGNode;
  type_dag_root : nat;
  type_dag_height : nat
}.

Definition type_dag_size (graph : TypeDAG) : nat :=
  length (type_dag_nodes graph).

(** The first matching identifier is canonical. *)
Fixpoint find_type_dag_node
    (needle : TypeDAGNode)
    (nodes : list TypeDAGNode) : option nat :=
  match nodes with
  | [] => None
  | node :: tail =>
      if type_dag_node_eq_dec needle node then Some 0
      else option_map S (find_type_dag_node needle tail)
  end.

(** Interning either reuses an existing identifier or appends one fresh node.
    Appending preserves all identifiers already stored in arrow nodes. *)
Definition intern_type_dag_node
    (node : TypeDAGNode)
    (nodes : list TypeDAGNode) : nat * list TypeDAGNode :=
  match find_type_dag_node node nodes with
  | Some identifier => (identifier, nodes)
  | None => (length nodes, nodes ++ [node])
  end.

Fixpoint type_to_dag_acc
    (source : ty)
    (nodes : list TypeDAGNode) : nat * list TypeDAGNode :=
  match source with
  | var variable => intern_type_dag_node (type_dag_var variable) nodes
  | con constant => intern_type_dag_node (type_dag_con constant) nodes
  | arrow domain codomain =>
      let '(domain_id, domain_nodes) := type_to_dag_acc domain nodes in
      let '(codomain_id, codomain_nodes) :=
        type_to_dag_acc codomain domain_nodes in
      intern_type_dag_node
        (type_dag_arrow domain_id codomain_id) codomain_nodes
  end.

Fixpoint type_tree_height (source : ty) : nat :=
  match source with
  | var _ | con _ => 1
  | arrow domain codomain =>
      S (Nat.max (type_tree_height domain) (type_tree_height codomain))
  end.

Definition type_to_dag (source : ty) : TypeDAG :=
  let '(root, nodes) := type_to_dag_acc source [] in
  {| type_dag_nodes := nodes;
     type_dag_root := root;
     type_dag_height := type_tree_height source |}.

(** Interpret an explicit graph as a tree.  The fuel also makes this function
    safe on arbitrary, possibly cyclic values received across extraction. *)
Fixpoint type_dag_decode_fuel
    (fuel : nat)
    (nodes : list TypeDAGNode)
    (root : nat) : option ty :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match nth_error nodes root with
      | Some (type_dag_var variable) => Some (var variable)
      | Some (type_dag_con constant) => Some (con constant)
      | Some (type_dag_arrow domain_id codomain_id) =>
          match type_dag_decode_fuel fuel' nodes domain_id,
                type_dag_decode_fuel fuel' nodes codomain_id with
          | Some domain, Some codomain => Some (arrow domain codomain)
          | _, _ => None
          end
      | None => None
      end
  end.

Definition type_dag_decode (graph : TypeDAG) : option ty :=
  type_dag_decode_fuel
    (S (type_dag_height graph))
    (type_dag_nodes graph)
    (type_dag_root graph).

Lemma find_type_dag_node_sound : forall needle nodes identifier,
  find_type_dag_node needle nodes = Some identifier ->
  nth_error nodes identifier = Some needle.
Proof.
  intros needle nodes.
  induction nodes as [|node tail IH]; intros identifier Hfind.
  - discriminate.
  - cbn in Hfind.
    destruct (type_dag_node_eq_dec needle node) as [Hequal | Hdifferent].
    + inversion Hfind; subst.
      reflexivity.
    + destruct (find_type_dag_node needle tail) as [tail_id |] eqn:Htail;
        inversion Hfind; subst.
      cbn.
      now apply IH.
Qed.

Lemma find_type_dag_node_none_not_in : forall needle nodes,
  find_type_dag_node needle nodes = None ->
  ~ In needle nodes.
Proof.
  intros needle nodes.
  induction nodes as [|node tail IH]; intro Hfind.
  - cbn. tauto.
  - cbn in Hfind.
    destruct (type_dag_node_eq_dec needle node) as [Hequal | Hdifferent].
    + discriminate.
    + destruct (find_type_dag_node needle tail) as [identifier |]
        eqn:Htail; [discriminate |].
      intro Hin.
      destruct Hin as [Hequal | Hin].
      * now apply Hdifferent.
      * now apply (IH eq_refl).
Qed.

Lemma nth_error_app_some : forall {A : Type} (prefix suffix : list A)
    identifier value,
  nth_error prefix identifier = Some value ->
  nth_error (prefix ++ suffix) identifier = Some value.
Proof.
  intros A prefix.
  induction prefix as [|head tail IH]; intros suffix identifier value Hlookup.
  - destruct identifier; discriminate.
  - destruct identifier as [|identifier']; cbn in *.
    + exact Hlookup.
    + now apply IH.
Qed.

Lemma intern_type_dag_node_at : forall node nodes identifier nodes' suffix,
  intern_type_dag_node node nodes = (identifier, nodes') ->
  nth_error (nodes' ++ suffix) identifier = Some node.
Proof.
  intros node nodes identifier nodes' suffix Hintern.
  unfold intern_type_dag_node in Hintern.
  destruct (find_type_dag_node node nodes) as [found |] eqn:Hfind.
  - inversion Hintern; subst.
    apply nth_error_app_some.
    now apply find_type_dag_node_sound in Hfind.
  - inversion Hintern; subst.
    rewrite <- app_assoc, nth_error_app2 by lia.
    replace (length nodes - length nodes) with 0 by lia.
    reflexivity.
Qed.

Lemma intern_type_dag_node_extends : forall node nodes identifier nodes',
  intern_type_dag_node node nodes = (identifier, nodes') ->
  exists suffix, nodes' = nodes ++ suffix.
Proof.
  intros node nodes identifier nodes' Hintern.
  unfold intern_type_dag_node in Hintern.
  destruct (find_type_dag_node node nodes) as [found |] eqn:Hfind.
  - inversion Hintern; subst.
    exists [].
    now rewrite app_nil_r.
  - inversion Hintern; subst.
    now exists [node].
Qed.

Lemma intern_type_dag_node_preserves_NoDup :
  forall node nodes identifier nodes',
  NoDup nodes ->
  intern_type_dag_node node nodes = (identifier, nodes') ->
  NoDup nodes'.
Proof.
  intros node nodes identifier nodes' Hunique Hintern.
  unfold intern_type_dag_node in Hintern.
  destruct (find_type_dag_node node nodes) as [found |] eqn:Hfind.
  - now inversion Hintern; subst.
  - inversion Hintern; subst.
    apply NoDup_app.
    + exact Hunique.
    + repeat constructor; simpl; tauto.
    + intros value Hin Hsingleton.
      cbn in Hsingleton.
      destruct Hsingleton as [Hequal | Hfalse]; [|contradiction].
      subst value.
      now apply (@find_type_dag_node_none_not_in node nodes Hfind).
Qed.

Lemma type_to_dag_acc_extends : forall source nodes root nodes',
  type_to_dag_acc source nodes = (root, nodes') ->
  exists suffix, nodes' = nodes ++ suffix.
Proof.
  induction source as [variable | constant | domain IHdomain codomain IHcodomain];
    intros nodes root nodes' Hbuild.
  - cbn in Hbuild.
    eapply intern_type_dag_node_extends; exact Hbuild.
  - cbn in Hbuild.
    eapply intern_type_dag_node_extends; exact Hbuild.
  - cbn in Hbuild.
    destruct (type_to_dag_acc domain nodes) as [domain_id domain_nodes]
      eqn:Hdomain.
    destruct (type_to_dag_acc codomain domain_nodes)
      as [codomain_id codomain_nodes] eqn:Hcodomain.
    destruct (intern_type_dag_node
      (type_dag_arrow domain_id codomain_id) codomain_nodes)
      as [arrow_id arrow_nodes] eqn:Harrow.
    inversion Hbuild; subst root nodes'.
    destruct (IHdomain _ _ _ Hdomain) as [domain_suffix Hdomain_nodes].
    destruct (IHcodomain _ _ _ Hcodomain)
      as [codomain_suffix Hcodomain_nodes].
    destruct (@intern_type_dag_node_extends
      (type_dag_arrow domain_id codomain_id) codomain_nodes
      arrow_id arrow_nodes Harrow)
      as [arrow_suffix Harrow_nodes].
    exists (domain_suffix ++ codomain_suffix ++ arrow_suffix).
    subst domain_nodes codomain_nodes arrow_nodes.
    now repeat rewrite app_assoc.
Qed.

Lemma type_to_dag_acc_preserves_NoDup : forall source nodes root nodes',
  NoDup nodes ->
  type_to_dag_acc source nodes = (root, nodes') ->
  NoDup nodes'.
Proof.
  induction source as [variable | constant | domain IHdomain codomain IHcodomain];
    intros nodes root nodes' Hunique Hbuild.
  - cbn in Hbuild.
    eapply intern_type_dag_node_preserves_NoDup; eassumption.
  - cbn in Hbuild.
    eapply intern_type_dag_node_preserves_NoDup; eassumption.
  - cbn in Hbuild.
    destruct (type_to_dag_acc domain nodes) as [domain_id domain_nodes]
      eqn:Hdomain.
    destruct (type_to_dag_acc codomain domain_nodes)
      as [codomain_id codomain_nodes] eqn:Hcodomain.
    destruct (intern_type_dag_node
      (type_dag_arrow domain_id codomain_id) codomain_nodes)
      as [arrow_id arrow_nodes] eqn:Harrow.
    inversion Hbuild; subst root nodes'.
    eapply intern_type_dag_node_preserves_NoDup; [|exact Harrow].
    eapply IHcodomain; [|exact Hcodomain].
    eapply IHdomain; eassumption.
Qed.

Theorem type_to_dag_has_unique_nodes : forall source,
  NoDup (type_dag_nodes (type_to_dag source)).
Proof.
  intro source.
  unfold type_to_dag.
  destruct (type_to_dag_acc source []) as [root nodes] eqn:Hbuild.
  cbn.
  eapply type_to_dag_acc_preserves_NoDup; [constructor | exact Hbuild].
Qed.

(** Correctness is stated for any future suffix: later interned nodes cannot
    change the meaning of an identifier already returned by the builder. *)
Theorem type_to_dag_acc_correct : forall source nodes root nodes',
  type_to_dag_acc source nodes = (root, nodes') ->
  forall suffix fuel,
    type_tree_height source < fuel ->
    type_dag_decode_fuel fuel (nodes' ++ suffix) root = Some source.
Proof.
  induction source as [variable | constant | domain IHdomain codomain IHcodomain];
    intros nodes root nodes' Hbuild suffix fuel Hfuel.
  - cbn in Hbuild.
    destruct fuel as [|fuel']; [lia |].
    cbn [type_dag_decode_fuel].
    erewrite intern_type_dag_node_at by exact Hbuild.
    reflexivity.
  - cbn in Hbuild.
    destruct fuel as [|fuel']; [lia |].
    cbn [type_dag_decode_fuel].
    erewrite intern_type_dag_node_at by exact Hbuild.
    reflexivity.
  - cbn in Hbuild.
    destruct (type_to_dag_acc domain nodes) as [domain_id domain_nodes]
      eqn:Hdomain.
    destruct (type_to_dag_acc codomain domain_nodes)
      as [codomain_id codomain_nodes] eqn:Hcodomain.
    destruct (intern_type_dag_node
      (type_dag_arrow domain_id codomain_id) codomain_nodes)
      as [arrow_id arrow_nodes] eqn:Harrow.
    inversion Hbuild; subst root nodes'.
    destruct fuel as [|fuel']; [lia |].
    destruct (@type_to_dag_acc_extends codomain domain_nodes
      codomain_id codomain_nodes Hcodomain)
      as [codomain_suffix Hcodomain_nodes].
    destruct (@intern_type_dag_node_extends
      (type_dag_arrow domain_id codomain_id) codomain_nodes
      arrow_id arrow_nodes Harrow)
      as [arrow_suffix Harrow_nodes].
    assert (Hfinal_codomain :
      arrow_nodes ++ suffix =
      codomain_nodes ++ (arrow_suffix ++ suffix)).
    { subst arrow_nodes. now rewrite app_assoc. }
    assert (Hfinal_domain :
      arrow_nodes ++ suffix =
      domain_nodes ++ (codomain_suffix ++ arrow_suffix ++ suffix)).
    { subst codomain_nodes arrow_nodes. now repeat rewrite app_assoc. }
    assert (Hdomain_decode :
      type_dag_decode_fuel fuel' (arrow_nodes ++ suffix) domain_id =
      Some domain).
    { rewrite Hfinal_domain.
      eapply IHdomain; [exact Hdomain |].
      cbn in Hfuel.
      lia. }
    assert (Hcodomain_decode :
      type_dag_decode_fuel fuel' (arrow_nodes ++ suffix) codomain_id =
      Some codomain).
    { rewrite Hfinal_codomain.
      eapply IHcodomain; [exact Hcodomain |].
      cbn in Hfuel.
      lia. }
    cbn [type_dag_decode_fuel].
    erewrite intern_type_dag_node_at by exact Harrow.
    cbn.
    now rewrite Hdomain_decode, Hcodomain_decode.
Qed.

Theorem type_to_dag_correct : forall source,
  type_dag_decode (type_to_dag source) = Some source.
Proof.
  intro source.
  unfold type_dag_decode, type_to_dag.
  destruct (type_to_dag_acc source []) as [root nodes] eqn:Hbuild.
  change
    (type_dag_decode_fuel (S (type_tree_height source)) nodes root =
      Some source).
  replace nodes with (nodes ++ []) at 1 by now rewrite app_nil_r.
  eapply type_to_dag_acc_correct; [exact Hbuild |].
  lia.
Qed.
