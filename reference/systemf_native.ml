(* Hand-written native OCaml for the executable part of the System F
   development.

   This is a readable counterpart of [extraction/systemf.ml], not another
   verified artifact.  It keeps the three algorithms used by the lecture in
   one file:

     - Algorithm W for the Curry-style HM fragment;
     - generation of the relational interpretation of a System F type;
     - the memoising [brec] implementation used at Blot's extraction boundary.

   The explicit Church checker and the independent weak-head reducer are
   included because they are the executable oracles connecting those blocks.
   Proof terms, dependent indices, parsers, and the full [isrc]/[adeq]/[bound]
   realiser network deliberately remain in Rocq and generated OCaml.  In
   particular, this file does not pretend that its [brec] implementation proves
   adequacy of that extraction boundary.

   Run it directly with:

       ocaml reference/systemf_native.ml
*)

(* ===== Explicit Church-style System F ===== *)

type ftype =
  | TVar of int
  | TArrow of ftype * ftype
  | TForall of ftype

type fterm =
  | FVar of int
  | FLam of ftype * fterm
  | FApp of fterm * fterm
  | FTLam of fterm
  | FTApp of fterm * ftype

(* Erased, untyped lambda terms: the Curry-style view that [erase] produces
   from a Church-style [fterm].  Type annotations, [FTLam] and [FTApp] all
   disappear, so evaluation below never inspects a type. *)
type eterm =
  | EVar of int
  | ELam of eterm
  | EApp of eterm * eterm

let rec ftype_eq left right =
  match left, right with
  | TVar i, TVar j -> i = j
  | TArrow (a1, b1), TArrow (a2, b2) ->
      ftype_eq a1 a2 && ftype_eq b1 b2
  | TForall body1, TForall body2 -> ftype_eq body1 body2
  | _ -> false

let rec ftype_closed depth = function
  | TVar ix -> ix < depth
  | TArrow (dom, codom) ->
      ftype_closed depth dom && ftype_closed depth codom
  | TForall body -> ftype_closed (depth + 1) body

let checked_ix label ix =
  if ix < 0 then invalid_arg (label ^ ": negative de Bruijn index")
  else ix

let rec ftype_shift amount cutoff = function
  | TVar ix when ix < cutoff -> TVar ix
  | TVar ix -> TVar (checked_ix "ftype_shift" (ix + amount))
  | TArrow (dom, codom) ->
      TArrow
        (ftype_shift amount cutoff dom,
         ftype_shift amount cutoff codom)
  | TForall body -> TForall (ftype_shift amount (cutoff + 1) body)

(* TAPL-style substitution.  [ftype_subst_top arg body] both replaces
   index zero and removes the surrounding universal binder. *)
let rec ftype_subst ix replacement = function
  | TVar var when var = ix ->
      ftype_shift ix 0 replacement
  | TVar var -> TVar var
  | TArrow (dom, codom) ->
      TArrow
        (ftype_subst ix replacement dom,
         ftype_subst ix replacement codom)
  | TForall body -> TForall (ftype_subst (ix + 1) replacement body)

let ftype_subst_top arg body =
  ftype_shift (-1) 0
    (ftype_subst 0 (ftype_shift 1 0 arg) body)

let rec erase = function
  | FVar ix -> EVar ix
  | FLam (_, body) -> ELam (erase body)
  | FApp (function_, arg) -> EApp (erase function_, erase arg)
  | FTLam body -> erase body
  | FTApp (function_, _) -> erase function_

type check_error =
  | Unbound_term_var of int
  | Ill_scoped_ann of ftype
  | Expected_arrow of ftype
  | Arg_ty_mismatch of ftype * ftype
  | Expected_forall of ftype

let rec nth_opt ix = function
  | [] -> None
  | value :: _ when ix = 0 -> Some value
  | _ :: rest when ix > 0 -> nth_opt (ix - 1) rest
  | _ -> None

let rec check_fterm ty_depth ctx = function
  | FVar ix ->
      (match nth_opt ix ctx with
       | Some ty -> Ok ty
       | None -> Error (Unbound_term_var ix))
  | FLam (dom, body) ->
      if not (ftype_closed ty_depth dom) then
        Error (Ill_scoped_ann dom)
      else
        (match check_fterm ty_depth (dom :: ctx) body with
         | Ok codom -> Ok (TArrow (dom, codom))
         | Error error -> Error error)
  | FApp (function_, arg) ->
      (match check_fterm ty_depth ctx function_ with
       | Error error -> Error error
       | Ok (TArrow (dom, codom)) ->
           (match check_fterm ty_depth ctx arg with
            | Error error -> Error error
            | Ok actual when ftype_eq dom actual -> Ok codom
            | Ok actual -> Error (Arg_ty_mismatch (dom, actual)))
       | Ok actual -> Error (Expected_arrow actual))
  | FTLam body ->
      let lifted_ctx = List.map (ftype_shift 1 0) ctx in
      (match check_fterm (ty_depth + 1) lifted_ctx body with
       | Ok body_type -> Ok (TForall body_type)
       | Error error -> Error error)
  | FTApp (function_, arg_type) ->
      if not (ftype_closed ty_depth arg_type) then
        Error (Ill_scoped_ann arg_type)
      else
        (match check_fterm ty_depth ctx function_ with
         | Error error -> Error error
         | Ok (TForall body) -> Ok (ftype_subst_top arg_type body)
         | Ok actual -> Error (Expected_forall actual))

let check_closed term = check_fterm 0 [] term

(* ===== Independent weak-head reducer ===== *)

let rec term_shift amount cutoff = function
  | EVar ix when ix < cutoff -> EVar ix
  | EVar ix -> EVar (checked_ix "term_shift" (ix + amount))
  | ELam body -> ELam (term_shift amount (cutoff + 1) body)
  | EApp (function_, arg) ->
      EApp
        (term_shift amount cutoff function_,
         term_shift amount cutoff arg)

let rec term_subst ix replacement = function
  | EVar var when var = ix -> term_shift ix 0 replacement
  | EVar var -> EVar var
  | ELam body -> ELam (term_subst (ix + 1) replacement body)
  | EApp (function_, arg) ->
      EApp
        (term_subst ix replacement function_,
         term_subst ix replacement arg)

let term_subst_top arg body =
  term_shift (-1) 0
    (term_subst 0 (term_shift 1 0 arg) body)

let rec wh_step = function
  | EApp (ELam body, arg) -> Some (term_subst_top arg body)
  | EApp (function_, arg) ->
      (match wh_step function_ with
       | Some function' -> Some (EApp (function', arg))
       | None -> None)
  | EVar _ | ELam _ -> None

let rec eval_cap fuel term =
  match wh_step term with
  | None -> Some (0, term)
  | Some _ when fuel = 0 -> None
  | Some term' ->
      (match eval_cap (fuel - 1) term' with
       | None -> None
       | Some (steps, normal_form) -> Some (steps + 1, normal_form))

(* ===== Curry-style HM and Algorithm W ===== *)

module IntSet = Set.Make (Int)

type hm_type =
  | HVar of int
  | HCon of int
  | HArrow of hm_type * hm_type

type hm_term =
  | HName of int
  | HConstant of int
  | HLam of int * hm_term
  | HApp of hm_term * hm_term
  | HLet of int * hm_term * hm_term

type scheme = {
  quantified : int list;
  body : hm_type;
}

type subst = (int * hm_type) list
type env = (int * scheme) list

let rec hm_type_eq left right =
  match left, right with
  | HVar i, HVar j | HCon i, HCon j -> i = j
  | HArrow (a1, b1), HArrow (a2, b2) ->
      hm_type_eq a1 a2 && hm_type_eq b1 b2
  | _ -> false

let rec hm_free_vars = function
  | HVar var -> IntSet.singleton var
  | HCon _ -> IntSet.empty
  | HArrow (dom, codom) ->
      IntSet.union (hm_free_vars dom) (hm_free_vars codom)

let scheme_free_vars scheme =
  List.fold_left
    (fun vars quantified -> IntSet.remove quantified vars)
    (hm_free_vars scheme.body)
    scheme.quantified

let env_free_vars env =
  List.fold_left
    (fun vars (_, scheme) ->
       IntSet.union vars (scheme_free_vars scheme))
    IntSet.empty env

let rec apply_subst subst = function
  | HVar var ->
      (match List.assoc_opt var subst with
       | None -> HVar var
       | Some replacement -> apply_subst subst replacement)
  | HCon constant -> HCon constant
  | HArrow (dom, codom) ->
      HArrow
        (apply_subst subst dom,
         apply_subst subst codom)

let apply_scheme subst scheme =
  let filtered =
    List.filter
      (fun (var, _) -> not (List.mem var scheme.quantified))
      subst
  in
  { scheme with body = apply_subst filtered scheme.body }

let apply_env subst env =
  List.map
    (fun (name, scheme) -> name, apply_scheme subst scheme)
    env

(* [compose after before] denotes first applying [before], then [after]. *)
let comp_subst after before =
  let before_dom = List.map fst before in
  let rewritten =
    List.map
      (fun (var, ty) -> var, apply_subst after ty)
      before
  in
  rewritten
  @ List.filter
      (fun (var, _) -> not (List.mem var before_dom))
      after

let monomorphic body = { quantified = []; body }

let lookup_env name env =
  List.assoc_opt name env

type w_event =
  | WFresh of int
  | WInstantiate of int * scheme * hm_type
  | WUnify of hm_type * hm_type * subst option
  | WGeneralize of hm_type * scheme
  | WCompose of subst * subst * subst
  | WFailure of string

type w_state = {
  mutable next_var : int;
  mutable rev_trace : w_event list;
}

exception W_error of string

let record state event =
  state.rev_trace <- event :: state.rev_trace

let fresh_type state =
  let var = state.next_var in
  state.next_var <- var + 1;
  record state (WFresh var);
  HVar var

let compose state after before =
  let result = comp_subst after before in
  record state (WCompose (after, before, result));
  result

let bind_var var ty =
  if hm_type_eq (HVar var) ty then []
  else if IntSet.mem var (hm_free_vars ty) then
    raise (W_error "occurs check")
  else
    [var, ty]

let rec unify left right =
  match left, right with
  | HVar var, ty -> bind_var var ty
  | ty, HVar var -> bind_var var ty
  | HCon fst, HCon snd when fst = snd -> []
  | HArrow (dom1, codom1), HArrow (dom2, codom2) ->
      let fst = unify dom1 dom2 in
      let snd =
        unify
          (apply_subst fst codom1)
          (apply_subst fst codom2)
      in
      comp_subst snd fst
  | _ -> raise (W_error "constructor mismatch")

let unify_traced state left right =
  try
    let subst = unify left right in
    record state (WUnify (left, right, Some subst));
    subst
  with W_error message ->
    record state (WUnify (left, right, None));
    raise (W_error message)

let instantiate state name scheme =
  let replacements =
    List.map
      (fun var -> var, fresh_type state)
      scheme.quantified
  in
  let instance = apply_subst replacements scheme.body in
  record state (WInstantiate (name, scheme, instance));
  instance

let generalize state env ty =
  let quantified =
    IntSet.elements
      (IntSet.diff
         (hm_free_vars ty)
         (env_free_vars env))
  in
  let scheme = { quantified; body = ty } in
  record state (WGeneralize (ty, scheme));
  scheme

let rec infer_w state env = function
  | HName name ->
      (match lookup_env name env with
       | Some scheme -> [], instantiate state name scheme
       | None -> raise (W_error "unbound term variable"))
  | HConstant constant -> [], HCon constant
  | HLam (name, body) ->
      let dom = fresh_type state in
      let subst, codom =
        infer_w state ((name, monomorphic dom) :: env) body
      in
      subst,
      HArrow (apply_subst subst dom, codom)
  | HApp (function_, arg) ->
      let fst, function_type = infer_w state env function_ in
      let snd, arg_type =
        infer_w state (apply_env fst env) arg
      in
      let result_type = fresh_type state in
      let third =
        unify_traced state
          (apply_subst snd function_type)
          (HArrow (arg_type, result_type))
      in
      let fst_two = compose state snd fst in
      compose state third fst_two,
      apply_subst third result_type
  | HLet (name, bound, body) ->
      let fst, bound_type = infer_w state env bound in
      let env' = apply_env fst env in
      let scheme =
        generalize state env'
          (apply_subst fst bound_type)
      in
      let snd, body_type =
        infer_w state ((name, scheme) :: env') body
      in
      compose state snd fst, body_type

type w_result =
  | WInferred of {
      subst : subst;
      inferred_type : hm_type;
      trace : w_event list;
    }
  | WRejected of {
      message : string;
      trace : w_event list;
    }

let run_w term =
  let state = { next_var = 0; rev_trace = [] } in
  try
    let subst, inferred_type = infer_w state [] term in
    WInferred {
      subst;
      inferred_type = apply_subst subst inferred_type;
      trace = List.rev state.rev_trace;
    }
  with W_error message ->
    record state (WFailure message);
    WRejected { message; trace = List.rev state.rev_trace }

(* Top-level generalisation is the type-only bridge used by the relational
   generator.  The verified project additionally retains the W derivation and
   reifies a checked Church term; that dependent audit trail is intentionally
   not duplicated here. *)
let hm_principal_ftype constants ty =
  let rec first_occurrences seen = function
    | HVar var ->
        if List.mem var seen then seen else seen @ [var]
    | HCon _ -> seen
    | HArrow (dom, codom) ->
        first_occurrences (first_occurrences seen dom) codom
  in
  let quantified = first_occurrences [] ty in
  let count = List.length quantified in
  let var_pos = List.mapi (fun pos var -> var, pos) quantified in
  let rec translate = function
    | HVar var ->
        (match List.assoc_opt var var_pos with
         | Some pos -> TVar (count - pos - 1)
         | None -> invalid_arg "hm_principal_ftype: unquantified variable")
    | HCon constant -> constants constant
    | HArrow (dom, codom) ->
        TArrow (translate dom, translate codom)
  in
  List.fold_right (fun _ body -> TForall body) quantified (translate ty)

(* ===== A maximally shared view of HM types ===== *)

type dag_node =
  | DVar of int
  | DConst of int
  | DArrow of int * int

type type_dag = {
  nodes : dag_node array;
  root : int;
}

let dag_of_hm_type ty =
  let nodes = ref [] in
  let rec find_ix wanted ix = function
    | [] -> None
    | node :: _ when node = wanted -> Some ix
    | _ :: rest -> find_ix wanted (ix + 1) rest
  in
  let intern node =
    match find_ix node 0 !nodes with
    | Some ident -> ident
    | None ->
        let ident = List.length !nodes in
        nodes := !nodes @ [node];
        ident
  in
  let rec visit = function
    | HVar var -> intern (DVar var)
    | HCon constant -> intern (DConst constant)
    | HArrow (dom, codom) ->
        let dom_id = visit dom in
        let codom_id = visit codom in
        intern (DArrow (dom_id, codom_id))
  in
  let root = visit ty in
  { nodes = Array.of_list !nodes; root }

let hm_type_of_dag dag =
  let memo = Array.make (Array.length dag.nodes) None in
  let rec decode ident =
    match memo.(ident) with
    | Some ty -> ty
    | None ->
        let ty =
          match dag.nodes.(ident) with
          | DVar var -> HVar var
          | DConst constant -> HCon constant
          | DArrow (dom, codom) ->
              HArrow (decode dom, decode codom)
        in
        memo.(ident) <- Some ty;
        ty
  in
  decode dag.root

let rec hm_tree_size = function
  | HVar _ | HCon _ -> 1
  | HArrow (dom, codom) ->
      1 + hm_tree_size dom + hm_tree_size codom

let rec duplicated_arrow_family depth ty =
  if depth = 0 then ty
  else
    let previous = duplicated_arrow_family (depth - 1) ty in
    HArrow (previous, HArrow (previous, ty))

(* ===== Relational formulas and the free-theorem generator ===== *)

(* The native presentation uses names in the output AST.  The Rocq generator
   uses de Bruijn indices and proves [relate_correct]; naming here merely keeps
   the lecture view readable. *)
type presented_type =
  | PVar of string
  | PArrow of presented_type * presented_type
  | PForall of string * presented_type

type relational_value =
  | VName of string
  | VApply of relational_value * relational_value
  | VTypeApply of relational_value * presented_type

type rel_formula =
  | RTrue
  | RRelated of string * relational_value * relational_value
  | REqual of relational_value * relational_value
  | RAnd of rel_formula * rel_formula
  | RImplies of rel_formula * rel_formula
  | RForallValue of string * presented_type * rel_formula
  | RForallType of string * rel_formula
  | RForallRelation of
      string * presented_type * presented_type * rel_formula

type relation_binding = {
  left_type : string;
  right_type : string;
  relation_name : string;
}

type generator_state = {
  mutable next_type_name : int;
  mutable next_value_name : int;
  mutable next_relation_name : int;
}

let fresh_name counter prefix =
  let ix = !counter in
  counter := ix + 1;
  prefix ^ string_of_int ix

let fresh_presented_type state =
  let counter = ref state.next_type_name in
  let name = fresh_name counter "A" in
  state.next_type_name <- !counter;
  name

let fresh_presented_value state side =
  let counter = ref state.next_value_name in
  let name = fresh_name counter side in
  state.next_value_name <- !counter;
  name

let fresh_presented_relation state =
  let counter = ref state.next_relation_name in
  let name = fresh_name counter "R" in
  state.next_relation_name <- !counter;
  name

let relation_binding_at env ix =
  match nth_opt ix env with
  | Some binding -> binding
  | None ->
      let suffix = string_of_int ix in
      {
        left_type = "freeL" ^ suffix;
        right_type = "freeR" ^ suffix;
        relation_name = "freeR" ^ suffix;
      }

type projection = Left | Right

let rec project_type state side env = function
  | TVar ix ->
      let binding = relation_binding_at env ix in
      PVar (match side with Left -> binding.left_type | Right -> binding.right_type)
  | TArrow (dom, codom) ->
      PArrow
        (project_type state side env dom,
         project_type state side env codom)
  | TForall body ->
      let name = fresh_presented_type state in
      let local =
        { left_type = name; right_type = name; relation_name = "_" }
      in
      PForall (name, project_type state side (local :: env) body)

let rec relate state env ty left right =
  match ty with
  | TVar ix ->
      let binding = relation_binding_at env ix in
      RRelated (binding.relation_name, left, right)
  | TArrow (dom, codom) ->
      let left_name = fresh_presented_value state "x" in
      let right_name = fresh_presented_value state "y" in
      let left_var = VName left_name in
      let right_var = VName right_name in
      RForallValue
        (left_name, project_type state Left env dom,
         RForallValue
           (right_name, project_type state Right env dom,
            RImplies
              (relate state env dom left_var right_var,
               relate state env codom
                 (VApply (left, left_var))
                 (VApply (right, right_var)))))
  | TForall body ->
      let left_name = fresh_presented_type state in
      let right_name = fresh_presented_type state in
      let relation_name = fresh_presented_relation state in
      let left_type = PVar left_name in
      let right_type = PVar right_name in
      let binding = { left_type = left_name; right_type = right_name; relation_name } in
      RForallType
        (left_name,
         RForallType
           (right_name,
            RForallRelation
              (relation_name, left_type, right_type,
               relate state (binding :: env) body
                 (VTypeApply (left, left_type))
                 (VTypeApply (right, right_type)))))

let generate_relation ty =
  let state = {
    next_type_name = 0;
    next_value_name = 0;
    next_relation_name = 0;
  } in
  relate state [] ty (VName "f") (VName "f")

(* Church encodings used by the presentation pass. *)
let church_bool =
  TForall (TArrow (TVar 0, TArrow (TVar 0, TVar 0)))

let church_list element =
  let element_under_binder = ftype_shift 1 0 element in
  TForall
    (TArrow
       (TArrow
          (element_under_binder,
           TArrow (TVar 0, TVar 0)),
        TArrow (TVar 0, TVar 0)))

let rec presented_type_contains var = function
  | PVar name -> name = var
  | PArrow (dom, codom) ->
      presented_type_contains var dom
      || presented_type_contains var codom
  | PForall (name, body) ->
      name <> var && presented_type_contains var body

let bool_body binder = function
  | PArrow (PVar first, PArrow (PVar second, PVar third)) ->
      first = binder && second = binder && third = binder
  | _ -> false

let list_body binder = function
  | PArrow
      (PArrow (element, PArrow (PVar first, PVar second)),
       PArrow (PVar third, PVar fourth))
    when first = binder && second = binder
         && third = binder && fourth = binder
         && not (presented_type_contains binder element) ->
      Some element
  | _ -> None

let rec pp_presented_type = function
  | PForall (binder, body) when bool_body binder body -> "Bool"
  | PForall (binder, body) ->
      (match list_body binder body with
       | Some element -> "[" ^ pp_presented_type element ^ "]"
       | None -> "forall " ^ binder ^ ". " ^ pp_presented_type body)
  | PVar name -> name
  | PArrow (dom, codom) ->
      let dom_text =
        match dom with
        | PArrow _ -> "(" ^ pp_presented_type dom ^ ")"
        | PForall (binder, body)
          when bool_body binder body || Option.is_some (list_body binder body) ->
            pp_presented_type dom
        | PForall _ -> "(" ^ pp_presented_type dom ^ ")"
        | PVar _ -> pp_presented_type dom
      in
      dom_text ^ " -> " ^ pp_presented_type codom

let rec pp_relational_value = function
  | VName name -> name
  | VApply (function_, arg) ->
      "(" ^ pp_relational_value function_ ^ " "
      ^ pp_relational_value arg ^ ")"
  | VTypeApply (function_, arg) ->
      "(" ^ pp_relational_value function_ ^ " ["
      ^ pp_presented_type arg ^ "])"

let rec pp_rel_formula = function
  | RTrue -> "True"
  | RRelated (relation, left, right) ->
      relation ^ " " ^ pp_relational_value left ^ " "
      ^ pp_relational_value right
  | REqual (left, right) ->
      pp_relational_value left ^ " = " ^ pp_relational_value right
  | RAnd (left, right) ->
      "(" ^ pp_rel_formula left ^ " /\\ " ^ pp_rel_formula right ^ ")"
  | RImplies (premise, conclusion) ->
      "(" ^ pp_rel_formula premise ^ " -> "
      ^ pp_rel_formula conclusion ^ ")"
  | RForallValue (name, ty, body) ->
      "forall " ^ name ^ " : " ^ pp_presented_type ty ^ ". "
      ^ pp_rel_formula body
  | RForallType (name, body) ->
      "forall " ^ name ^ " : Type. " ^ pp_rel_formula body
  | RForallRelation (name, left, right, body) ->
      "forall " ^ name ^ " : " ^ pp_presented_type left ^ " -> "
      ^ pp_presented_type right ^ " -> Prop. " ^ pp_rel_formula body

(* ===== The custom bar-recursion extraction boundary ===== *)

type cache_source = State_cache | Local_cache

type brec_event =
  | BQuery of int * eterm
  | BHit of int * cache_source * eterm
  | BMiss of int * eterm
  | BUpdate of int * int * eterm

let rec eterm_eq left right =
  match left, right with
  | EVar i, EVar j -> i = j
  | ELam body1, ELam body2 -> eterm_eq body1 body2
  | EApp (f1, a1), EApp (f2, a2) ->
      eterm_eq f1 f2 && eterm_eq a1 a2
  | _ -> false

let assoc_term key entries =
  let rec search = function
    | [] -> None
    | (candidate, value) :: _ when eterm_eq key candidate ->
        Some value
    | _ :: rest -> search rest
  in
  search entries

(* This is the reviewed demand-driven OCaml implementation supplied for
   [BarRec.Bound.brec].  A recursive call extends the current finite state with
   the candidate answer demanded by [f]; a per-call cache avoids recomputing a
   pure oracle query.  [emit] observes the algorithm but cannot affect it. *)
let memoized_brec ?(emit = fun _ -> ()) f g initial_state =
  let rec run depth state =
    let local_cache = ref [] in
    g (fun key ->
        emit (BQuery (depth, key));
        match assoc_term key !local_cache with
        | Some value ->
            emit (BHit (depth, Local_cache, key));
            value
        | None ->
            let value =
              match state key with
              | Some value ->
                  emit (BHit (depth, State_cache, key));
                  value
              | None ->
                  emit (BMiss (depth, key));
                  let next_candidate = ref 0 in
                  f (fun answer ->
                      let candidate = !next_candidate in
                      next_candidate := candidate + 1;
                      emit (BUpdate (depth + 1, candidate, key));
                      run (depth + 1)
                        (fun query ->
                           if eterm_eq query key then Some answer
                           else state query))
            in
            local_cache := (key, value) :: !local_cache;
            value)
  in
  run 0 initial_state

(* ===== Pretty printers ===== *)

let rec pp_ftype_with names precedence = function
  | TVar ix ->
      (match nth_opt ix names with
       | Some name -> name
       | None -> "#" ^ string_of_int ix)
  | TArrow (dom, codom) ->
      let text =
        pp_ftype_with names 1 dom ^ " -> "
        ^ pp_ftype_with names 0 codom
      in
      if precedence > 0 then "(" ^ text ^ ")" else text
  | TForall body ->
      let name = "X" ^ string_of_int (List.length names) in
      let text = "forall " ^ name ^ ". " ^ pp_ftype_with (name :: names) 0 body in
      if precedence > 0 then "(" ^ text ^ ")" else text

let pp_ftype ty = pp_ftype_with [] 0 ty

let rec pp_eterm = function
  | EVar ix -> "#" ^ string_of_int ix
  | ELam body -> "(lambda. " ^ pp_eterm body ^ ")"
  | EApp (function_, arg) ->
      "(" ^ pp_eterm function_ ^ " " ^ pp_eterm arg ^ ")"

let rec pp_hm_type_with precedence = function
  | HVar var -> "'" ^ string_of_int var
  | HCon constant -> "c" ^ string_of_int constant
  | HArrow (dom, codom) ->
      let text =
        pp_hm_type_with 1 dom ^ " -> " ^ pp_hm_type_with 0 codom
      in
      if precedence > 0 then "(" ^ text ^ ")" else text

let pp_hm_type ty = pp_hm_type_with 0 ty

let pp_subst subst =
  let entries =
    List.map
      (fun (var, ty) ->
         "'" ^ string_of_int var ^ " := " ^ pp_hm_type ty)
      subst
  in
  "[" ^ String.concat "; " entries ^ "]"

let pp_scheme scheme =
  match scheme.quantified with
  | [] -> pp_hm_type scheme.body
  | vars ->
      "forall "
      ^ String.concat " "
          (List.map (fun var -> "'" ^ string_of_int var) vars)
      ^ ". " ^ pp_hm_type scheme.body

let pp_w_event = function
  | WFresh var -> "fresh '" ^ string_of_int var
  | WInstantiate (name, scheme, instance) ->
      "instantiate x" ^ string_of_int name ^ " : " ^ pp_scheme scheme
      ^ " => " ^ pp_hm_type instance
  | WUnify (left, right, Some subst) ->
      "unify " ^ pp_hm_type left ^ " ~ " ^ pp_hm_type right
      ^ " => " ^ pp_subst subst
  | WUnify (left, right, None) ->
      "unify " ^ pp_hm_type left ^ " ~ " ^ pp_hm_type right
      ^ " => failure"
  | WGeneralize (ty, scheme) ->
      "generalize " ^ pp_hm_type ty ^ " => " ^ pp_scheme scheme
  | WCompose (after, before, result) ->
      "compose " ^ pp_subst after ^ " after "
      ^ pp_subst before ^ " => " ^ pp_subst result
  | WFailure message -> "failure: " ^ message

let pp_cache_source = function
  | State_cache -> "state"
  | Local_cache -> "cache"

let pp_brec_event = function
  | BQuery (depth, key) ->
      Printf.sprintf "depth=%d query %s" depth (pp_eterm key)
  | BHit (depth, source, key) ->
      Printf.sprintf "depth=%d hit(%s) %s"
        depth (pp_cache_source source) (pp_eterm key)
  | BMiss (depth, key) ->
      Printf.sprintf "depth=%d miss %s" depth (pp_eterm key)
  | BUpdate (depth, candidate, key) ->
      Printf.sprintf "depth=%d update[%d] %s"
        depth candidate (pp_eterm key)

(* ===== Shared lecture examples and native smoke tests ===== *)

let polymorphic_identity_type =
  TForall (TArrow (TVar 0, TVar 0))

let polymorphic_identity =
  FTLam (FLam (TVar 0, FVar 0))

let explicit_type_application =
  FApp
    (FTApp (polymorphic_identity, polymorphic_identity_type),
     polymorphic_identity)

let term4 =
  FApp
    (FLam (polymorphic_identity_type, FVar 0),
     polymorphic_identity)

let w_let_identity =
  HLet
    (0,
     HLam (1, HName 1),
     HApp (HName 0, HName 0))

let w_occurs_failure =
  HLam (0, HApp (HName 0, HName 0))

let polymorphic_list_endomorphism =
  TForall
    (TArrow
       (church_list (TVar 0),
        church_list (TVar 0)))

let negative_occurrence_example =
  TForall
    (TArrow
       (TArrow (TVar 0, church_bool),
        TArrow (TVar 0, church_bool)))

let presented_closed_type ty =
  let state = {
    next_type_name = 0;
    next_value_name = 0;
    next_relation_name = 0;
  } in
  project_type state Left [] ty

let run_brec_smoke () =
  let events = ref [] in
  let key = EVar 0 in
  let result =
    memoized_brec
      ~emit:(fun event -> events := event :: !events)
      (fun continue -> continue 7)
      (fun oracle -> oracle key)
      (fun _ -> None)
  in
  result, List.rev !events

let run_examples () =
  assert (check_closed polymorphic_identity = Ok polymorphic_identity_type);
  assert (check_closed explicit_type_application = Ok polymorphic_identity_type);
  assert (check_closed term4 = Ok polymorphic_identity_type);
  assert
    (eval_cap 1 (erase term4)
     = Some (1, erase polymorphic_identity));
  assert
    (eval_cap 1 (erase explicit_type_application)
     = Some (1, erase polymorphic_identity));

  let inferred_type, w_trace =
    match run_w w_let_identity with
    | WRejected failure ->
        failwith ("Algorithm W rejected let-id: " ^ failure.message)
    | WInferred success -> success.inferred_type, success.trace
  in
  (match inferred_type with
   | HArrow (HVar left, HVar right) -> assert (left = right)
   | _ -> failwith "let-id did not receive an identity type");
  (match run_w w_occurs_failure with
   | WRejected _ -> ()
   | WInferred _ -> failwith "self-application passed the occurs check");

  let duplicated = duplicated_arrow_family 4 (HVar 0) in
  let dag = dag_of_hm_type duplicated in
  assert (hm_type_eq (hm_type_of_dag dag) duplicated);
  assert (Array.length dag.nodes < hm_tree_size duplicated);

  let identity_formula = generate_relation polymorphic_identity_type in
  let list_formula = generate_relation polymorphic_list_endomorphism in
  let negative_formula = generate_relation negative_occurrence_example in
  let brec_result, brec_trace = run_brec_smoke () in
  assert (brec_result = 7);
  assert (List.exists (function BMiss _ -> true | _ -> false) brec_trace);
  assert
    (List.exists
       (function BHit (_, State_cache, _) -> true | _ -> false)
       brec_trace);

  print_endline "Native System F reference:";
  Printf.printf "\nChurch checker and WH reducer:\n";
  Printf.printf "  polymorphic identity : %s\n" (pp_ftype polymorphic_identity_type);
  Printf.printf "  explicit type application erases and normalizes in 1 WH step\n";
  Printf.printf "  term4 normalizes in 1 WH step\n";

  Printf.printf "\nAlgorithm W:\n";
  Printf.printf "  let id = fun x -> x in id id : %s\n" (pp_hm_type inferred_type);
  List.iteri
    (fun ix event ->
       if ix < 8 then Printf.printf "    %02d  %s\n" (ix + 1) (pp_w_event event))
    w_trace;
  if List.length w_trace > 8 then
    Printf.printf "    ... %d more events\n" (List.length w_trace - 8);
  Printf.printf "  occurs-check example: rejected\n";
  Printf.printf "  duplicated type: tree=%d, DAG=%d\n"
    (hm_tree_size duplicated) (Array.length dag.nodes);

  Printf.printf "\nRelational generator:\n";
  Printf.printf "  type: %s\n"
    (pp_presented_type (presented_closed_type polymorphic_list_endomorphism));
  Printf.printf "  forall a. a -> a:\n    %s\n" (pp_rel_formula identity_formula);
  Printf.printf "  forall a. [a] -> [a]:\n    %s\n" (pp_rel_formula list_formula);
  Printf.printf "  negative occurrence:\n    %s\n" (pp_rel_formula negative_formula);

  Printf.printf "\nMemoised brec boundary:\n";
  List.iter
    (fun event -> Printf.printf "    %s\n" (pp_brec_event event))
    brec_trace;
  Printf.printf "  result: %d\n" brec_result

(* As in [strictness-pcf/reference/pcf_native.ml], loading with [#mod_use]
   has no side effect. *)
let () =
  if Filename.basename Sys.argv.(0) = "systemf_native.ml" then run_examples ()
