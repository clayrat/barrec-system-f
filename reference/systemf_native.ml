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
  | FVar of int
  | FArrow of ftype * ftype
  | FForall of ftype

type raw_church =
  | CVar of int
  | CAbs of ftype * raw_church
  | CApp of raw_church * raw_church
  | CTAbs of raw_church
  | CTApp of raw_church * ftype

type erased_term =
  | EVar of int
  | EAbs of erased_term
  | EApp of erased_term * erased_term

let rec ftype_equal left right =
  match left, right with
  | FVar i, FVar j -> i = j
  | FArrow (a1, b1), FArrow (a2, b2) ->
      ftype_equal a1 a2 && ftype_equal b1 b2
  | FForall body1, FForall body2 -> ftype_equal body1 body2
  | _ -> false

let rec ftype_closed depth = function
  | FVar index -> index < depth
  | FArrow (domain, codomain) ->
      ftype_closed depth domain && ftype_closed depth codomain
  | FForall body -> ftype_closed (depth + 1) body

let checked_index label index =
  if index < 0 then invalid_arg (label ^ ": negative de Bruijn index")
  else index

let rec ftype_shift amount cutoff = function
  | FVar index when index < cutoff -> FVar index
  | FVar index -> FVar (checked_index "ftype_shift" (index + amount))
  | FArrow (domain, codomain) ->
      FArrow
        (ftype_shift amount cutoff domain,
         ftype_shift amount cutoff codomain)
  | FForall body -> FForall (ftype_shift amount (cutoff + 1) body)

(* TAPL-style substitution.  [ftype_subst_top argument body] both replaces
   index zero and removes the surrounding universal binder. *)
let rec ftype_subst index replacement = function
  | FVar variable when variable = index ->
      ftype_shift index 0 replacement
  | FVar variable -> FVar variable
  | FArrow (domain, codomain) ->
      FArrow
        (ftype_subst index replacement domain,
         ftype_subst index replacement codomain)
  | FForall body -> FForall (ftype_subst (index + 1) replacement body)

let ftype_subst_top argument body =
  ftype_shift (-1) 0
    (ftype_subst 0 (ftype_shift 1 0 argument) body)

let rec erase = function
  | CVar index -> EVar index
  | CAbs (_, body) -> EAbs (erase body)
  | CApp (function_, argument) -> EApp (erase function_, erase argument)
  | CTAbs body -> erase body
  | CTApp (function_, _) -> erase function_

type church_error =
  | Unbound_term_variable of int
  | Ill_scoped_annotation of ftype
  | Expected_arrow of ftype
  | Argument_type_mismatch of ftype * ftype
  | Expected_forall of ftype

let rec nth_opt index = function
  | [] -> None
  | value :: _ when index = 0 -> Some value
  | _ :: rest when index > 0 -> nth_opt (index - 1) rest
  | _ -> None

let rec check_church type_depth context = function
  | CVar index ->
      (match nth_opt index context with
       | Some ty -> Ok ty
       | None -> Error (Unbound_term_variable index))
  | CAbs (domain, body) ->
      if not (ftype_closed type_depth domain) then
        Error (Ill_scoped_annotation domain)
      else
        (match check_church type_depth (domain :: context) body with
         | Ok codomain -> Ok (FArrow (domain, codomain))
         | Error error -> Error error)
  | CApp (function_, argument) ->
      (match check_church type_depth context function_ with
       | Error error -> Error error
       | Ok (FArrow (domain, codomain)) ->
           (match check_church type_depth context argument with
            | Error error -> Error error
            | Ok actual when ftype_equal domain actual -> Ok codomain
            | Ok actual -> Error (Argument_type_mismatch (domain, actual)))
       | Ok actual -> Error (Expected_arrow actual))
  | CTAbs body ->
      let lifted_context = List.map (ftype_shift 1 0) context in
      (match check_church (type_depth + 1) lifted_context body with
       | Ok body_type -> Ok (FForall body_type)
       | Error error -> Error error)
  | CTApp (function_, argument_type) ->
      if not (ftype_closed type_depth argument_type) then
        Error (Ill_scoped_annotation argument_type)
      else
        (match check_church type_depth context function_ with
         | Error error -> Error error
         | Ok (FForall body) -> Ok (ftype_subst_top argument_type body)
         | Ok actual -> Error (Expected_forall actual))

let check_closed term = check_church 0 [] term

(* ===== Independent weak-head reducer ===== *)

let rec term_shift amount cutoff = function
  | EVar index when index < cutoff -> EVar index
  | EVar index -> EVar (checked_index "term_shift" (index + amount))
  | EAbs body -> EAbs (term_shift amount (cutoff + 1) body)
  | EApp (function_, argument) ->
      EApp
        (term_shift amount cutoff function_,
         term_shift amount cutoff argument)

let rec term_subst index replacement = function
  | EVar variable when variable = index -> term_shift index 0 replacement
  | EVar variable -> EVar variable
  | EAbs body -> EAbs (term_subst (index + 1) replacement body)
  | EApp (function_, argument) ->
      EApp
        (term_subst index replacement function_,
         term_subst index replacement argument)

let term_subst_top argument body =
  term_shift (-1) 0
    (term_subst 0 (term_shift 1 0 argument) body)

let rec wh_step = function
  | EApp (EAbs body, argument) -> Some (term_subst_top argument body)
  | EApp (function_, argument) ->
      (match wh_step function_ with
       | Some function' -> Some (EApp (function', argument))
       | None -> None)
  | EVar _ | EAbs _ -> None

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

type substitution = (int * hm_type) list
type environment = (int * scheme) list

let rec hm_type_equal left right =
  match left, right with
  | HVar i, HVar j | HCon i, HCon j -> i = j
  | HArrow (a1, b1), HArrow (a2, b2) ->
      hm_type_equal a1 a2 && hm_type_equal b1 b2
  | _ -> false

let rec hm_free_variables = function
  | HVar variable -> IntSet.singleton variable
  | HCon _ -> IntSet.empty
  | HArrow (domain, codomain) ->
      IntSet.union (hm_free_variables domain) (hm_free_variables codomain)

let scheme_free_variables scheme =
  List.fold_left
    (fun variables quantified -> IntSet.remove quantified variables)
    (hm_free_variables scheme.body)
    scheme.quantified

let environment_free_variables environment =
  List.fold_left
    (fun variables (_, scheme) ->
       IntSet.union variables (scheme_free_variables scheme))
    IntSet.empty environment

let rec apply_substitution substitution = function
  | HVar variable ->
      (match List.assoc_opt variable substitution with
       | None -> HVar variable
       | Some replacement -> apply_substitution substitution replacement)
  | HCon constant -> HCon constant
  | HArrow (domain, codomain) ->
      HArrow
        (apply_substitution substitution domain,
         apply_substitution substitution codomain)

let apply_scheme substitution scheme =
  let filtered =
    List.filter
      (fun (variable, _) -> not (List.mem variable scheme.quantified))
      substitution
  in
  { scheme with body = apply_substitution filtered scheme.body }

let apply_environment substitution environment =
  List.map
    (fun (name, scheme) -> name, apply_scheme substitution scheme)
    environment

(* [compose after before] denotes first applying [before], then [after]. *)
let compose_substitution after before =
  let before_domain = List.map fst before in
  let rewritten =
    List.map
      (fun (variable, ty) -> variable, apply_substitution after ty)
      before
  in
  rewritten
  @ List.filter
      (fun (variable, _) -> not (List.mem variable before_domain))
      after

let monomorphic body = { quantified = []; body }

let lookup_environment name environment =
  List.assoc_opt name environment

type w_event =
  | WFresh of int
  | WInstantiate of int * scheme * hm_type
  | WUnify of hm_type * hm_type * substitution option
  | WGeneralize of hm_type * scheme
  | WCompose of substitution * substitution * substitution
  | WFailure of string

type w_state = {
  mutable next_variable : int;
  mutable reversed_trace : w_event list;
}

exception W_error of string

let record state event =
  state.reversed_trace <- event :: state.reversed_trace

let fresh_type state =
  let variable = state.next_variable in
  state.next_variable <- variable + 1;
  record state (WFresh variable);
  HVar variable

let compose state after before =
  let result = compose_substitution after before in
  record state (WCompose (after, before, result));
  result

let bind_variable variable ty =
  if hm_type_equal (HVar variable) ty then []
  else if IntSet.mem variable (hm_free_variables ty) then
    raise (W_error "occurs check")
  else
    [variable, ty]

let rec unify_untraced left right =
  match left, right with
  | HVar variable, ty -> bind_variable variable ty
  | ty, HVar variable -> bind_variable variable ty
  | HCon first, HCon second when first = second -> []
  | HArrow (domain1, codomain1), HArrow (domain2, codomain2) ->
      let first = unify_untraced domain1 domain2 in
      let second =
        unify_untraced
          (apply_substitution first codomain1)
          (apply_substitution first codomain2)
      in
      compose_substitution second first
  | _ -> raise (W_error "constructor mismatch")

let unify state left right =
  try
    let substitution = unify_untraced left right in
    record state (WUnify (left, right, Some substitution));
    substitution
  with W_error message ->
    record state (WUnify (left, right, None));
    raise (W_error message)

let instantiate state name scheme =
  let replacements =
    List.map
      (fun variable -> variable, fresh_type state)
      scheme.quantified
  in
  let instance = apply_substitution replacements scheme.body in
  record state (WInstantiate (name, scheme, instance));
  instance

let generalize state environment ty =
  let quantified =
    IntSet.elements
      (IntSet.diff
         (hm_free_variables ty)
         (environment_free_variables environment))
  in
  let scheme = { quantified; body = ty } in
  record state (WGeneralize (ty, scheme));
  scheme

let rec infer_w state environment = function
  | HName name ->
      (match lookup_environment name environment with
       | Some scheme -> [], instantiate state name scheme
       | None -> raise (W_error "unbound term variable"))
  | HConstant constant -> [], HCon constant
  | HLam (name, body) ->
      let domain = fresh_type state in
      let substitution, codomain =
        infer_w state ((name, monomorphic domain) :: environment) body
      in
      substitution,
      HArrow (apply_substitution substitution domain, codomain)
  | HApp (function_, argument) ->
      let first, function_type = infer_w state environment function_ in
      let second, argument_type =
        infer_w state (apply_environment first environment) argument
      in
      let result_type = fresh_type state in
      let third =
        unify state
          (apply_substitution second function_type)
          (HArrow (argument_type, result_type))
      in
      let first_two = compose state second first in
      compose state third first_two,
      apply_substitution third result_type
  | HLet (name, bound, body) ->
      let first, bound_type = infer_w state environment bound in
      let environment' = apply_environment first environment in
      let scheme =
        generalize state environment'
          (apply_substitution first bound_type)
      in
      let second, body_type =
        infer_w state ((name, scheme) :: environment') body
      in
      compose state second first, body_type

type w_result =
  | WInferred of {
      substitution : substitution;
      inferred_type : hm_type;
      trace : w_event list;
    }
  | WRejected of {
      message : string;
      trace : w_event list;
    }

let run_w term =
  let state = { next_variable = 0; reversed_trace = [] } in
  try
    let substitution, inferred_type = infer_w state [] term in
    WInferred {
      substitution;
      inferred_type = apply_substitution substitution inferred_type;
      trace = List.rev state.reversed_trace;
    }
  with W_error message ->
    record state (WFailure message);
    WRejected { message; trace = List.rev state.reversed_trace }

(* Top-level generalisation is the type-only bridge used by the relational
   generator.  The verified project additionally retains the W derivation and
   reifies a checked Church term; that dependent audit trail is intentionally
   not duplicated here. *)
let hm_principal_ftype constants ty =
  let rec first_occurrences seen = function
    | HVar variable ->
        if List.mem variable seen then seen else seen @ [variable]
    | HCon _ -> seen
    | HArrow (domain, codomain) ->
        first_occurrences (first_occurrences seen domain) codomain
  in
  let quantified = first_occurrences [] ty in
  let count = List.length quantified in
  let positions = List.mapi (fun position variable -> variable, position) quantified in
  let rec translate = function
    | HVar variable ->
        (match List.assoc_opt variable positions with
         | Some position -> FVar (count - position - 1)
         | None -> invalid_arg "hm_principal_ftype: unquantified variable")
    | HCon constant -> constants constant
    | HArrow (domain, codomain) ->
        FArrow (translate domain, translate codomain)
  in
  List.fold_right (fun _ body -> FForall body) quantified (translate ty)

(* ===== A maximally shared view of HM types ===== *)

type dag_node =
  | DVariable of int
  | DConstant of int
  | DArrow of int * int

type type_dag = {
  nodes : dag_node array;
  root : int;
}

let dag_of_hm_type ty =
  let nodes = ref [] in
  let rec find_index wanted index = function
    | [] -> None
    | node :: _ when node = wanted -> Some index
    | _ :: rest -> find_index wanted (index + 1) rest
  in
  let intern node =
    match find_index node 0 !nodes with
    | Some identifier -> identifier
    | None ->
        let identifier = List.length !nodes in
        nodes := !nodes @ [node];
        identifier
  in
  let rec visit = function
    | HVar variable -> intern (DVariable variable)
    | HCon constant -> intern (DConstant constant)
    | HArrow (domain, codomain) ->
        let domain_id = visit domain in
        let codomain_id = visit codomain in
        intern (DArrow (domain_id, codomain_id))
  in
  let root = visit ty in
  { nodes = Array.of_list !nodes; root }

let hm_type_of_dag dag =
  let memo = Array.make (Array.length dag.nodes) None in
  let rec decode identifier =
    match memo.(identifier) with
    | Some ty -> ty
    | None ->
        let ty =
          match dag.nodes.(identifier) with
          | DVariable variable -> HVar variable
          | DConstant constant -> HCon constant
          | DArrow (domain, codomain) ->
              HArrow (decode domain, decode codomain)
        in
        memo.(identifier) <- Some ty;
        ty
  in
  decode dag.root

let rec hm_tree_size = function
  | HVar _ | HCon _ -> 1
  | HArrow (domain, codomain) ->
      1 + hm_tree_size domain + hm_tree_size codomain

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
  let index = !counter in
  counter := index + 1;
  prefix ^ string_of_int index

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

let relation_binding_at environment index =
  match nth_opt index environment with
  | Some binding -> binding
  | None ->
      let suffix = string_of_int index in
      {
        left_type = "freeL" ^ suffix;
        right_type = "freeR" ^ suffix;
        relation_name = "freeR" ^ suffix;
      }

type projection = Left | Right

let rec project_type state side environment = function
  | FVar index ->
      let binding = relation_binding_at environment index in
      PVar (match side with Left -> binding.left_type | Right -> binding.right_type)
  | FArrow (domain, codomain) ->
      PArrow
        (project_type state side environment domain,
         project_type state side environment codomain)
  | FForall body ->
      let name = fresh_presented_type state in
      let local =
        { left_type = name; right_type = name; relation_name = "_" }
      in
      PForall (name, project_type state side (local :: environment) body)

let rec relate state environment ty left right =
  match ty with
  | FVar index ->
      let binding = relation_binding_at environment index in
      RRelated (binding.relation_name, left, right)
  | FArrow (domain, codomain) ->
      let left_name = fresh_presented_value state "x" in
      let right_name = fresh_presented_value state "y" in
      let left_variable = VName left_name in
      let right_variable = VName right_name in
      RForallValue
        (left_name, project_type state Left environment domain,
         RForallValue
           (right_name, project_type state Right environment domain,
            RImplies
              (relate state environment domain left_variable right_variable,
               relate state environment codomain
                 (VApply (left, left_variable))
                 (VApply (right, right_variable)))))
  | FForall body ->
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
               relate state (binding :: environment) body
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
  FForall (FArrow (FVar 0, FArrow (FVar 0, FVar 0)))

let church_list element =
  let element_under_binder = ftype_shift 1 0 element in
  FForall
    (FArrow
       (FArrow
          (element_under_binder,
           FArrow (FVar 0, FVar 0)),
        FArrow (FVar 0, FVar 0)))

let rec presented_type_contains variable = function
  | PVar name -> name = variable
  | PArrow (domain, codomain) ->
      presented_type_contains variable domain
      || presented_type_contains variable codomain
  | PForall (name, body) ->
      name <> variable && presented_type_contains variable body

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
  | PArrow (domain, codomain) ->
      let domain_text =
        match domain with
        | PArrow _ -> "(" ^ pp_presented_type domain ^ ")"
        | PForall (binder, body)
          when bool_body binder body || Option.is_some (list_body binder body) ->
            pp_presented_type domain
        | PForall _ -> "(" ^ pp_presented_type domain ^ ")"
        | PVar _ -> pp_presented_type domain
      in
      domain_text ^ " -> " ^ pp_presented_type codomain

let rec pp_relational_value = function
  | VName name -> name
  | VApply (function_, argument) ->
      "(" ^ pp_relational_value function_ ^ " "
      ^ pp_relational_value argument ^ ")"
  | VTypeApply (function_, argument) ->
      "(" ^ pp_relational_value function_ ^ " ["
      ^ pp_presented_type argument ^ "])"

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
  | BQuery of int * erased_term
  | BHit of int * cache_source * erased_term
  | BMiss of int * erased_term
  | BUpdate of int * int * erased_term

let rec erased_term_equal left right =
  match left, right with
  | EVar i, EVar j -> i = j
  | EAbs body1, EAbs body2 -> erased_term_equal body1 body2
  | EApp (f1, a1), EApp (f2, a2) ->
      erased_term_equal f1 f2 && erased_term_equal a1 a2
  | _ -> false

let assoc_term key entries =
  let rec search = function
    | [] -> None
    | (candidate, value) :: _ when erased_term_equal key candidate ->
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
                           if erased_term_equal query key then Some answer
                           else state query))
            in
            local_cache := (key, value) :: !local_cache;
            value)
  in
  run 0 initial_state

(* ===== Pretty printers ===== *)

let rec pp_ftype_with names precedence = function
  | FVar index ->
      (match nth_opt index names with
       | Some name -> name
       | None -> "#" ^ string_of_int index)
  | FArrow (domain, codomain) ->
      let text =
        pp_ftype_with names 1 domain ^ " -> "
        ^ pp_ftype_with names 0 codomain
      in
      if precedence > 0 then "(" ^ text ^ ")" else text
  | FForall body ->
      let name = "X" ^ string_of_int (List.length names) in
      let text = "forall " ^ name ^ ". " ^ pp_ftype_with (name :: names) 0 body in
      if precedence > 0 then "(" ^ text ^ ")" else text

let pp_ftype ty = pp_ftype_with [] 0 ty

let rec pp_erased_term = function
  | EVar index -> "#" ^ string_of_int index
  | EAbs body -> "(lambda. " ^ pp_erased_term body ^ ")"
  | EApp (function_, argument) ->
      "(" ^ pp_erased_term function_ ^ " " ^ pp_erased_term argument ^ ")"

let rec pp_hm_type_with precedence = function
  | HVar variable -> "'" ^ string_of_int variable
  | HCon constant -> "c" ^ string_of_int constant
  | HArrow (domain, codomain) ->
      let text =
        pp_hm_type_with 1 domain ^ " -> " ^ pp_hm_type_with 0 codomain
      in
      if precedence > 0 then "(" ^ text ^ ")" else text

let pp_hm_type ty = pp_hm_type_with 0 ty

let pp_substitution substitution =
  let entries =
    List.map
      (fun (variable, ty) ->
         "'" ^ string_of_int variable ^ " := " ^ pp_hm_type ty)
      substitution
  in
  "[" ^ String.concat "; " entries ^ "]"

let pp_scheme scheme =
  match scheme.quantified with
  | [] -> pp_hm_type scheme.body
  | variables ->
      "forall "
      ^ String.concat " "
          (List.map (fun variable -> "'" ^ string_of_int variable) variables)
      ^ ". " ^ pp_hm_type scheme.body

let pp_w_event = function
  | WFresh variable -> "fresh '" ^ string_of_int variable
  | WInstantiate (name, scheme, instance) ->
      "instantiate x" ^ string_of_int name ^ " : " ^ pp_scheme scheme
      ^ " => " ^ pp_hm_type instance
  | WUnify (left, right, Some substitution) ->
      "unify " ^ pp_hm_type left ^ " ~ " ^ pp_hm_type right
      ^ " => " ^ pp_substitution substitution
  | WUnify (left, right, None) ->
      "unify " ^ pp_hm_type left ^ " ~ " ^ pp_hm_type right
      ^ " => failure"
  | WGeneralize (ty, scheme) ->
      "generalize " ^ pp_hm_type ty ^ " => " ^ pp_scheme scheme
  | WCompose (after, before, result) ->
      "compose " ^ pp_substitution after ^ " after "
      ^ pp_substitution before ^ " => " ^ pp_substitution result
  | WFailure message -> "failure: " ^ message

let pp_cache_source = function
  | State_cache -> "state"
  | Local_cache -> "cache"

let pp_brec_event = function
  | BQuery (depth, key) ->
      Printf.sprintf "depth=%d query %s" depth (pp_erased_term key)
  | BHit (depth, source, key) ->
      Printf.sprintf "depth=%d hit(%s) %s"
        depth (pp_cache_source source) (pp_erased_term key)
  | BMiss (depth, key) ->
      Printf.sprintf "depth=%d miss %s" depth (pp_erased_term key)
  | BUpdate (depth, candidate, key) ->
      Printf.sprintf "depth=%d update[%d] %s"
        depth candidate (pp_erased_term key)

(* ===== Shared lecture examples and native smoke tests ===== *)

let polymorphic_identity_type =
  FForall (FArrow (FVar 0, FVar 0))

let polymorphic_identity =
  CTAbs (CAbs (FVar 0, CVar 0))

let explicit_type_application =
  CApp
    (CTApp (polymorphic_identity, polymorphic_identity_type),
     polymorphic_identity)

let term4 =
  CApp
    (CAbs (polymorphic_identity_type, CVar 0),
     polymorphic_identity)

let w_let_identity =
  HLet
    (0,
     HLam (1, HName 1),
     HApp (HName 0, HName 0))

let w_occurs_failure =
  HLam (0, HApp (HName 0, HName 0))

let polymorphic_list_endomorphism =
  FForall
    (FArrow
       (church_list (FVar 0),
        church_list (FVar 0)))

let negative_occurrence_example =
  FForall
    (FArrow
       (FArrow (FVar 0, church_bool),
        FArrow (FVar 0, church_bool)))

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
  assert (hm_type_equal (hm_type_of_dag dag) duplicated);
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
    (fun index event ->
       if index < 8 then Printf.printf "    %02d  %s\n" (index + 1) (pp_w_event event))
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
