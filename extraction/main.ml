(* Demo of shared examples and the independent weak-head reducer. *)
open Systemf

let pp_nat = string_of_int

let rec pp_term = function
  | Var n -> "#" ^ pp_nat n
  | Abs t -> "(lambda. " ^ pp_term t ^ ")"
  | App (f, x) -> "(" ^ pp_term f ^ " " ^ pp_term x ^ ")"

let check_native_nat_contracts () =
  if pred 0 <> 0 || pred 3 <> 2 then
    failwith "native nat extraction changed truncated predecessor";
  if sub 2 5 <> 0 || sub 7 5 <> 2 then
    failwith "native nat extraction changed truncated subtraction";
  if add 20 22 <> 42 || mul 6 7 <> 42 then
    failwith "native nat extraction changed arithmetic"

let print_live_brec_trace () =
  let display_limit = 16 in
  let events = ref 0 in
  let queries = ref 0 in
  let state_hits = ref 0 in
  let cache_hits = ref 0 in
  let misses = ref 0 in
  let updates = ref 0 in
  let maximum_depth = ref 0 in
  let invocations = Hashtbl.create 17 in
  let observe_context context =
    Hashtbl.replace invocations context.Barrec_trace.brec_id ();
    maximum_depth := Stdlib.max !maximum_depth context.Barrec_trace.depth
  in
  let consume event =
    incr events;
    let label, context =
      match event with
      | Barrec_trace.Query context ->
          incr queries;
          "query", context
      | Barrec_trace.Hit (Barrec_trace.State, context) ->
          incr state_hits;
          "hit(state)", context
      | Barrec_trace.Hit (Barrec_trace.Cache, context) ->
          incr cache_hits;
          "hit(cache)", context
      | Barrec_trace.Miss context ->
          incr misses;
          "miss", context
      | Barrec_trace.Update (candidate, context) ->
          incr updates;
          let candidate_name =
            match candidate with
            | Barrec_trace.Exf -> "exf"
            | Barrec_trace.U -> "u"
          in
          "update(" ^ candidate_name ^ ")", context
    in
    observe_context context;
    if !events <= display_limit then
      Printf.printf "  %02d  brec=%d depth=%d %-12s key=%s\n"
        !events context.Barrec_trace.brec_id context.Barrec_trace.depth label
        context.Barrec_trace.key
  in
  print_endline "Live BBC demand trace (term1, first 16 events):";
  let proposed_bound =
    Barrec_trace.with_consumer consume (fun () -> bound type1 term1)
  in
  if proposed_bound <> 1 then
    failwith "live brec trace changed the repaired term1 bound";
  if !queries = 0 || !state_hits = 0 || !cache_hits = 0
     || !misses = 0 || !updates = 0
  then failwith "live brec trace did not expose every demand phase";
  let suppressed = Stdlib.max 0 (!events - display_limit) in
  Printf.printf "  ... %d additional event(s) suppressed\n" suppressed;
  Printf.printf
    ("  summary: brec=%d queries=%d state-hits=%d cache-hits=%d "
     ^^ "misses=%d updates=%d max-depth=%d bound=%d\n")
    (Hashtbl.length invocations) !queries !state_hits !cache_hits !misses
    !updates !maximum_depth proposed_bound

let rec pp_hm_ty = function
  | Var0 n -> "'" ^ pp_nat n
  | Con n -> "c" ^ pp_nat n
  | Arrow (l, r) -> "(" ^ pp_hm_ty l ^ " -> " ^ pp_hm_ty r ^ ")"

let rec pp_hm_scheme = function
  | Sc_var n -> "'" ^ pp_nat n
  | Sc_con n -> "c" ^ pp_nat n
  | Sc_gen n -> "g" ^ pp_nat n
  | Sc_arrow (l, r) ->
      "(" ^ pp_hm_scheme l ^ " -> " ^ pp_hm_scheme r ^ ")"

let rec pp_hm_term = function
  | Var_t name -> "x" ^ pp_nat name
  | Const_t name -> "c" ^ pp_nat name
  | App_t (function_, argument) ->
      "(" ^ pp_hm_term function_ ^ " " ^ pp_hm_term argument ^ ")"
  | Let_t (name, bound, body) ->
      "(let x" ^ pp_nat name ^ " = " ^ pp_hm_term bound
      ^ " in " ^ pp_hm_term body ^ ")"
  | Lam_t (name, body) ->
      "(fun x" ^ pp_nat name ^ " -> " ^ pp_hm_term body ^ ")"

let pp_substitution substitution =
  let binding (variable, ty) =
    "'" ^ pp_nat variable ^ " := " ^ pp_hm_ty ty
  in
  "{" ^ String.concat "; " (List.map binding substitution) ^ "}"

let pp_substitution_domain substitution =
  let variable (name, _) = "'" ^ pp_nat name in
  "[" ^ String.concat ", " (List.map variable substitution) ^ "]"

let rec substitution_equal left right =
  match left, right with
  | [], [] -> true
  | (left_variable, left_type) :: left_rest,
    (right_variable, right_type) :: right_rest ->
      left_variable = right_variable
      && eq_ty_dec left_type right_type
      && substitution_equal left_rest right_rest
  | _ -> false

let w_result_equal left right =
  match left, right with
  | Inference_rejected, Inference_rejected -> true
  | Inferred (left_type, left_substitution),
    Inferred (right_type, right_substitution) ->
      eq_ty_dec left_type right_type
      && substitution_equal left_substitution right_substitution
  | _ -> false

let print_pair_dup_family_sizes () =
  let expected_monomorphic = [(3, 2); (9, 6); (21, 14); (45, 30)] in
  let expected_polymorphic = [(3, 2); (11, 8); (27, 20); (59, 44)] in
  print_endline "Maximally shared monomorphic fixed-result control:";
  List.iter
    (fun depth ->
      let rocq_depth = depth in
      Printf.printf "  n=%d: type tree/DAG=%d/%d nodes\n"
        depth
        (hm_monomorphic_shared_pair_type_tree_size rocq_depth)
        (hm_monomorphic_shared_pair_type_dag_size rocq_depth))
    [0; 1; 2; 3; 4];
  print_endline "Algorithm W bad family (let x_(n+1) = (x_n, x_n)):";
  List.iteri
    (fun depth expected_monomorphic_sizes ->
      let rocq_depth = depth in
      let monomorphic = hm_monomorphic_pair_dup_family rocq_depth in
      let polymorphic = hm_polymorphic_pair_dup_family rocq_depth in
      let observed_sizes expression =
        match inferred_type_representation_sizes expression with
        | Some (tree_size, dag_size) ->
            (tree_size, dag_size)
        | None -> failwith "W rejected a generated pair-duplication term"
      in
      let monomorphic_sizes = observed_sizes monomorphic in
      let polymorphic_sizes = observed_sizes polymorphic in
      let expected_polymorphic_sizes =
        List.nth expected_polymorphic depth
      in
      if monomorphic_sizes <> expected_monomorphic_sizes
         || polymorphic_sizes <> expected_polymorphic_sizes
      then failwith "pair-duplication tree/DAG sizes changed unexpectedly";
      let monomorphic_tree, monomorphic_dag = monomorphic_sizes in
      let polymorphic_tree, polymorphic_dag = polymorphic_sizes in
      Printf.printf
        "  n=%d: source mono/poly=%d/%d; tree mono/poly=%d/%d; DAG mono/poly=%d/%d nodes\n"
        depth
        (hm_term_tree_size monomorphic)
        (hm_term_tree_size polymorphic)
        monomorphic_tree polymorphic_tree
        monomorphic_dag polymorphic_dag)
    expected_monomorphic

let rec hm_occurs variable = function
  | Var0 found -> variable = found
  | Con _ -> false
  | Arrow (left, right) ->
      hm_occurs variable left || hm_occurs variable right

let rec hm_term_equal left right =
  match left, right with
  | Var_t left, Var_t right
  | Const_t left, Const_t right -> left = right
  | App_t (left_function, left_argument),
    App_t (right_function, right_argument) ->
      hm_term_equal left_function right_function
      && hm_term_equal left_argument right_argument
  | Let_t (left_name, left_bound, left_body),
    Let_t (right_name, right_bound, right_body) ->
      left_name = right_name
      && hm_term_equal left_bound right_bound
      && hm_term_equal left_body right_body
  | Lam_t (left_name, left_body), Lam_t (right_name, right_body) ->
      left_name = right_name
      && hm_term_equal left_body right_body
  | _ -> false

let accept_w_elaboration () =
  if not (constant_freeb hm_let_identity_self_application) then
    failwith "W elaboration fixture escaped the constant-free fragment";
  (match erase_hm_closed hm_let_identity_self_application with
   | Some erased ->
       let expected =
         App (Abs (App (Var 0, Var 0)), Abs (Var 0))
       in
       if not (term_equal erased expected) then
         failwith "HM let erasure changed unexpectedly"
   | None -> failwith "closed constant-free HM fixture did not erase");
  (match runW_elab hm_let_identity_self_application [] with
   | Elaborated (ty, substitution, tree) as result ->
       if not
         (w_result_equal
           (erase_w_elab_result result)
           (runW_exec hm_let_identity_self_application []))
       then failwith "W elaboration does not erase to runW_exec";
       if not (hm_term_equal
         (w_elab_tree_source tree) hm_let_identity_self_application)
       then failwith "W elaboration tree does not recover its source";
       if not (eq_ty_dec (w_elab_tree_type tree) ty) then
         failwith "W elaboration tree does not expose its result type";
       if w_elab_instantiation_count 0 tree <> 2 then
         failwith "W elaboration did not retain both id instantiations";
       Printf.printf
         "  let id = fun x -> x in id id: %s, substitution %s\n"
         (pp_hm_ty ty) (pp_substitution substitution)
   | Elaboration_rejected _ ->
       failwith "W elaboration rejected its end-to-end fixture");
  (match runWChurchChecked
      (fun _ -> type1) hm_let_identity_self_application with
   | Ok checked_elaboration ->
       let elaboration = checked_elaboration.checked_church_elaboration in
       (match checked_elaboration.checked_church_certificate with
        | ExistT (ty, intrinsic) ->
            if not (type_eq_dec ty elaboration.raw_church_systemf_type) then
              failwith "reified RawChurch has an unexpected checked type";
            let erased = fterm_to_term [] ty intrinsic in
            if not (term_equal erased
              (checked_church_erasure checked_elaboration))
            then failwith "retained checker certificate changed its erasure";
            if not (term_equal erased
              (erase_raw elaboration.raw_church_term))
            then failwith "checked RawChurch changed its erasure";
            if not (term_equal erased
              (App (Abs (App (Var 0, Var 0)), Abs (Var 0))))
            then failwith "W-to-RawChurch bridge changed HM erasure";
            (match eval_cap 2 erased with
             | Some (steps, normal_form) ->
                 if steps <> 2
                    || not (term_equal normal_form (Abs (Var 0)))
                 then failwith "main W-to-F term has an unexpected WH trace";
                 Printf.printf
                   "  checked erasure: %s\n  weak-head: %s step(s), %s\n"
                   (pp_term erased) (pp_nat steps) (pp_term normal_form)
             | None ->
                 failwith "main W-to-F term exhausted its exact WH cap")
       )
   | Err _ -> failwith "W-to-RawChurch reification failed");
  (match runWChurchChecked
      (fun _ -> type1) hm_dead_internal_type_variable with
   | Ok checked_elaboration ->
       let elaboration = checked_elaboration.checked_church_elaboration in
       if not (type_eq_dec elaboration.raw_church_systemf_type type1) then
         failwith "dead internal type variable changed the principal type";
       if not (term_equal (checked_church_erasure checked_elaboration)
         (Abs (App (Abs (Var 1), Abs (Var 0)))))
       then failwith "defaulted Church elaboration changed HM erasure";
       print_endline
         "  dead internal type variable: defaulted and checker-accepted"
   | Err _ ->
       failwith "dead internal type variable escaped reification defaulting");
  match runW_elab (Const_t 0) [] with
  | Elaboration_rejected (Elab_unsupported_constant 0) -> ()
  | _ -> failwith "W elaboration accepted a source constant"

let parse_hm_or_fail source =
  match Parser.parse_hm_program source with
  | Parser.Parsed expression -> expression
  | Parser.Parse_error diagnostic ->
      failwith ("HM frontend: " ^ Parser.diagnostic_to_string source diagnostic)

let check_hm_frontend_contracts () =
  (match Parser.parse_hm_program "true" with
   | Parser.Parsed (Const_t 1) -> ()
   | _ -> failwith "HM frontend does not preserve the true marker");
  (match Parser.parse_hm_program "7" with
   | Parser.Parsed (Const_t value) when value = 7 -> ()
   | _ -> failwith "HM frontend does not preserve an integer literal");
  (match Parser.parse_hm_program "0 )" with
   | Parser.Parse_error diagnostic when diagnostic.offset = 2 -> ()
   | _ -> failwith "HM frontend accepted trailing input");
  (match Parser.parse_hm_program "missing" with
   | Parser.Parse_error diagnostic when diagnostic.offset = 0 -> ()
   | _ -> failwith "HM frontend accepted an unbound name");
  (match Parser.parse_hm_program
           "let x = 0 in let x = true in x" with
   | Parser.Parsed
       (Let_t (1, Const_t 0,
         Let_t (2, Const_t 1, Var_t 2))) -> ()
   | _ -> failwith "HM frontend resolves shadowed names incorrectly")

let rec pp_type ty =
  match recognize_church_type ty with
  | Some CABool -> "Bool"
  | Some (CAListVariable index) -> "[" ^ pp_type (TVar index) ^ "]"
  | None ->
      match ty with
      | TVar n -> "X" ^ pp_nat n
      | TArrow (l, r) -> "(" ^ pp_type l ^ " -> " ^ pp_type r ^ ")"
      | TForall t -> "(forall. " ^ pp_type t ^ ")"

let rec pp_raw_church = function
  | RCVar index -> "#" ^ pp_nat index
  | RCAbs (ty, body) ->
      "(lambda:" ^ pp_type ty ^ ". " ^ pp_raw_church body ^ ")"
  | RCApp (f, x) ->
      "(" ^ pp_raw_church f ^ " " ^ pp_raw_church x ^ ")"
  | RCTAbs body -> "(Lambda. " ^ pp_raw_church body ^ ")"
  | RCTApp (f, ty) ->
      "(" ^ pp_raw_church f ^ " [" ^ pp_type ty ^ "])"

let rec raw_church_equal left right =
  match left, right with
  | RCVar left_index, RCVar right_index ->
      left_index = right_index
  | RCAbs (left_type, left_body), RCAbs (right_type, right_body) ->
      type_eq_dec left_type right_type
      && raw_church_equal left_body right_body
  | RCApp (left_function, left_argument),
    RCApp (right_function, right_argument) ->
      raw_church_equal left_function right_function
      && raw_church_equal left_argument right_argument
  | RCTAbs left_body, RCTAbs right_body ->
      raw_church_equal left_body right_body
  | RCTApp (left_function, left_type),
    RCTApp (right_function, right_type) ->
      raw_church_equal left_function right_function
      && type_eq_dec left_type right_type
  | _ -> false

let church_identity_source =
  "Lambda X. fun (x : X) -> x"

let church_type_application_source =
  "(Lambda X. fun (x : X) -> x) "
  ^ "[forall X. X -> X] "
  ^ "(Lambda X. fun (x : X) -> x)"

let parse_church_or_fail source =
  match Church_parser.parse_church_program source with
  | Church_parser.Church_parsed raw -> raw
  | Church_parser.Church_parse_error diagnostic ->
      failwith
        ("Church frontend: "
         ^ Church_parser.diagnostic_to_string source diagnostic)

let check_church_frontend_contracts () =
  (match Church_parser.parse_church_program church_identity_source with
   | Church_parser.Church_parsed raw
       when raw_church_equal raw boundary_raw_polymorphic_identity -> ()
   | _ -> failwith "Church frontend changed the polymorphic identity");
  (match Church_parser.parse_church_program
      "Lambda X. fun x : X. x" with
   | Church_parser.Church_parsed raw
       when raw_church_equal raw boundary_raw_polymorphic_identity -> ()
   | _ -> failwith "Church frontend changed the compact lambda binder");
  (match Church_parser.parse_church_program church_type_application_source with
   | Church_parser.Church_parsed raw
       when raw_church_equal raw boundary_raw_type_application -> ()
   | _ -> failwith "Church frontend changed explicit type application");
  (match Church_parser.parse_church_program
      "Lambda X. fun (f : X -> X -> X) -> fun (x : X) -> f x" with
   | Church_parser.Church_parsed
       (RCTAbs
         (RCAbs
           (TArrow (TVar 0, TArrow (TVar 0, TVar 0)),
            RCAbs (TVar 0, RCApp (RCVar 1, RCVar 0))))) -> ()
   | _ -> failwith "Church frontend precedence or indices changed");
  (match Church_parser.parse_church_program
      "Lambda X. Lambda X. fun (x : X) -> x" with
   | Church_parser.Church_parsed
       (RCTAbs (RCTAbs (RCAbs (TVar 0, RCVar 0)))) -> ()
   | _ -> failwith "Church frontend resolves shadowed type names incorrectly");
  (match Church_parser.parse_church_program "Lambda X. missing" with
   | Church_parser.Church_parse_error diagnostic
       when diagnostic.offset = 10 -> ()
   | _ -> failwith "Church frontend accepted an unbound term name");
  (match Church_parser.parse_church_program "fun (x : X) -> x" with
   | Church_parser.Church_parse_error diagnostic
       when diagnostic.offset = 9 -> ()
   | _ -> failwith "Church frontend accepted an unbound type name");
  (match Church_parser.parse_church_program
      "Lambda X. fun (x : X) -> x )" with
   | Church_parser.Church_parse_error _ -> ()
   | _ -> failwith "Church frontend accepted trailing input");
  (match Church_parser.parse_church_program
      "fun (x : forall X. X -> X) -> x x" with
   | Church_parser.Church_parsed raw ->
       begin match check_core 0 [] raw with
       | Err (ExpectedArrow ty)
           when type_eq_dec ty boundary_identity_type -> ()
       | _ -> failwith "Church checker accepted an invalid parsed term"
       end
   | Church_parser.Church_parse_error _ ->
       failwith "Church parser performed type checking")

let pp_bound prefix depth index =
  if index < depth then prefix ^ string_of_int (depth - index - 1)
  else prefix ^ "?" ^ string_of_int index

let rec pp_formula_type depth ty =
  match recognize_formula_church_type ty with
  | Some CABool -> "Bool"
  | Some (CAListVariable index) ->
      "[" ^ pp_formula_type depth (RTVar index) ^ "]"
  | None ->
      match ty with
      | RTVar n -> pp_bound "A" depth n
      | RTArrow (l, r) ->
          "(" ^ pp_formula_type depth l ^ " -> "
          ^ pp_formula_type depth r ^ ")"
      | RTForall body ->
          "(forall A" ^ string_of_int depth ^ ". "
          ^ pp_formula_type (depth + 1) body ^ ")"

let rec pp_value_expr type_depth value_depth = function
  | RVBound n -> pp_bound "x" value_depth n
  | RVFree n -> "f" ^ pp_nat n
  | RVApp (f, x) ->
      "(" ^ pp_value_expr type_depth value_depth f ^ " "
      ^ pp_value_expr type_depth value_depth x ^ ")"
  | RVTypeApp (f, ty) ->
      pp_value_expr type_depth value_depth f
      ^ "[" ^ pp_formula_type type_depth ty ^ "]"

let rec pp_relation_expr relation_depth = function
  | RRBound n -> pp_bound "R" relation_depth n
  | RRFree 0 -> "ListRel"
  | RRFree n -> "Rel" ^ pp_nat n
  | RRApp (RRFree 0, argument) ->
      "ListRel " ^ pp_relation_expr relation_depth argument
  | RRApp (constructor, argument) ->
      "(" ^ pp_relation_expr relation_depth constructor ^ " "
      ^ pp_relation_expr relation_depth argument ^ ")"

let rec pp_rel_formula type_depth relation_depth value_depth = function
  | RFTop -> "true"
  | RFRel (relation, lhs, rhs) ->
      pp_relation_expr relation_depth relation ^ " "
      ^ pp_value_expr type_depth value_depth lhs ^ " "
      ^ pp_value_expr type_depth value_depth rhs
  | RFEqual (lhs, rhs) ->
      pp_value_expr type_depth value_depth lhs ^ " = "
      ^ pp_value_expr type_depth value_depth rhs
  | RFAnd (lhs, rhs) ->
      "(" ^ pp_rel_formula type_depth relation_depth value_depth lhs
      ^ " /\\ "
      ^ pp_rel_formula type_depth relation_depth value_depth rhs ^ ")"
  | RFImplies (premise, conclusion) ->
      "(" ^ pp_rel_formula type_depth relation_depth value_depth premise
      ^ " -> "
      ^ pp_rel_formula type_depth relation_depth value_depth conclusion ^ ")"
  | RFForallValue (ty, body) ->
      "forall x" ^ string_of_int value_depth ^ " : "
      ^ pp_formula_type type_depth ty ^ ". "
      ^ pp_rel_formula type_depth relation_depth (value_depth + 1) body
  | RFForallType body ->
      "forall A" ^ string_of_int type_depth ^ ". "
      ^ pp_rel_formula (type_depth + 1) relation_depth value_depth body
  | RFForallRelation (lhs_ty, rhs_ty, body) ->
      "forall R" ^ string_of_int relation_depth ^ " : "
      ^ "(" ^ pp_formula_type type_depth lhs_ty ^ ") -> "
      ^ "(" ^ pp_formula_type type_depth rhs_ty ^ ") -> Prop. "
      ^ pp_rel_formula type_depth (relation_depth + 1) value_depth body

let pp_generated_formula formula =
  pp_rel_formula 0 0 0 formula

(* Constants are not used by the two bridge examples.  A total, closed
   interpretation is nevertheless part of the public W-to-System-F boundary. *)
let demo_constant_type _ = type1

let pp_type_error = function
  | UnboundTermVariable n -> "unbound term variable #" ^ pp_nat n
  | TypeAnnotationOutOfScope t ->
      "type annotation out of scope: " ^ pp_type t
  | TypeArgumentOutOfScope t ->
      "type argument out of scope: " ^ pp_type t
  | ExpectedArrow t -> "expected an arrow type, found " ^ pp_type t
  | ExpectedForall t -> "expected a forall type, found " ^ pp_type t
  | TypeMismatch (expected, found) ->
      "type mismatch: expected " ^ pp_type expected
      ^ ", found " ^ pp_type found

(* [checkClosed] carries a Prop certificate erased at extraction; the
   observable result is the same as [check_core], see
   [check_core_correspondence]. *)
let print_check i raw =
  match checkClosed raw with
  | Ok (ExistT (ty, t)) ->
      let erased = fterm_to_term [] ty t in
      if not (term_equal erased (erase_raw raw)) then
        failwith "checker result does not erase to the input";
      Printf.printf
        "raw_term%d: %s\n  erasure %s\n" (i + 1) (pp_type ty) (pp_term erased)
  | Err error ->
      Printf.printf "raw_term%d: rejected, %s\n" (i + 1) (pp_type_error error)

let print_curry_church_boundary () =
  let polymorphic_type =
    match boundary_checked_type boundary_raw_polymorphic_identity with
    | Some ty -> ty
    | None -> failwith "boundary polymorphic identity was rejected"
  in
  let annotated_identity_type =
    match boundary_checked_type boundary_raw_identity_at_identity_type with
    | Some ty -> ty
    | None -> failwith "boundary annotated identity was rejected"
  in
  if not (term_equal
      (erase_raw boundary_raw_polymorphic_identity)
      boundary_curry_identity)
     || not (term_equal
       (erase_raw boundary_raw_identity_at_identity_type)
       boundary_curry_identity)
  then failwith "Church identity choices have different Curry erasures";
  if type_eq_dec polymorphic_type annotated_identity_type then
    failwith "Curry/Church boundary lost the different checked types";
  if not (term_equal
      (erase_raw boundary_raw_type_application)
      (erase_raw boundary_raw_annotated_application))
  then failwith "explicit type application survived Curry erasure";
  (match boundary_hm_identity_church_view with
   | Some (ty, raw) ->
       if not (type_eq_dec ty boundary_identity_type)
          || not (raw_church_equal raw boundary_raw_polymorphic_identity)
       then failwith "HM did not restore the rank-1 Church identity"
   | None -> failwith "HM rejected the Curry identity");
  print_endline "Curry/Church boundary:";
  Printf.printf "  Curry erasure: %s\n" (pp_term boundary_curry_identity);
  Printf.printf "  Church choice A: %s : %s\n"
    (pp_raw_church boundary_raw_polymorphic_identity)
    (pp_type polymorphic_type);
  Printf.printf "  Church choice B: %s : %s\n"
    (pp_raw_church boundary_raw_identity_at_identity_type)
    (pp_type annotated_identity_type);
  print_endline "  same Curry term, different checked System F types";
  Printf.printf "  erased type application: %s\n    -> %s\n"
    (pp_raw_church boundary_raw_type_application)
    (pp_term (erase_raw boundary_raw_type_application));
  print_endline
    "  back across: explicit Church annotations, or HM principal rank-1 elaboration";
  Printf.printf "  HM fun x -> x restores: %s\n"
    (pp_raw_church boundary_raw_polymorphic_identity)

let print_church_frontend () =
  check_church_frontend_contracts ();
  let identity = parse_church_or_fail church_identity_source in
  let explicit_application =
    parse_church_or_fail church_type_application_source
  in
  let identity_type =
    match boundary_checked_type identity with
    | Some ty -> ty
    | None -> failwith "parsed Church identity failed checkClosed"
  in
  let application_type =
    match boundary_checked_type explicit_application with
    | Some ty -> ty
    | None -> failwith "parsed Church application failed checkClosed"
  in
  print_endline "Church surface frontend:";
  Printf.printf "  source: %s\n" church_identity_source;
  Printf.printf "  parsed/checkClosed: %s : %s\n"
    (pp_raw_church identity) (pp_type identity_type);
  Printf.printf "  explicit [A] application checks as: %s\n"
    (pp_type application_type);
  print_endline
    "  syntax errors/name resolution belong to the parser; typing remains in checkClosed"

let run_church_source source =
  match Church_parser.parse_church_program source with
  | Church_parser.Church_parse_error diagnostic ->
      Printf.eprintf "Church parse error: %s\n%!"
        (Church_parser.diagnostic_to_string source diagnostic);
      exit 2
  | Church_parser.Church_parsed raw ->
      Printf.printf "source: %s\n" source;
      Printf.printf "RawChurch: %s\n" (pp_raw_church raw);
      Printf.printf "Curry erasure: %s\n" (pp_term (erase_raw raw));
      begin match checkClosed raw with
      | Ok (ExistT (ty, intrinsic)) ->
          let checked_erasure = fterm_to_term [] ty intrinsic in
          if not (term_equal checked_erasure (erase_raw raw)) then
            failwith "parsed checker result changed its erasure";
          Printf.printf "checkClosed: accepted\ntype: %s\n" (pp_type ty)
      | Err error ->
          Printf.printf "checkClosed: rejected\nerror: %s\n%!"
            (pp_type_error error);
          exit 3
      end

let pp_unify_result = function
  | Unified _ -> "success"
  | Rejected -> "rejected"

let pp_trace_unification left right = function
  | Unified substitution -> "success " ^ pp_substitution substitution
  | Rejected ->
      let occurs_failure =
        match left, right with
        | Var0 variable, ty
        | ty, Var0 variable -> hm_occurs variable ty
        | _ -> false
      in
      if occurs_failure then "rejected (occurs check)" else "rejected"

let pp_trace_failure = function
  | Trace_missing_variable variable ->
      "unbound source variable x" ^ pp_nat variable
  | Trace_instantiation_failure (variable, sigma) ->
      "cannot instantiate x" ^ pp_nat variable ^ " : " ^ pp_hm_scheme sigma
  | Trace_unification_failure (left, right) ->
      "cannot unify " ^ pp_hm_ty left ^ " with " ^ pp_hm_ty right

let pp_w_trace_event = function
  | Trace_fresh variable ->
      "fresh '" ^ pp_nat variable
  | Trace_instantiate (variable, state, sigma, instance) ->
      "instantiate x" ^ pp_nat variable ^ " at '" ^ pp_nat state
      ^ " : " ^ pp_hm_scheme sigma ^ " => "
      ^ (match instance with
         | Some ty -> pp_hm_ty ty
         | None -> "rejected")
  | Trace_unify (left, right, result) ->
      "unify " ^ pp_hm_ty left ^ " ~ " ^ pp_hm_ty right
      ^ " => " ^ pp_trace_unification left right result
  | Trace_generalize (variable, ty, sigma) ->
      "generalize x" ^ pp_nat variable ^ " : " ^ pp_hm_ty ty
      ^ " => " ^ pp_hm_scheme sigma
  | Trace_compose (first, second, result) ->
      "compose " ^ pp_substitution_domain first
      ^ " ; " ^ pp_substitution_domain second
      ^ " => " ^ pp_substitution_domain result
  | Trace_fail failure -> "fail: " ^ pp_trace_failure failure

let rec scheme_is_monomorphic = function
  | Sc_gen _ -> false
  | Sc_var _ | Sc_con _ -> true
  | Sc_arrow (domain, codomain) ->
      scheme_is_monomorphic domain && scheme_is_monomorphic codomain

(* Presentation filter only: the full event list is kept for the checks
   below and for the Rocq regressions.  Composing with an empty substitution
   and instantiating a monomorphic scheme carry no information on a slide. *)
let event_is_noise = function
  | Trace_compose ([], _, _) | Trace_compose (_, [], _) -> true
  | Trace_instantiate (_, _, sigma, _) -> scheme_is_monomorphic sigma
  | _ -> false

let print_w_trace label expression =
  let traced = runWTrace expression [] in
  if not (w_result_equal traced.trace_result (runW_exec expression [])) then
    failwith "extracted runWTrace does not erase to runW_exec";
  Printf.printf "  %s\n" label;
  (match traced.trace_result with
   | Inferred (ty, substitution) ->
       Printf.printf "    result: %s, substitution %s\n"
         (pp_hm_ty ty) (pp_substitution substitution)
   | Inference_rejected -> Printf.printf "    result: rejected\n");
  let shown = ref 0 and hidden = ref 0 in
  List.iter
    (fun event ->
      if event_is_noise event then incr hidden
      else begin
        incr shown;
        Printf.printf "    %02d  %s\n" !shown (pp_w_trace_event event)
      end)
    traced.trace_events;
  if !hidden > 0 then
    Printf.printf
      "    (%d identity composition/monomorphic instantiation event(s) hidden)\n"
      !hidden;
  traced

let run_hm_source source =
  match Parser.parse_hm_program source with
  | Parser.Parse_error diagnostic ->
      Printf.eprintf "HM parse error: %s\n%!"
        (Parser.diagnostic_to_string source diagnostic);
      exit 2
  | Parser.Parsed expression ->
      Printf.printf "source: %s\n" source;
      Printf.printf "resolved HM: %s\n" (pp_hm_term expression);
      print_endline "Algorithm W trace:";
      let traced = print_w_trace source expression in
      begin match traced.trace_result with
      | Inference_rejected ->
          Printf.eprintf "Algorithm W: rejected\n%!";
          exit 3
      | Inferred (hm_type, substitution) ->
          let systemf_type = hm_principal_type demo_constant_type hm_type in
          Printf.printf "principal HM type: %s\n" (pp_hm_ty hm_type);
          Printf.printf "substitution: %s\n"
            (pp_substitution substitution);
          if constant_freeb expression then
            Printf.printf "System F principal type: %s\n"
              (pp_type systemf_type)
          else begin
            print_endline
              "constant interpretation: every cN := forall X. X -> X";
            Printf.printf "System F principal type: %s\n"
              (pp_type systemf_type)
          end;
          Printf.printf "free theorem: %s\n"
            (pp_generated_formula (relgen_presented systemf_type));
          if constant_freeb expression then
            match runWChurchChecked demo_constant_type expression with
            | Ok checked ->
                let elaboration = checked.checked_church_elaboration in
                if not (type_eq_dec
                  elaboration.raw_church_systemf_type systemf_type)
                then failwith
                  "interactive HM bridge changed the principal type";
                let erased = checked_church_erasure checked in
                Printf.printf "RawChurch: %s\n"
                  (pp_raw_church elaboration.raw_church_term);
                Printf.printf "Curry erasure: %s\n" (pp_term erased);
                begin match eval_cap 32 erased with
                | Some (steps, normal_form) ->
                    Printf.printf "weak-head: %d step(s), %s\n"
                      steps (pp_term normal_form)
                | None ->
                    print_endline
                      "weak-head: exact cap 32 exhausted (BBC not started)"
                end
            | Err _ ->
                failwith
                  "successful pure HM input failed checked Church elaboration"
          else
            print_endline
              "RawChurch: skipped (source constants have no term interpretation)"
      end

let accept_main_w_trace traced =
  let expected_type =
    let result = Var0 8 in
    Arrow (Arrow (Con 0, Arrow (Con 1, result)), result)
  in
  (match traced.trace_result with
   | Inferred (inferred_type, _) when eq_ty_dec inferred_type expected_type -> ()
   | _ -> failwith "frontend W trace has an unexpected Church-pair type");
  if trace_instantiation_count 1 traced.trace_events <> 2 then
    failwith "frontend W trace does not instantiate id exactly twice";
  if trace_generalization_count 0 traced.trace_events <> 1
     || trace_generalization_count 1 traced.trace_events <> 1
  then failwith "frontend W trace lost pair/id generalization";
  if trace_failure_count traced.trace_events <> 0 then
    failwith "frontend W trace unexpectedly contains a failure"

let accept_rejected_w_trace traced =
  match traced.trace_result with
  | Inference_rejected ->
      if trace_failure_count traced.trace_events <> 1 then
        failwith "rejected W trace has an unexpected failure count"
  | Inferred _ -> failwith "self application unexpectedly passed W"

let print_evaluation cap i term =
  Printf.printf "term%d: %s\n" (i + 1) (pp_term term);
  match eval_cap cap term with
  | None -> Printf.printf "  weak-head: cap %s exhausted\n" (pp_nat cap)
  | Some (steps, normal_form) ->
      let fueled_normal_form = run_fuel steps term in
      if not (term_equal normal_form fueled_normal_form) then
        failwith "eval_cap and run_fuel disagree";
      Printf.printf
        "  weak-head: %s step(s), %s\n"
        (pp_nat steps)
        (pp_term fueled_normal_form)

let run_full_demo () =
  let cap = 10 in
  let main_hm_source =
    "let id = fun x -> x in (id 0, id true)"
  in
  check_native_nat_contracts ();
  check_hm_frontend_contracts ();
  let frontend_pair_application = parse_hm_or_fail main_hm_source in
  if not (hm_term_equal frontend_pair_application polymorphic_pair_application)
  then failwith "HM frontend expansion differs from the Rocq fixture";
  print_endline "System F: syntax, erasure, and weak-head reduction.";
  List.iteri (print_evaluation cap) erased_examples;
  print_endline "Church checking:";
  List.iteri print_check [raw_term1; raw_term2; raw_term3; raw_term4];
  (match check_core 0 []
     (RCApp (RCAbs (type1, RCVar 0), RCAbs (type1, RCVar 0))) with
   | Err (TypeMismatch _) ->
       print_endline "  (lambda x:forall.x) (lambda x:forall.x): rejected, type mismatch"
   | _ -> failwith "checker accepted an ill-typed application");
  print_church_frontend ();
  print_curry_church_boundary ();
  print_endline "Hindley-Milner inference:";
  Printf.printf
    "  unify '0 = '0: %s\n"
    (pp_unify_result (unify_exec (Var0 0) (Var0 0)));
  Printf.printf
    "  unify '0 = '0 -> '1: %s\n"
    (pp_unify_result
      (unify_exec (Var0 0) (Arrow (Var0 0, Var0 1))));
  Printf.printf
    "  unify ('0 -> '1) = (c7 -> c8): %s\n"
    (pp_unify_result
      (unify_exec
        (Arrow (Var0 0, Var0 1))
        (Arrow (Con 7, Con 8))));
  let inferred_exec, substitution_exec =
    match runW_exec repeated_application [] with
    | Inferred (inferred, substitution) -> inferred, substitution
    | Inference_rejected ->
        failwith "proof-free W rejected the repeated-application regression"
  in
  ignore substitution_exec;
  begin
      let a = Var0 1 in
      let b = Var0 3 in
      let expected = Arrow (Arrow (a, b), Arrow (a, b)) in
      if not (eq_ty_dec inferred_exec expected) then
        failwith "W returned an unexpected principal type";
      Printf.printf
        "  repeated application: %s\n"
        (pp_hm_ty inferred_exec)
  end;
  print_pair_dup_family_sizes ();
  print_endline "Main HM to System F pipeline:";
  accept_w_elaboration ();
  print_endline "HM surface frontend:";
  Printf.printf "  source: %s\n" main_hm_source;
  print_endline "  resolved names and expanded pair match the Rocq fixture";
  print_endline "Algorithm W trace:";
  let main_trace =
    print_w_trace
      "let id = fun x -> x in (id 0, id true)"
      frontend_pair_application
  in
  accept_main_w_trace main_trace;
  let rejected_trace =
    print_w_trace
      "lambda x. x x"
      (Lam_t (0, App_t (Var_t 0, Var_t 0)))
  in
  accept_rejected_w_trace rejected_trace;
  print_endline "W to System F type bridge:";
  (match infer_systemf_type_exec demo_constant_type repeated_application with
   | Some ty ->
       let expected =
         TForall
           (TForall
             (TArrow
               (TArrow (TVar 1, TVar 0),
                TArrow (TVar 1, TVar 0))))
       in
       if not (type_eq_dec ty expected) then
         failwith "extracted W-to-System-F bridge returned an unexpected type";
       Printf.printf "  repeated application: %s\n" (pp_type ty)
   | None -> failwith "W-to-System-F bridge rejected the W regression");
  print_endline "Free theorem generation:";
  if pp_type church_bool_type <> "Bool" then
    failwith "source Church Bool abbreviation changed unexpectedly";
  if pp_type (church_list_type (TVar 0)) <> "[X0]" then
    failwith "source Church list abbreviation changed unexpectedly";
  if pp_formula_type 1 (formula_type_of_type church_bool_type) <> "Bool" then
    failwith "formula Church Bool abbreviation changed unexpectedly";
  if pp_formula_type 1
       (formula_type_of_type (church_list_type (TVar 0))) <> "[A0]"
  then failwith "formula Church list abbreviation changed unexpectedly";
  if pp_relation_expr 1 (list_relation (RRBound 0)) <> "ListRel R0" then
    failwith "ListRel abbreviation changed unexpectedly";
  print_endline "  abbreviations: Bool, [A], ListRel R";
  Printf.printf "  type1: %s\n" (pp_generated_formula (relgen type1));
  let list_formula =
    pp_generated_formula
      (relgen_presented polymorphic_list_endomorphism_type)
  in
  let expected_list_formula =
    "forall A0. forall A1. forall R0 : (A0) -> (A1) -> Prop. "
    ^ "forall x0 : [A0]. forall x1 : [A1]. "
    ^ "(ListRel R0 x0 x1 -> "
    ^ "ListRel R0 (f0[A0] x0) (f0[A1] x1))"
  in
  if list_formula <> expected_list_formula then
    failwith "readable list free theorem changed unexpectedly";
  Printf.printf "  forall a. [a] -> [a]: %s\n" list_formula;
  let readable_filter_formula =
    pp_generated_formula (relgen_presented polymorphic_filter_type)
  in
  let expected_filter_formula =
    "forall A0. forall A1. forall R0 : (A0) -> (A1) -> Prop. "
    ^ "forall x0 : (A0 -> Bool). forall x1 : (A1 -> Bool). "
    ^ "(forall x2 : A0. forall x3 : A1. "
    ^ "(R0 x2 x3 -> (x0 x2) = (x1 x3)) -> "
    ^ "forall x2 : [A0]. forall x3 : [A1]. "
    ^ "(ListRel R0 x2 x3 -> "
    ^ "ListRel R0 ((f0[A0] x0) x2) ((f0[A1] x1) x3)))"
  in
  if readable_filter_formula <> expected_filter_formula then
    failwith "readable filter free theorem changed unexpectedly";
  Printf.printf "  filter: %s\n" readable_filter_formula;
  let negative_formula =
    pp_generated_formula (relgen_presented negative_occurrence_type)
  in
  let expected_negative_formula =
    "forall A0. forall A1. forall R0 : (A0) -> (A1) -> Prop. "
    ^ "forall x0 : (A0 -> A0). forall x1 : (A1 -> A1). "
    ^ "(forall x2 : A0. forall x3 : A1. "
    ^ "(R0 x2 x3 -> R0 (x0 x2) (x1 x3)) -> "
    ^ "forall x2 : A0. forall x3 : A1. "
    ^ "(R0 x2 x3 -> "
    ^ "R0 ((f0[A0] x0) x2) ((f0[A1] x1) x3)))"
  in
  if negative_formula <> expected_negative_formula then
    failwith "negative-occurrence free theorem changed unexpectedly";
  Printf.printf "  negative occurrence: %s\n" negative_formula;
  (match infer_relational_formula_exec
           demo_constant_type hm_let_identity_self_application with
   | Some formula ->
       Printf.printf "  W let-id theorem: %s\n"
         (pp_generated_formula formula)
   | None ->
       failwith "main W-to-F input did not reach the relational generator");
  print_live_brec_trace ()

let () =
  match Array.to_list Sys.argv with
  | [_] -> run_full_demo ()
  | [_; "--brec-only"] -> print_live_brec_trace ()
  | [_; "--hm"; source] -> run_hm_source source
  | [_; "--church"; source] -> run_church_source source
  | _ ->
      Printf.eprintf
        "usage: main.exe [--brec-only | --hm 'TERM' | --church 'TERM']\n%!";
      exit 64
