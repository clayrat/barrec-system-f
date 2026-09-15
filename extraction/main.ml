(* Demo of shared examples and the independent weak-head reducer. *)
open Systemf

let rec int_of_nat = function
  | O -> 0
  | S n -> 1 + int_of_nat n

let rec nat_of_int n =
  if n <= 0 then O else S (nat_of_int (n - 1))

let pp_nat n = string_of_int (int_of_nat n)

let rec pp_term = function
  | Var n -> "#" ^ pp_nat n
  | Abs t -> "(lambda. " ^ pp_term t ^ ")"
  | App (f, x) -> "(" ^ pp_term f ^ " " ^ pp_term x ^ ")"

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
      int_of_nat left_variable = int_of_nat right_variable
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

let rec hm_occurs variable = function
  | Var0 found -> int_of_nat variable = int_of_nat found
  | Con _ -> false
  | Arrow (left, right) ->
      hm_occurs variable left || hm_occurs variable right

let rec hm_term_equal left right =
  match left, right with
  | Var_t left, Var_t right
  | Const_t left, Const_t right -> int_of_nat left = int_of_nat right
  | App_t (left_function, left_argument),
    App_t (right_function, right_argument) ->
      hm_term_equal left_function right_function
      && hm_term_equal left_argument right_argument
  | Let_t (left_name, left_bound, left_body),
    Let_t (right_name, right_bound, right_body) ->
      int_of_nat left_name = int_of_nat right_name
      && hm_term_equal left_bound right_bound
      && hm_term_equal left_body right_body
  | Lam_t (left_name, left_body), Lam_t (right_name, right_body) ->
      int_of_nat left_name = int_of_nat right_name
      && hm_term_equal left_body right_body
  | _ -> false

let accept_w_elaboration () =
  if not (constant_freeb hm_let_identity_self_application) then
    failwith "W elaboration fixture escaped the constant-free fragment";
  (match erase_hm_closed hm_let_identity_self_application with
   | Some erased ->
       let expected =
         App (Abs (App (Var O, Var O)), Abs (Var O))
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
       if int_of_nat (w_elab_instantiation_count O tree) <> 2 then
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
              (App (Abs (App (Var O, Var O)), Abs (Var O))))
            then failwith "W-to-RawChurch bridge changed HM erasure";
            (match eval_cap (nat_of_int 2) erased with
             | Some (steps, normal_form) ->
                 if int_of_nat steps <> 2
                    || not (term_equal normal_form (Abs (Var O)))
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
         (Abs (App (Abs (Var (S O)), Abs (Var O)))))
       then failwith "defaulted Church elaboration changed HM erasure";
       print_endline
         "  dead internal type variable: defaulted and checker-accepted"
   | Err _ ->
       failwith "dead internal type variable escaped reification defaulting");
  match runW_elab (Const_t O) [] with
  | Elaboration_rejected (Elab_unsupported_constant O) -> ()
  | _ -> failwith "W elaboration accepted a source constant"

let parse_hm_or_fail source =
  match Parser.parse_hm_program source with
  | Parser.Parsed expression -> expression
  | Parser.Parse_error diagnostic ->
      failwith ("HM frontend: " ^ Parser.diagnostic_to_string source diagnostic)

let check_hm_frontend_contracts () =
  (match Parser.parse_hm_program "true" with
   | Parser.Parsed (Const_t (S O)) -> ()
   | _ -> failwith "HM frontend does not preserve the true marker");
  (match Parser.parse_hm_program "7" with
   | Parser.Parsed (Const_t value) when int_of_nat value = 7 -> ()
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
       (Let_t (S O, Const_t O,
         Let_t (S (S O), Const_t (S O), Var_t (S (S O))))) -> ()
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

let pp_bound prefix depth index =
  let index = int_of_nat index in
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
  | RRFree O -> "ListRel"
  | RRFree n -> "Rel" ^ pp_nat n
  | RRApp (RRFree O, argument) ->
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

let accept_main_w_trace traced =
  let expected_type =
    let result = Var0 (nat_of_int 8) in
    Arrow (Arrow (Con O, Arrow (Con (S O), result)), result)
  in
  (match traced.trace_result with
   | Inferred (inferred_type, _) when eq_ty_dec inferred_type expected_type -> ()
   | _ -> failwith "frontend W trace has an unexpected Church-pair type");
  if int_of_nat (trace_instantiation_count (S O) traced.trace_events) <> 2 then
    failwith "frontend W trace does not instantiate id exactly twice";
  if int_of_nat (trace_generalization_count O traced.trace_events) <> 1
     || int_of_nat (trace_generalization_count (S O) traced.trace_events) <> 1
  then failwith "frontend W trace lost pair/id generalization";
  if int_of_nat (trace_failure_count traced.trace_events) <> 0 then
    failwith "frontend W trace unexpectedly contains a failure"

let accept_rejected_w_trace traced =
  match traced.trace_result with
  | Inference_rejected ->
      if int_of_nat (trace_failure_count traced.trace_events) <> 1 then
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

let () =
  let cap = nat_of_int 10 in
  let main_hm_source =
    "let id = fun x -> x in (id 0, id true)"
  in
  check_hm_frontend_contracts ();
  let frontend_pair_application = parse_hm_or_fail main_hm_source in
  if not (hm_term_equal frontend_pair_application polymorphic_pair_application)
  then failwith "HM frontend expansion differs from the Rocq fixture";
  print_endline "System F: syntax, erasure, and weak-head reduction.";
  List.iteri (print_evaluation cap) erased_examples;
  print_endline "Church checking:";
  List.iteri print_check [raw_term1; raw_term2; raw_term3; raw_term4];
  (match check_core O []
     (RCApp (RCAbs (type1, RCVar O), RCAbs (type1, RCVar O))) with
   | Err (TypeMismatch _) ->
       print_endline "  (lambda x:forall.x) (lambda x:forall.x): rejected, type mismatch"
   | _ -> failwith "checker accepted an ill-typed application");
  print_endline "Hindley-Milner inference:";
  Printf.printf
    "  unify '0 = '0: %s\n"
    (pp_unify_result (unify_exec (Var0 O) (Var0 O)));
  Printf.printf
    "  unify '0 = '0 -> '1: %s\n"
    (pp_unify_result
      (unify_exec (Var0 O) (Arrow (Var0 O, Var0 (S O)))));
  Printf.printf
    "  unify ('0 -> '1) = (c7 -> c8): %s\n"
    (pp_unify_result
      (unify_exec
        (Arrow (Var0 O, Var0 (S O)))
        (Arrow (Con (nat_of_int 7), Con (nat_of_int 8)))));
  let inferred_exec, substitution_exec =
    match runW_exec repeated_application [] with
    | Inferred (inferred, substitution) -> inferred, substitution
    | Inference_rejected ->
        failwith "proof-free W rejected the repeated-application regression"
  in
  ignore substitution_exec;
  begin
      let a = Var0 (S O) in
      let b = Var0 (S (S (S O))) in
      let expected = Arrow (Arrow (a, b), Arrow (a, b)) in
      if not (eq_ty_dec inferred_exec expected) then
        failwith "W returned an unexpected principal type";
      Printf.printf
        "  repeated application: %s\n"
        (pp_hm_ty inferred_exec)
  end;
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
      (Lam_t (O, App_t (Var_t O, Var_t O)))
  in
  accept_rejected_w_trace rejected_trace;
  print_endline "W to System F type bridge:";
  (match infer_systemf_type_exec demo_constant_type repeated_application with
   | Some ty ->
       let expected =
         TForall
           (TForall
             (TArrow
               (TArrow (TVar (S O), TVar O),
                TArrow (TVar (S O), TVar O))))
       in
       if not (type_eq_dec ty expected) then
         failwith "extracted W-to-System-F bridge returned an unexpected type";
       Printf.printf "  repeated application: %s\n" (pp_type ty)
   | None -> failwith "W-to-System-F bridge rejected the W regression");
  print_endline "Free theorem generation:";
  if pp_type church_bool_type <> "Bool" then
    failwith "source Church Bool abbreviation changed unexpectedly";
  if pp_type (church_list_type (TVar O)) <> "[X0]" then
    failwith "source Church list abbreviation changed unexpectedly";
  if pp_formula_type 1 (formula_type_of_type church_bool_type) <> "Bool" then
    failwith "formula Church Bool abbreviation changed unexpectedly";
  if pp_formula_type 1
       (formula_type_of_type (church_list_type (TVar O))) <> "[A0]"
  then failwith "formula Church list abbreviation changed unexpectedly";
  if pp_relation_expr 1 (list_relation (RRBound O)) <> "ListRel R0" then
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
       failwith "main W-to-F input did not reach the relational generator")
