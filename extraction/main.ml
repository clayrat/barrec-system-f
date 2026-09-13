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

let pp_unify_result = function
  | Unified _ -> "success"
  | Rejected -> "rejected"

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
  print_endline "System F: syntax, erasure, and weak-head reduction.";
  List.iteri (print_evaluation cap) erased_examples;
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
  print_endline "Church checking and free theorems are planned."
