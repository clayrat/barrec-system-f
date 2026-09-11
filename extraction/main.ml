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
  print_endline
    "Inference, Church checking, free theorems, and bound are planned."
