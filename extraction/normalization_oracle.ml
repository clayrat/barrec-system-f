(* Acceptance oracle for the extracted normalization pipeline.

   Exact weak-head evaluation is performed before the selected wrapper, so a
   timed-out strict BBC run still leaves the independently established step
   count in stdout.
   The selected public wrapper must retain precisely that erased term, return
   a bound no smaller than its exact number of steps, and reduce it to the
   independently computed weak-head normal form. *)

open Systemf

let rec pp_term = function
  | Var n -> Printf.sprintf "#%d" n
  | Lam body -> Printf.sprintf "(lambda. %s)" (pp_term body)
  | App (function_, argument) ->
      Printf.sprintf "(%s %s)" (pp_term function_) (pp_term argument)

type fixture =
  | Church of fterm
  | HindleyMilner of hmterm

let fixture depth = function
  | "term1" -> Church raw_term1
  | "term2" -> Church raw_term2
  | "term3" -> Church raw_term3
  | "term4" -> Church raw_term4
  | "w-let-id" -> HindleyMilner hm_let_identity_self_application
  | "w-pair-dup-mono" ->
      HindleyMilner (hm_monomorphic_pair_dup_family depth)
  | "w-pair-dup-poly" ->
      HindleyMilner (hm_polymorphic_pair_dup_family depth)
  | name ->
      Printf.eprintf
        ("unknown case %S; expected term1, term2, term3, term4, "
         ^^ "w-let-id, w-pair-dup-mono, or w-pair-dup-poly\n%!")
        name;
      exit 64

let erased_fixture = function
  | Church raw -> fterm_to_term raw
  | HindleyMilner expression ->
      (match erase_hm_closed expression with
       | Some erased -> erased
       | None ->
           Printf.eprintf "fixture is not a closed constant-free HM term\n%!";
           exit 5)

let normalize_fixture force_bar_recursive = function
  | Church raw ->
      (match normalizeClosed raw with
       | Ok normalization -> normalization
       | Err _ ->
           Printf.eprintf "normalizeClosed rejected the checked fixture\n%!";
           exit 5)
  | HindleyMilner expression ->
      let result =
        if force_bar_recursive then
          runWBarNormalization (fun _ -> type1) expression
        else runWNormalization (fun _ -> type1) expression
      in
      (match result with
       | Ok normalization -> normalization
       | Err _ ->
           Printf.eprintf "W normalization rejected the HM fixture\n%!";
           exit 5)

let case_name = ref ""
let exact_cap = ref 100
let family_depth = ref 3
let force_bar_recursive = ref false

let options =
  [ ( "--case",
      Arg.Set_string case_name,
      ("NAME evaluate term1, term2, term3, term4, w-let-id, "
       ^ "w-pair-dup-mono, or w-pair-dup-poly") );
    ( "--eval-cap",
      Arg.Set_int exact_cap,
      "N cap for exact weak-head evaluation (default: 100)" );
    ( "--depth",
      Arg.Set_int family_depth,
      "N depth of a generated pair-duplication family (default: 3)" );
    ( "--bar-recursive",
      Arg.Set force_bar_recursive,
      "force the strict bar-recursive path for an HM fixture" ) ]

let () =
  Arg.parse options
    (fun argument -> raise (Arg.Bad ("unexpected argument: " ^ argument)))
    "normalization-oracle --case NAME [--depth N] [--eval-cap N]";
  if !case_name = "" then raise (Arg.Bad "--case is required");
  if !exact_cap < 0 then raise (Arg.Bad "--eval-cap must be non-negative");
  if !family_depth < 0 then raise (Arg.Bad "--depth must be non-negative");
  let selected = fixture !family_depth !case_name in
  let erased = erased_fixture selected in
  Printf.printf "case=%s\n" !case_name;
  if !case_name = "w-pair-dup-mono" || !case_name = "w-pair-dup-poly"
  then Printf.printf "depth=%d\n" !family_depth;
  Printf.printf "erased=%s\n" (pp_term erased);
  match eval_cap !exact_cap erased with
  | None ->
      Printf.printf "actual_status=cap_exhausted\n";
      Printf.printf "eval_cap=%d\n%!" !exact_cap;
      exit 3
  | Some (actual_steps, exact_whnf) ->
      Printf.printf "actual_steps=%d\n" actual_steps;
      Printf.printf "whnf=%s\n%!" (pp_term exact_whnf);
      let started = Unix.gettimeofday () in
      let normalization = normalize_fixture !force_bar_recursive selected in
      let elapsed = Unix.gettimeofday () -. started in
      let proposed_bound = normalization.normalization_bound in
      let bound_source =
        match normalization.normalization_bound_source with
        | Exact_evaluation_bound -> "exact"
        | Bar_recursive_bound -> "bar-recursive"
      in
      Printf.printf "bound_source=%s\n" bound_source;
      Printf.printf "bound=%d\n" proposed_bound;
      Printf.printf "normalization_elapsed_seconds=%.6f\n%!" elapsed;
      if not (term_equal erased (normalization_erasure normalization)) then begin
        Printf.eprintf
          "pipeline mismatch: wrapper normalized a different erasure\n%!";
        exit 4
      end;
      if proposed_bound < actual_steps then begin
        Printf.eprintf
          "underestimation: bound=%d is smaller than actual_steps=%d\n%!"
          proposed_bound actual_steps;
        exit 2
      end;
      if not (term_equal exact_whnf normalization.normalization_result) then begin
        Printf.eprintf
          "normal-form mismatch: run_fuel bound disagrees with exact WHNF\n%!";
        exit 4
      end;
      Printf.printf "oracle_status=accepted\n%!"
