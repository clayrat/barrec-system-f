(* Size-oriented driver for the classic Algorithm W pair-duplication family.

   It deliberately avoids printing the inferred type: serializing that tree
   is part of the phenomenon being measured and quickly dominates useful
   output. *)

open Systemf

let variant = ref "poly"
let depth = ref 3

let options =
  [ ( "--variant",
      Arg.Symbol (["mono"; "poly"], fun selected -> variant := selected),
      "mono|poly choose a lambda-bound or let-polymorphic x_0" );
    ( "--depth",
      Arg.Set_int depth,
      "N number of pair-duplication let bindings (default: 3)" ) ]

let () =
  Arg.parse options
    (fun argument -> raise (Arg.Bad ("unexpected argument: " ^ argument)))
    "hm-evil [--variant mono|poly] [--depth N]";
  if !depth < 0 then raise (Arg.Bad "--depth must be non-negative");
  let rocq_depth = !depth in
  let expression =
    match !variant with
    | "mono" -> hm_monomorphic_pair_dup_family rocq_depth
    | "poly" -> hm_polymorphic_pair_dup_family rocq_depth
    | _ -> assert false
  in
  Printf.printf "family=let-x-(n+1)-pair-x-n-x-n\n";
  Printf.printf "variant=%s\n" !variant;
  Printf.printf "depth=%d\n" !depth;
  Printf.printf "source_tree_nodes=%d\n%!"
    (hm_term_tree_size expression);
  let started = Unix.gettimeofday () in
  let result = inferred_type_representation_sizes expression in
  let elapsed = Unix.gettimeofday () -. started in
  match result with
  | Some (tree_size, dag_size) ->
      Printf.printf "inferred_type_tree_nodes=%d\n" tree_size;
      Printf.printf "inferred_type_dag_nodes=%d\n" dag_size;
      Printf.printf "inference_elapsed_seconds=%.6f\n" elapsed;
      Printf.printf "inference_status=inferred\n%!"
  | None ->
      Printf.printf "inference_elapsed_seconds=%.6f\n" elapsed;
      Printf.printf "inference_status=rejected\n%!";
      exit 5
