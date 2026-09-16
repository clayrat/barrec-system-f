type context = {
  brec_id : int;
  depth : int;
  key : string;
}

type hit_source = State | Cache
type candidate = Exf | U

type event =
  | Query of context
  | Hit of hit_source * context
  | Miss of context
  | Update of candidate * context

let live_consumer = ref None
let next_brec_id = ref 0
let tsv_event = ref 0

let trace_max_events =
  match Sys.getenv_opt "BLOT_TRACE_MAX_EVENTS" with
  | Some value -> int_of_string_opt value
  | None -> None

let trace_output =
  match Sys.getenv_opt "BLOT_TRACE_FILE" with
  | Some path -> Some (open_out path)
  | None -> None

let emit_tsv phase lookup candidate context =
  let event_number = !tsv_event in
  incr tsv_event;
  match trace_output, trace_max_events with
  | None, _ -> ()
  | Some _, Some maximum when event_number >= maximum -> ()
  | Some output, _ ->
      Printf.fprintf output
        "TRACE\tproject\t%d\t%d\t%s\t%d\t%s\t%s\t%s\n%!"
        context.brec_id event_number phase context.depth lookup candidate
        context.key

(** Preserve the historical nine-column benchmark schema.  A pedagogical
    [Query] is followed by its outcome; TSV records combine those two events
    and spell an [Update] as the older [restart] phase. *)
let emit_file_event = function
  | Query _ -> ()
  | Hit (State, context) -> emit_tsv "query" "hit" "-" context
  | Hit (Cache, context) -> emit_tsv "cache" "hit" "-" context
  | Miss context -> emit_tsv "query" "miss" "-" context
  | Update (candidate, context) ->
      let candidate_name = match candidate with Exf -> "exf" | U -> "u" in
      emit_tsv "restart" "miss" candidate_name context

let enabled () =
  match trace_output, !live_consumer with
  | None, None -> false
  | _ -> true

let fresh_brec_id () =
  if enabled () then begin
    let identifier = !next_brec_id in
    incr next_brec_id;
    identifier
  end else
    -1

let key_var index = Printf.sprintf "#%d" index
let key_lam body = Printf.sprintf "(lambda.%s)" body
let key_app function_ argument = Printf.sprintf "(%s %s)" function_ argument

let emit event =
  emit_file_event event;
  match !live_consumer with
  | Some consumer -> consumer event
  | None -> ()

let context brec_id depth key = { brec_id; depth; key }

let query brec_id depth key =
  emit (Query (context brec_id depth key))

let hit source brec_id depth key =
  emit (Hit (source, context brec_id depth key))

let miss brec_id depth key =
  emit (Miss (context brec_id depth key))

let update candidate brec_id depth key =
  emit (Update (candidate, context brec_id depth key))

let with_consumer consumer action =
  let previous = !live_consumer in
  live_consumer := Some consumer;
  try
    let result = action () in
    live_consumer := previous;
    result
  with exception_raised ->
    live_consumer := previous;
    raise exception_raised
