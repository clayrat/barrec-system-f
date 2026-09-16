(** Optional observations emitted by the hand-written extraction of [brec].
    With no consumer and no [BLOT_TRACE_FILE], the runtime remains silent. *)

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

val enabled : unit -> bool
val fresh_brec_id : unit -> int
val key_var : int -> string
val key_lam : string -> string
val key_app : string -> string -> string
val query : int -> int -> string -> unit
val hit : hit_source -> int -> int -> string -> unit
val miss : int -> int -> string -> unit
val update : candidate -> int -> int -> string -> unit
val with_consumer : (event -> unit) -> (unit -> 'a) -> 'a
