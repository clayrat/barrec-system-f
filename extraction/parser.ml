(* Small, unverified surface front end for the extracted HM language.

   Grammar (application associates to the left):

     expression  ::= "let" name "=" expression "in" expression
                   | "fun" name "->" expression
                   | application
     application ::= atom atom*
     atom        ::= name | integer | "true"
                   | "(" expression ")"
                   | "(" expression "," expression ")"

   Names are resolved to the numeric identifiers expected by W. Integer
   literals retain their value as [Const_t n]; [true] is the boolean marker
   [Const_t 1]. Pair syntax is expanded through a reserved [pair] binding
   whose value is the shared Rocq Church-pair term. Parsing consumes the
   complete input and all diagnostics retain a byte offset plus line/column. *)

open Systemf

type span = {
  start_offset : int;
  end_offset : int;
}

type diagnostic = {
  offset : int;
  message : string;
}

type parse_result =
  | Parsed of term0
  | Parse_error of diagnostic

exception Frontend_error of diagnostic

let fail_at offset message =
  raise (Frontend_error { offset; message })

type token_kind =
  | Let
  | In
  | Fun
  | True
  | Ident of string
  | Integer of int
  | Equal
  | Arrow_token
  | Left_paren
  | Right_paren
  | Comma
  | End

type token = {
  kind : token_kind;
  span : span;
}

let is_space = function
  | ' ' | '\t' | '\r' | '\n' -> true
  | _ -> false

let is_digit character =
  character >= '0' && character <= '9'

let is_name_start character =
  (character >= 'a' && character <= 'z')
  || (character >= 'A' && character <= 'Z')
  || character = '_'

let is_name_continue character =
  is_name_start character || is_digit character || character = '\''

let keyword_or_name = function
  | "let" -> Let
  | "in" -> In
  | "fun" -> Fun
  | "true" -> True
  | name -> Ident name

let tokenize source =
  let length = String.length source in
  let token kind start_offset end_offset =
    { kind; span = { start_offset; end_offset } }
  in
  let rec scan offset reversed =
    if offset = length then
      Array.of_list
        (List.rev (token End length length :: reversed))
    else
      let character = source.[offset] in
      if is_space character then
        scan (offset + 1) reversed
      else if is_name_start character then
        let stop = ref (offset + 1) in
        while !stop < length && is_name_continue source.[!stop] do
          incr stop
        done;
        let name = String.sub source offset (!stop - offset) in
        scan !stop (token (keyword_or_name name) offset !stop :: reversed)
      else if is_digit character then
        let stop = ref (offset + 1) in
        while !stop < length && is_digit source.[!stop] do
          incr stop
        done;
        let literal = String.sub source offset (!stop - offset) in
        let value =
          try int_of_string literal
          with Failure _ -> fail_at offset "integer literal is too large"
        in
        scan !stop (token (Integer value) offset !stop :: reversed)
      else
        match character with
        | '=' -> scan (offset + 1) (token Equal offset (offset + 1) :: reversed)
        | '(' ->
            scan (offset + 1) (token Left_paren offset (offset + 1) :: reversed)
        | ')' ->
            scan (offset + 1) (token Right_paren offset (offset + 1) :: reversed)
        | ',' -> scan (offset + 1) (token Comma offset (offset + 1) :: reversed)
        | '-' when offset + 1 < length && source.[offset + 1] = '>' ->
            scan (offset + 2) (token Arrow_token offset (offset + 2) :: reversed)
        | _ ->
            fail_at offset
              (Printf.sprintf "unexpected character %C" character)
  in
  scan 0 []

type surface_term =
  | Surface_variable of string * span
  | Surface_constant of int * span
  | Surface_application of surface_term * surface_term * span
  | Surface_lambda of string * surface_term * span
  | Surface_let of string * surface_term * surface_term * span
  | Surface_pair of surface_term * surface_term * span

let surface_span = function
  | Surface_variable (_, span)
  | Surface_constant (_, span)
  | Surface_application (_, _, span)
  | Surface_lambda (_, _, span)
  | Surface_let (_, _, _, span)
  | Surface_pair (_, _, span) -> span

type parser_state = {
  tokens : token array;
  mutable cursor : int;
}

let current state = state.tokens.(state.cursor)

let consume state =
  let token = current state in
  state.cursor <- state.cursor + 1;
  token

let expect_name state description =
  match (current state).kind with
  | Ident name ->
      let token = consume state in
      name, token.span
  | _ -> fail_at (current state).span.start_offset description

let expect_fixed state expected description =
  let token = current state in
  if token.kind = expected then ignore (consume state)
  else fail_at token.span.start_offset description

let begins_atom = function
  | Ident _ | Integer _ | True | Left_paren -> true
  | _ -> false

let rec parse_expression state =
  match (current state).kind with
  | Let -> parse_let state
  | Fun -> parse_lambda state
  | _ -> parse_application state

and parse_let state =
  let start = (consume state).span.start_offset in
  let name, _ = expect_name state "expected a name after 'let'" in
  expect_fixed state Equal "expected '=' after the let-bound name";
  let bound = parse_expression state in
  expect_fixed state In "expected 'in' after the let-bound expression";
  let body = parse_expression state in
  Surface_let
    (name, bound, body,
      { start_offset = start; end_offset = (surface_span body).end_offset })

and parse_lambda state =
  let start = (consume state).span.start_offset in
  let name, _ = expect_name state "expected an argument name after 'fun'" in
  expect_fixed state Arrow_token "expected '->' after the argument name";
  let body = parse_expression state in
  Surface_lambda
    (name, body,
      { start_offset = start; end_offset = (surface_span body).end_offset })

and parse_application state =
  let function_term = parse_atom state in
  let rec arguments accumulated =
    if begins_atom (current state).kind then
      let argument = parse_atom state in
      let span =
        { start_offset = (surface_span accumulated).start_offset;
          end_offset = (surface_span argument).end_offset }
      in
      arguments (Surface_application (accumulated, argument, span))
    else
      accumulated
  in
  arguments function_term

and parse_atom state =
  let token = current state in
  match token.kind with
  | Ident name ->
      ignore (consume state);
      Surface_variable (name, token.span)
  | Integer value ->
      ignore (consume state);
      Surface_constant (value, token.span)
  | True ->
      ignore (consume state);
      Surface_constant (1, token.span)
  | Left_paren ->
      let start = (consume state).span.start_offset in
      let first = parse_expression state in
      begin
        match (current state).kind with
        | Comma ->
            ignore (consume state);
            let second = parse_expression state in
            let closing = current state in
            expect_fixed state Right_paren "expected ')' after the pair";
            Surface_pair
              (first, second,
                { start_offset = start; end_offset = closing.span.end_offset })
        | _ ->
            expect_fixed state Right_paren "expected ')'";
            first
      end
  | _ -> fail_at token.span.start_offset "expected an expression"

let rec nat_of_nonnegative_int value =
  if value <= 0 then O else S (nat_of_nonnegative_int (value - 1))

type resolver_state = {
  mutable next_identifier : int;
  mutable uses_pair : bool;
}

let fresh_identifier state =
  let identifier = state.next_identifier in
  state.next_identifier <- identifier + 1;
  nat_of_nonnegative_int identifier

let rec resolve state environment = function
  | Surface_variable (name, span) ->
      begin
        match List.assoc_opt name environment with
        | Some identifier -> Var_t identifier
        | None -> fail_at span.start_offset ("unbound variable '" ^ name ^ "'")
      end
  | Surface_constant (value, _) ->
      Const_t (nat_of_nonnegative_int value)
  | Surface_application (function_term, argument, _) ->
      let resolved_function = resolve state environment function_term in
      let resolved_argument = resolve state environment argument in
      App_t (resolved_function, resolved_argument)
  | Surface_lambda (name, body, _) ->
      let identifier = fresh_identifier state in
      Lam_t (identifier, resolve state ((name, identifier) :: environment) body)
  | Surface_let (name, bound, body, _) ->
      let identifier = fresh_identifier state in
      let resolved_bound = resolve state environment bound in
      let resolved_body =
        resolve state ((name, identifier) :: environment) body
      in
      Let_t (identifier, resolved_bound, resolved_body)
  | Surface_pair (left, right, _) ->
      state.uses_pair <- true;
      let resolved_left = resolve state environment left in
      let resolved_right = resolve state environment right in
      App_t (App_t (Var_t O, resolved_left), resolved_right)

let parse_hm_program source =
  try
    let state = { tokens = tokenize source; cursor = 0 } in
    let surface = parse_expression state in
    let trailing = current state in
    begin
      match trailing.kind with
      | End -> ()
      | _ -> fail_at trailing.span.start_offset "unexpected trailing input"
    end;
    (* Identifier zero is reserved for the injected Church pair. *)
    let resolver = { next_identifier = 1; uses_pair = false } in
    let body = resolve resolver [] surface in
    if resolver.uses_pair then Parsed (Let_t (O, hm_pair, body))
    else Parsed body
  with Frontend_error diagnostic -> Parse_error diagnostic

let line_and_column source offset =
  let line = ref 1 in
  let column = ref 1 in
  let limit = min offset (String.length source) in
  for index = 0 to limit - 1 do
    if source.[index] = '\n' then begin
      incr line;
      column := 1
    end else
      incr column
  done;
  !line, !column

let diagnostic_to_string source diagnostic =
  let line, column = line_and_column source diagnostic.offset in
  Printf.sprintf "line %d, column %d: %s"
    line column diagnostic.message
