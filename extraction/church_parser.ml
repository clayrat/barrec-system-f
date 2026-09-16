(* Textual front end for the full explicit (Church-style) System F syntax.

   Grammar. Term and type application associate to the left; type arrows
   associate to the right.

     term        ::= "fun" "(" name ":" type ")" "->" term
                   | "fun" name ":" type "." term
                   | "Lambda" name "." term
                   | elimination
     elimination ::= atom (atom | "[" type "]")*
     atom        ::= name | "(" term ")"
     type        ::= "forall" name "." type | arrow-type
     arrow-type  ::= type-atom ("->" type)?
     type-atom   ::= name | "(" type ")"

   The parser resolves both namespaces to de Bruijn indices and consumes the
   complete input. It deliberately performs no typing: a well-formed parsed
   [fterm] still goes through the verified [checkClosed] boundary. *)

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
  | Church_parsed of fterm
  | Church_parse_error of diagnostic

exception Frontend_error of diagnostic

let fail_at offset message =
  raise (Frontend_error { offset; message })

type token_kind =
  | Fun
  | Type_lambda
  | Forall
  | Ident of string
  | Colon
  | Dot
  | Arrow_token
  | Left_paren
  | Right_paren
  | Left_bracket
  | Right_bracket
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
  | "fun" -> Fun
  | "Lambda" | "lambda" -> Type_lambda
  | "forall" -> Forall
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
      else
        match character with
        | ':' -> scan (offset + 1) (token Colon offset (offset + 1) :: reversed)
        | '.' -> scan (offset + 1) (token Dot offset (offset + 1) :: reversed)
        | '(' ->
            scan (offset + 1) (token Left_paren offset (offset + 1) :: reversed)
        | ')' ->
            scan (offset + 1) (token Right_paren offset (offset + 1) :: reversed)
        | '[' ->
            scan (offset + 1) (token Left_bracket offset (offset + 1) :: reversed)
        | ']' ->
            scan (offset + 1) (token Right_bracket offset (offset + 1) :: reversed)
        | '-' when offset + 1 < length && source.[offset + 1] = '>' ->
            scan (offset + 2) (token Arrow_token offset (offset + 2) :: reversed)
        | _ ->
            fail_at offset
              (Printf.sprintf "unexpected character %C" character)
  in
  scan 0 []

type parser_state = {
  tokens : token array;
  mutable cursor : int;
}

let current state = state.tokens.(state.cursor)

let consume state =
  let token = current state in
  state.cursor <- state.cursor + 1;
  token

let expect_fixed state expected description =
  let token = current state in
  if token.kind = expected then ignore (consume state)
  else fail_at token.span.start_offset description

let expect_name state description =
  match (current state).kind with
  | Ident name ->
      let token = consume state in
      name, token.span
  | _ -> fail_at (current state).span.start_offset description

let nat_of_nonnegative_int value =
  if value < 0 then invalid_arg "nat_of_nonnegative_int" else value

let resolve_name namespace name span environment =
  let rec find index = function
    | [] ->
        fail_at span.start_offset
          ("unbound " ^ namespace ^ " variable '" ^ name ^ "'")
    | candidate :: rest ->
        if candidate = name then nat_of_nonnegative_int index
        else find (index + 1) rest
  in
  find 0 environment

let begins_term_atom = function
  | Ident _ | Left_paren -> true
  | _ -> false

let rec parse_type state type_environment =
  match (current state).kind with
  | Forall ->
      ignore (consume state);
      let name, _ =
        expect_name state "expected a type-variable name after 'forall'"
      in
      expect_fixed state Dot "expected '.' after the quantified type variable";
      TForall (parse_type state (name :: type_environment))
  | _ -> parse_arrow_type state type_environment

and parse_arrow_type state type_environment =
  let domain = parse_type_atom state type_environment in
  match (current state).kind with
  | Arrow_token ->
      ignore (consume state);
      TArrow (domain, parse_type state type_environment)
  | _ -> domain

and parse_type_atom state type_environment =
  let token = current state in
  match token.kind with
  | Ident name ->
      ignore (consume state);
      TVar (resolve_name "type" name token.span type_environment)
  | Left_paren ->
      ignore (consume state);
      let ty = parse_type state type_environment in
      expect_fixed state Right_paren "expected ')' after the type";
      ty
  | _ -> fail_at token.span.start_offset "expected a type"

let rec parse_term state term_environment type_environment =
  match (current state).kind with
  | Fun -> parse_term_lambda state term_environment type_environment
  | Type_lambda ->
      ignore (consume state);
      let name, _ =
        expect_name state "expected a type-variable name after 'Lambda'"
      in
      expect_fixed state Dot "expected '.' after the type abstraction";
      FTLam
        (parse_term state term_environment (name :: type_environment))
  | _ -> parse_elimination state term_environment type_environment

and parse_term_lambda state term_environment type_environment =
  ignore (consume state);
  let parenthesized =
    match (current state).kind with
    | Left_paren -> ignore (consume state); true
    | _ -> false
  in
  let name, _ = expect_name state "expected a name after 'fun'" in
  expect_fixed state Colon "expected ':' before the parameter type";
  let annotation = parse_type state type_environment in
  if parenthesized then begin
    expect_fixed state Right_paren "expected ')' after the typed parameter";
    expect_fixed state Arrow_token "expected '->' after the typed parameter"
  end else
    expect_fixed state Dot "expected '.' after the parameter type";
  FLam
    (annotation,
     parse_term state (name :: term_environment) type_environment)

and parse_elimination state term_environment type_environment =
  let head = parse_term_atom state term_environment type_environment in
  let rec suffixes accumulated =
    match (current state).kind with
    | Left_bracket ->
        ignore (consume state);
        let argument = parse_type state type_environment in
        expect_fixed state Right_bracket "expected ']' after the type argument";
        suffixes (FTApp (accumulated, argument))
    | kind when begins_term_atom kind ->
        let argument =
          parse_term_atom state term_environment type_environment
        in
        suffixes (FApp (accumulated, argument))
    | _ -> accumulated
  in
  suffixes head

and parse_term_atom state term_environment type_environment =
  let token = current state in
  match token.kind with
  | Ident name ->
      ignore (consume state);
      FVar (resolve_name "term" name token.span term_environment)
  | Left_paren ->
      ignore (consume state);
      let term = parse_term state term_environment type_environment in
      expect_fixed state Right_paren "expected ')' after the term";
      term
  | _ -> fail_at token.span.start_offset "expected a term"

let parse_church_program source =
  try
    let state = { tokens = tokenize source; cursor = 0 } in
    let raw = parse_term state [] [] in
    let trailing = current state in
    begin
      match trailing.kind with
      | End -> ()
      | _ -> fail_at trailing.span.start_offset "unexpected trailing input"
    end;
    Church_parsed raw
  with Frontend_error diagnostic -> Church_parse_error diagnostic

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
