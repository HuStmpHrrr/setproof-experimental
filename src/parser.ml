open Base
module I = Grammar.MenhirInterpreter
module S = MenhirLib.General

exception ParserError of string

let state env : int =
  match Lazy.force (I.stack env) with
  | S.Nil -> 0 (* hacky initial state *)
  | S.Cons (Element (s, _, _, _), _) -> I.number s

let rec loop next_token lexbuf (checkpoint : Ext_ast.module_def I.checkpoint) =
  match checkpoint with
  | I.InputNeeded _env ->
      let token = next_token () in
      let checkpoint = I.offer checkpoint token in
      loop next_token lexbuf checkpoint
  | I.Shifting _ | I.AboutToReduce _ ->
      let checkpoint = I.resume checkpoint in
      loop next_token lexbuf checkpoint
  | I.HandlingError env -> raise (ParserError ("Syntax error!" ^ Int.to_string (state env)))
  | I.Accepted module_def -> module_def
  | I.Rejected ->
      (* Cannot happen as we stop at syntax error immediatly *)
     assert false

let parse_channel name chan =
  let lexbuf = Sedlexing.Utf8.from_channel chan in
  Sedlexing.set_filename lexbuf name;
  let lexer = Lexer.gen_lexer lexbuf in
  try
    loop lexer lexbuf
      (Grammar.Incremental.modDef (fst @@ Sedlexing.lexing_positions lexbuf))
  with Lexer.InvalidToken (line, column, tok) ->
    raise
      (ParserError
         (Stdlib.Format.sprintf "lexing error : %s at %d:%d%!" tok line column))

let parse_file file = Stdio.In_channel.with_file ~f:(parse_channel file) file
