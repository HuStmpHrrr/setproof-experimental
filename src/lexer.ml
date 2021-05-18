open Base
module Token = Grammar

exception InvalidToken of int * int * string

let const lexbuf data =
  ignore (Sedlexing.lexeme lexbuf);
  data

let skip lexbuf = ignore (Sedlexing.lexeme lexbuf)

let block_comment_lexeme lexbuf =
  let rec helper depth =
    [%sedlex
      match lexbuf with
      | "{-" -> Sedlexing.Utf8.lexeme lexbuf ^ helper (depth + 1)
      | "-}" ->
          Sedlexing.Utf8.lexeme lexbuf
          ^ if depth = 1 then "" else helper (depth - 1)
      | any  -> Sedlexing.Utf8.lexeme lexbuf ^ helper depth
      | _    -> failwith ""]
  in
  helper 1

let line_comment = [%sedlex.regexp? "--", Star (Compl '\n')]

let gen_lexer lexbuf =
  let rec lexer lexbuf =
    [%sedlex
      match lexbuf with
      (* Whitespace-like tokens *)
      | eof -> const lexbuf Token.EOF
      | white_space ->
          skip lexbuf;
          lexer lexbuf
      | line_comment ->
          skip lexbuf;
          lexer lexbuf
      | Star ('0'..'9') ->
         Token.INTEGER (Int.of_string (Sedlexing.Utf8.lexeme lexbuf))
      | "{-" ->
          ignore (block_comment_lexeme lexbuf);
          lexer lexbuf
      (* Keywords *)
      | "pi" -> const lexbuf Token.KEY_PI
      | "lam" -> const lexbuf Token.KEY_LAM
      | "qind" -> const lexbuf Token.KEY_QIND
      | "where" -> const lexbuf Token.KEY_WHERE
      | "match" -> const lexbuf Token.KEY_MATCH
      | "with" -> const lexbuf Token.KEY_WITH
      | "refl" -> const lexbuf Token.KEY_REFL
      | "Univ" -> const lexbuf Token.KEY_UNIV
      (* Symbols *)
      | "(" -> const lexbuf Token.SYM_LPAR
      | ")" -> const lexbuf Token.SYM_RPAR
      (* | "[" -> const lexbuf Token.SYM_LSBR
       * | "]" -> const lexbuf Token.SYM_RSBR
       * | "{" -> const lexbuf Token.SYM_LBRA
       * | "}" -> const lexbuf Token.SYM_RBRA *)
      | ":=" -> const lexbuf Token.SYM_DEFEQ
      | "->" -> const lexbuf Token.SYM_ARROW
      | ":" -> const lexbuf Token.SYM_COLON
      | "," -> const lexbuf Token.SYM_COMMA
      | ";" -> const lexbuf Token.SYM_SEMI
      | "=" -> const lexbuf Token.SYM_EQ
      | "_" -> const lexbuf Token.SYM_UNDERSCORE
      | "_" | id_start, Star id_continue ->
          let tok = Sedlexing.Utf8.lexeme lexbuf in
          if Char.is_uppercase (String.get tok 0)
          then Token.UPPER_IDENT tok
          else Token.LOWER_IDENT tok
      | _ ->
          let l, c = Sedlexing.loc lexbuf in
          let tok = Sedlexing.Utf8.lexeme lexbuf in
          raise (InvalidToken (l, c, tok))]
  in
  Sedlexing.with_tokenizer lexer lexbuf
