open Lib

module P = MParser_wrapper
module E = Ext_ast
open P

let _ = debugging_level := 0

exception DuplicatedKeyword of string
exception ParserError of string

let integer = gen_integer ()

let block_comment = gen_block_comment "{-" "-}"

let line_comment = gen_line_comment "--"

let lex_spaces =
  String.concat
  <$> many (block_comment <|> line_comment <|> many1_chars space)
  <?> "whitespaces"

let lex p = p << lex_spaces
let lexchar c = lex (char c)
let lexstring s = lex (string s)

let with_loc p =
  let+ file = get_user_state
  and+ _, start_l, start_c = get_pos
  and+ d = p
  and+ _, end_l, end_c = get_pos in
  (RealLoc { file; start_l; start_c; end_l; end_c; data = () }, d)

let open_pair p = lex (with_loc p)
let close_pair open_name close_name loc p =
  lex p
  <?> Caml.Format.asprintf "%s matching with %s at %a" close_name open_name
        real_pp_loc loc

let open_paren = open_pair (char '(')
let close_paren loc =
  close_pair "opening parenthesis" "closing parenthesis" loc (char ')')

let id_following_chars = char '_' <|> alphanum

let keyword, lower_identifier, capital_identifier =
  let keywords = ref [] in
  let keyword id =
    if List.mem ~equal:String.equal !keywords id
    then raise (DuplicatedKeyword id);
    keywords := id :: !keywords;
    let* _ = string id in
    not_followed_by id_following_chars "Non-keyword"
  in
  let identifier_helper start =
    let helper =
      let+ c = start
      and+ cs = many id_following_chars in
      String.of_char_list (c :: cs)
    in
    let* s = look_ahead helper in
    if List.mem ~equal:String.equal !keywords s
    then message (s ^ " is a keyword")
    else
      let+ _ = helper in
      s
  in
  let lower_identifier =
    identifier_helper (char '_' <|> lowercase) <?> "lower-cased identifier"
  in
  let capital_identifier =
    identifier_helper uppercase <?> "Capital-cased identifier"
  in
  (keyword, lower_identifier, capital_identifier)

let key_pi = keyword "pi"
let key_lam = keyword "lam"
let key_data = keyword "data"
let key_where = keyword "where"
let key_quotient = keyword "quotient"
let key_match = keyword "match"
let key_with = keyword "with"
let key_Refl = keyword "Refl"
let key_Univ = keyword "Univ"

let refl_pattern =
  let+ l1, _ = lex (with_loc key_Refl)
  and+ l2, arg = lex (with_loc lower_identifier) in
  E.PatEq (loc_combine l1 l2, arg)

let constr_pattern =
  let+ l1, constr = lex (with_loc capital_identifier)
  and+ args = many (lex (with_loc capital_identifier)) in
  match List.last args with
  | None         -> E.PatInd (l1, constr, List.map ~f:snd args)
  | Some (l2, _) -> E.PatInd (loc_combine l1 l2, constr, List.map ~f:snd args)

let var_pattern =
  let+ l1, arg = lex (with_loc lower_identifier) in
  E.PatVar (l1, arg)

let pattern = refl_pattern <|> constr_pattern <|> var_pattern

let branch body_tm =
  let+ pat = pattern <??> "pattern"
  and+ _ = lexstring "->"
  and+ body_tm = body_tm <??> "body of branch"
  and+ _ = lexchar ';' in
  (pat, body_tm)

let lam_tm arg_ty body_tm =
  let* l1, _ = lex (with_loc key_lam)
  and* l, _ = open_paren in
  let+ arg = lex lower_identifier <?> "name of argument of lambda"
  and+ arg_ty = lexchar ':' >> arg_ty <??> "type of argument of lambda"
  and+ _ = close_paren l
  and+ _ = lexchar ','
  and+ body_tm = body_tm <??> "body of lambda" in
  E.TmLam (loc_combine l1 (E.tm_loc body_tm), arg, arg_ty, body_tm)

let pi_tm idx_ty idxed_ty =
  let* l1, _ = lex (with_loc key_pi)
  and* l, _ = open_paren in
  let+ idx = lex lower_identifier <?> "name of argument of pi"
  and+ idx_ty = lexchar ':' >> idx_ty <??> "type of argument of pi"
  and+ _ = close_paren l
  and+ _ = lexstring "->"
  and+ idxed_ty = idxed_ty <??> "codomain of pi" in
  E.TmPi (loc_combine l1 (E.tm_loc idxed_ty), idx, idx_ty, idxed_ty)

let arrow_tm idx_ty idxed_ty =
  let+ idx_ty = attempt (idx_ty << lexstring "->")
  and+ idxed_ty = idxed_ty in
  E.TmPi
    (loc_combine (E.tm_loc idx_ty) (E.tm_loc idxed_ty), "_", idx_ty, idxed_ty)

let quotient_branches br_tm =
  let+ l1, _ = lex (with_loc key_quotient)
  and+ eqs = many (branch br_tm) <??> "quotient branches of match" in
  match List.last eqs with
  | None        -> (Some l1, eqs)
  | Some (_, t) -> (Some (E.tm_loc t), eqs)

let match_tm scr_tm br_tm =
  let snd_tm_loc (_, t) = E.tm_loc t in
  let* l1, _ = open_pair key_match in
  let+ scr = scr_tm <??> "scrutinee of match"
  and+ l2, _ = close_pair "match" "with" l1 (with_loc key_with)
  and+ cs = many (branch br_tm) <??> "constructor branches of match"
  and+ ol3, eqs = opt (None, []) (quotient_branches br_tm) in
  match Option.(first_some ol3 (map ~f:snd_tm_loc (List.last cs))) with
  | None    -> Ext_ast.TmMatch (loc_combine l1 l2, scr, cs, eqs)
  | Some l3 -> Ext_ast.TmMatch (loc_combine l1 l3, scr, cs, eqs)

let eq_tm hs_tm =
  let+ lhs_tm = attempt (hs_tm << lexstring "=")
  and+ rhs_tm = hs_tm in
  E.TmEq (loc_combine (E.tm_loc lhs_tm) (E.tm_loc rhs_tm), lhs_tm, rhs_tm)

let refl_tm arg_tm =
  let+ l1, _ = lex (with_loc key_Refl)
  and+ arg_tm = arg_tm <??> "argument of Refl" in
  E.TmRefl (loc_combine l1 (E.tm_loc arg_tm), arg_tm)

let univ_with_level_tm =
  let+ l1, _ = lex (with_loc key_Univ)
  and+ l2, lv = lex (with_loc integer) in
  E.TmUniv (loc_combine l1 l2, lv)

let univ_no_level_tm =
  let+ l1, _ = lex (with_loc key_Univ) in
  E.TmUniv (l1, 0)

let constr_tm =
  debug 3 "constr_tm" E.pp_tm
    (let+ l1, constr = lex (with_loc capital_identifier) in
     E.TmConstr (l1, constr))

let var_tm =
  debug 3 "var_tm" E.pp_tm
    (let+ l1, var = lex (with_loc lower_identifier) in
     E.TmVar (l1, var))

let app_stack atomic_tm =
  let app_folder fun_tm arg_tm =
    E.TmApp (loc_combine (E.tm_loc fun_tm) (E.tm_loc arg_tm), fun_tm, arg_tm)
  in
  let* atomic_tms =
    debug 4 "many atomic_tm"
      (Caml.Format.pp_print_list E.pp_tm)
      (many1 atomic_tm)
  in
  match atomic_tms with
  | []                      -> fail "impossible case"
  | atomic_tm :: atomic_tms ->
      return (List.fold_left ~init:atomic_tm ~f:app_folder atomic_tms)

let tm =
  recur (fun tm ->
      let parened_tm =
        let* l, _ = open_paren in
        let+ tm = tm
        and+ _ = close_paren l in
        tm
      in
      let atomic_tm =
        debug 2 "atomic_tm" E.pp_tm
          (univ_no_level_tm <|> constr_tm <|> var_tm <|> parened_tm)
      in
      let application_tm =
        debug 2 "application_tm" E.pp_tm
          (univ_with_level_tm <|> refl_tm atomic_tm <|> app_stack atomic_tm)
      in
      let equality_tm = eq_tm application_tm <|> application_tm in
      lam_tm tm tm
      <|> pi_tm tm tm
      <|> match_tm tm tm
      <|> arrow_tm equality_tm tm
      <|> equality_tm
  )

let fun_def =
  let* l1, fid = open_pair lower_identifier in
  let+ fty = lexchar ':' >> tm <??> "type of function"
  and+ _ = lexstring ":="
  and+ fbody = tm <??> "body of function"
  and+ l2, _ =
    close_pair ("function \"" ^ fid ^ "\"") "';'" l1 (with_loc (char ';'))
  in
  E.FunDef (loc_combine l1 l2, fid, fty, fbody)

let quot_ind_entry =
  let* l1, eid = open_pair capital_identifier in
  let+ ety = lexchar ':' >> tm <??> "type of quotient"
  and+ l2, _ =
    close_pair ("quotient \"" ^ eid ^ "\"") "';'" l1 (with_loc (char ';'))
  in
  E.QuotIndEntryDef (loc_combine l1 l2, eid, ety)

let quot_ind_def =
  let quot_ind_idx =
    let* l, _ = open_paren in
    let+ idx = lex lower_identifier
    and+ idx_ty = lexchar ':' >> tm <??> "type of index"
    and+ _ = close_paren l in
    (idx, idx_ty)
  in
  let* l1, _ = open_pair key_data in
  let+ quot_id = lex lower_identifier
  and+ quot_indices = many quot_ind_idx
  and+ quot_kind = lexchar ':' >> tm <??> "kind of quotient inductive type"
  and+ _ = close_pair "\"data\"" "\"where\"" l1 key_where
  and+ quot_constrs =
    many quot_ind_entry <??> "constructors of quotient inductive type"
  and+ quot_quotients =
    opt []
      (let* _ = lex key_quotient in
       many quot_ind_entry <??> "quotients of quotient inductive type")
  and+ l2, _ = close_pair "\"data\"" "';'" l1 (with_loc (lexchar ';')) in
  let quot_loc = loc_combine l1 l2 in
  E.QuotIndDef
    { quot_loc; quot_id; quot_indices; quot_kind; quot_constrs; quot_quotients }

let top_stmt =
  map ~f:(fun t -> E.TopQuotInd t) quot_ind_def
  <|> map ~f:(fun t -> E.TopFunDef t) fun_def

let mod_def =
  debug 1 "module" E.pp_module_def
    (let* _ = debug 0 "module" Caml.Format.pp_print_string lex_spaces in
     let+ stmts = many top_stmt
     and+ _ = eof <?> "end of file" in
     E.ModDef stmts)

let parse_file file =
  let use_channel ch =
    match parse_channel mod_def ch file with
    | Success m       -> m
    | Failed (msg, _) -> raise (ParserError msg)
  in
  Stdio.In_channel.with_file ~f:use_channel file
