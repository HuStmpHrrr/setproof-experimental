open Lib

module P = ParserWrapper
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

let lex p = p <* ignore_m lex_spaces
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
  <?> Caml.Format.asprintf "closing %s matching with opening %s at %a"
        close_name open_name real_pp_loc loc
let close_pair' pair_name l p = close_pair pair_name pair_name l p

let id_following_chars = char '_' <|> alphanum

let keyword, lower_identifier, upper_identifier =
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
      let+ _ = skip helper in
      s
  in
  let lower_identifier = identifier_helper (char '_' <|> lowercase) in
  let upper_identifier = identifier_helper uppercase in
  (keyword, lower_identifier, upper_identifier)

let key_pi = keyword "pi"
let key_lam = keyword "lam"
let key_data = keyword "data"
let key_where = keyword "where"
let key_quotient = keyword "quotient"
let key_match = keyword "match"
let key_with = keyword "with"
let key_Refl = keyword "Refl"
let key_Univ = keyword "Univ"

let tm_loc = function
  | E.TmUniv (l, _)        -> l
  | E.TmConstr (l, _)      -> l
  | E.TmVar (l, _)         -> l
  | E.TmLam (l, _, _, _)   -> l
  | E.TmPi (l, _, _, _)    -> l
  | E.TmMatch (l, _, _, _) -> l
  | E.TmApp (l, _, _)      -> l
  | E.TmEq (l, _, _)       -> l
  | E.TmRefl (l, _)        -> l

let loc_of_pattern = function
  | E.PatVar (l, _)    -> l
  | E.PatInd (l, _, _) -> l
  | E.PatEq (l, _)     -> l

let refl_pattern =
  let+ l1, _ = lex (with_loc key_Refl)
  and+ l2, arg = lex (with_loc lower_identifier) in
  E.PatEq (loc_combine l1 l2, arg)

let constr_pattern =
  let+ l1, constr = lex (with_loc upper_identifier)
  and+ args = many (lex (with_loc upper_identifier)) in
  match List.last args with
  | None         -> E.PatInd (l1, constr, List.map ~f:snd args)
  | Some (l2, _) -> E.PatInd (loc_combine l1 l2, constr, List.map ~f:snd args)

let var_pattern =
  let+ l1, arg = lex (with_loc lower_identifier) in
  E.PatVar (l1, arg)

let pattern = refl_pattern <|> constr_pattern <|> var_pattern

let branch body_tm =
  let+ pat = pattern
  and+ _ = lexstring "->"
  and+ body_tm = body_tm
  and+ _ = lexchar ';' in
  (pat, body_tm)

let lam_tm arg_ty body_tm =
  (let+ l1, _ = lex (with_loc key_lam)
   and+ arg = lex lower_identifier
   and+ _ = lexchar ':'
   and+ arg_ty = arg_ty
   and+ _ = lexchar ','
   and+ body_tm = body_tm in
   E.TmLam (loc_combine l1 (tm_loc body_tm), arg, arg_ty, body_tm))
  <?> "lambda term"

let pi_tm idx_ty idxed_ty =
  let+ l1, _ = lex (with_loc key_pi)
  and+ _ = lexchar '('
  and+ idx = lex lower_identifier
  and+ _ = lexchar ':'
  and+ idx_ty = idx_ty
  and+ _ = lexchar ')'
  and+ _ = lexstring "->"
  and+ idxed_ty = idxed_ty in
  E.TmPi (loc_combine l1 (tm_loc idxed_ty), idx, idx_ty, idxed_ty)

let arrow_tm idx_ty idxed_ty =
  let+ idx_ty = attempt (idx_ty <* skip (lexstring "->"))
  and+ idxed_ty = idxed_ty in
  E.TmPi (loc_combine (tm_loc idx_ty) (tm_loc idxed_ty), "_", idx_ty, idxed_ty)

let quotient_branches br_tm =
  let+ l1, _ = lex (with_loc key_quotient)
  and+ eqs = many (branch br_tm) in
  match List.last eqs with
  | None        -> (Some l1, eqs)
  | Some (_, t) -> (Some (tm_loc t), eqs)

let match_tm scr_tm br_tm =
  let snd_tm_loc (_, t) = tm_loc t in
  let+ l1, _ = lex (with_loc key_match)
  and+ scr = scr_tm
  and+ l2, _ = lex (with_loc key_with)
  and+ cs = many (branch br_tm)
  and+ ol3, eqs = quotient_branches br_tm <|> return (None, []) in
  match Option.(first_some ol3 (map ~f:snd_tm_loc (List.last cs))) with
  | None    -> Ext_ast.TmMatch (loc_combine l1 l2, scr, cs, eqs)
  | Some l3 -> Ext_ast.TmMatch (loc_combine l1 l3, scr, cs, eqs)

let eq_tm hs_tm =
  let+ lhs_tm = attempt (hs_tm <* skip (lexstring "="))
  and+ rhs_tm = hs_tm in
  E.TmEq (loc_combine (tm_loc lhs_tm) (tm_loc rhs_tm), lhs_tm, rhs_tm)

let refl_tm arg_tm =
  let+ l1, _ = lex (with_loc key_Refl)
  and+ arg_tm = arg_tm in
  E.TmRefl (loc_combine l1 (tm_loc arg_tm), arg_tm)

let univ_tm =
  let+ l1, _ = lex (with_loc key_Univ)
  and+ l2, lv = lex (with_loc integer) in
  E.TmUniv (loc_combine l1 l2, lv)

let constr_tm =
  let+ l1, constr = lex (with_loc upper_identifier) in
  E.TmConstr (l1, constr)

let var_tm =
  debug 1 "var_tm" E.pp_tm
    (let+ l1, var = lex (with_loc lower_identifier) in
     E.TmVar (l1, var))

let app_stack atomic_tm =
  let app_folder fun_tm arg_tm =
    E.TmApp (loc_combine (tm_loc fun_tm) (tm_loc arg_tm), fun_tm, arg_tm)
  in
  let* atomic_tms =
    debug 1 "many atomic_tm"
      (Caml.Format.pp_print_list E.pp_tm)
      (many1 (debug 1 "atomic_tm" E.pp_tm atomic_tm))
  in
  match atomic_tms with
  | []                      -> fail "impossible case"
  | atomic_tm :: atomic_tms ->
      return (List.fold_left ~init:atomic_tm ~f:app_folder atomic_tms)

let tm =
  recur (fun tm ->
      let parened_tm =
        let* l, _ = open_pair (char '(') in
        let+ tm = tm
        and+ _ = close_pair' "parenthesis" l (char ')') in
        tm
      in
      let atomic_tm =
        debug 1 "atomic_tm" E.pp_tm (constr_tm <|> var_tm <|> parened_tm)
      in
      let application_tm =
        debug 1 "application_tm" E.pp_tm
          (univ_tm <|> refl_tm atomic_tm <|> app_stack atomic_tm)
      in
      let equality_tm = eq_tm application_tm <|> application_tm in
      lam_tm tm tm
      <|> pi_tm tm tm
      <|> match_tm tm tm
      <|> arrow_tm equality_tm tm
      <|> equality_tm
  )

let fun_def =
  let+ l1, fid = lex (with_loc lower_identifier)
  and+ _ = lexchar ':'
  and+ fty = tm
  and+ _ = lexstring ":="
  and+ fbody = tm
  and+ l2, _ = lex (with_loc (char ';')) in
  E.FunDef (loc_combine l1 l2, fid, fty, fbody)

let quot_ind_entry =
  let* l1, eid = open_pair upper_identifier in
  let+ _ = lexchar ':'
  and+ ety = tm
  and+ l2, _ = close_pair "quotient \"eid\"" "';'" l1 (with_loc (char ';')) in
  E.QuotIndEntryDef (loc_combine l1 l2, eid, ety)

let quot_ind_def =
  let quot_ind_idx =
    let* l, _ = open_pair (char '(') in
    let+ idx = lex lower_identifier
    and+ _ = lexchar ':'
    and+ idx_ty = tm
    and+ _ = close_pair' "parenthesis" l (char ')') in
    (idx, idx_ty)
  in
  let* l1, _ = open_pair key_data in
  let+ quot_id = lex lower_identifier
  and+ quot_indices = many quot_ind_idx
  and+ _ = lexchar ':'
  and+ quot_kind = tm <?> "kind of quotient inductive type"
  and+ _ = close_pair "\"data\"" "\"where\"" l1 key_where
  and+ quot_constrs = many quot_ind_entry
  and+ quot_quotients = lex key_quotient *> many quot_ind_entry <|> return []
  and+ l2, _ = close_pair "\"data\"" "';'" l1 (with_loc (lexchar ';')) in
  let quot_loc = loc_combine l1 l2 in
  E.QuotIndDef
    { quot_loc; quot_id; quot_indices; quot_kind; quot_constrs; quot_quotients }

let top_stmt =
  map ~f:(fun t -> E.TopQuotInd t) quot_ind_def
  <|> map ~f:(fun t -> E.TopFunDef t) fun_def

let mod_def =
  debug 0 "module" E.pp_module_def
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
