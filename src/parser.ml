open Base
open Earley_core
module Ext = Ext_ast

(* Location function. *)
let locate str1 start_c str2 end_c =
  let file = Input.filename str1 in
  let start_l  = Input.line_num str1 in
  let end_l  = Input.line_num str2 in
  Lib.(RealLoc { file; start_l; start_c; end_l; end_c; data = () })

#define LOCATE locate

let _ = Earley.keep_all_names := true

let ident_rest = "[_a-zA-Z0-9]"

module K =
  Keywords.Make
    (struct
      let id_charset = Charset.from_string ident_rest
      let reserved = []
    end)

let key_Univ = K.create "Univ"
let key_Refl = K.create "Refl"
let key_lam = K.create "lam"
let key_pi = K.create "pi"
let key_match = K.create "match"
let key_with = K.create "with"
let key_quotient = K.create "quotient"
let key_data = K.create "data"
let key_where = K.create "where"

let blank = Blanks.line_comments "--"

let parser integer =
  i:RE("0\\|[1-9][0-9]") -> Int.of_string i

let parser lower_ident =
  i:RE("\\(_\\|[a-z]\\)" ^ ident_rest ^ "*") -> K.check i; i

let parser upper_ident =
  i:RE("[A-Z]" ^ ident_rest ^ "*") -> K.check i; i

let parser branch tm = p:pattern "->" t:tm ';' -> (p, t)
and parser pattern = pattern0
and parser pattern0 =
  | cid:upper_ident args:pattern1* -> Ext.PatInd(Lib.loc_combine _loc_cid _loc_args, cid, args)
  | _s:key_Refl p:pattern1         -> Ext.PatEq(Lib.loc_combine _loc__s _loc_p, p)
  | pattern1
and parser pattern1 =
  | id:lower_ident    -> Ext.PatVar (_loc_id, id)
  | '(' p:pattern ')' -> p

let parser lam_tm (ty, tm) =
  _s:key_lam id:lower_ident ':' tau:ty ',' t:tm -> Ext.TmLam(Lib.loc_combine _loc__s _loc_t, id, tau, t)

let parser pi_tm (ty, ty') =
  _s:key_pi '(' id:lower_ident ':' tau:ty ')' "->" tau':ty' -> Ext.TmPi(Lib.loc_combine _loc__s _loc_tau', id, tau, tau')

let parser arrow_tm (ty, ty') =
  tau:ty "->" tau':ty' -> Ext.TmPi(Lib.loc_combine _loc_tau _loc_tau', "_", tau, tau')

let parser match_tm (scr, br_tm) =
  _s:key_match scr:scr key_with cbrs:(branch br_tm)* opt_qbrs:{key_quotient qbrs:(branch br_tm)* -> qbrs}? ->
    (match opt_qbrs with
     | Some qbrs -> Ext.TmMatch(Lib.loc_combine _loc__s _loc_opt_qbrs, scr, cbrs, qbrs)
     | None      -> Ext.TmMatch(Lib.loc_combine _loc__s _loc_cbrs, scr, cbrs, []))

let parser eq_tm tm =
  lhs:tm '=' rhs:tm -> Ext.TmEq(Lib.loc_combine _loc_lhs _loc_rhs, lhs, rhs)

let parser app_tm (tm, tm') =
  f:tm a:tm' -> Ext.TmApp(Lib.loc_combine _loc_f _loc_a, f, a)

let parser refl_tm tm =
  _s:key_Refl t:tm -> Ext.TmRefl(Lib.loc_combine _loc__s _loc_t, t)

let parser univ_tm =
  _s:key_Univ i:integer -> Ext.TmUniv(Lib.loc_combine _loc__s _loc_i, i)

let parser cstr_tm =
  cid:upper_ident -> Ext.TmConstr(_loc_cid, cid)

let parser var_tm =
  id:lower_ident -> Ext.TmVar(_loc_id, id)

let parser tm0 =
  | (lam_tm (tm0, tm0))
  | (pi_tm (tm0, tm0))
  | (match_tm (tm0, tm0))
  | (arrow_tm (tm1, tm0))
  | tm1
and parser tm1 =
  | (eq_tm tm2)
  | tm2
and parser tm2 =
  | (app_tm (tm2, tm3))
  | (refl_tm tm3)
  | univ_tm
  | tm3
and parser tm3 =
  | cstr_tm
  | var_tm
  | tm4
and parser tm4 =
  | '(' t:tm0 ')' -> t
and parser tm = tm0

let parser fun_def =
  i:lower_ident ':' tau:tm ":=" t:tm _e:';' -> Ext.FunDef(Lib.loc_combine _loc_i _loc__e, i, tau, t)

let parser quot_ind_entry =
  i:upper_ident ':' tau:tm _e:';' -> Ext.QuotIndEntryDef(Lib.loc_combine _loc_i _loc__e, i, tau)

let parser quot_ind =
  _s:key_data i:lower_ident idxs:{'(' i:lower_ident ':' tau:tm ')' -> (i, tau)}* ':' kappa:tm key_where
    cstrs:quot_ind_entry*
    quots:{key_quotient quots:quot_ind_entry* -> quots}?[[]]
  _e:';' -> Ext.QuotIndDef(Lib.loc_combine _loc__s _loc__e, i, idxs, kappa, cstrs, quots)

let parser top_stmt =
  | f:fun_def  -> Ext.TopFunDef f
  | q:quot_ind -> Ext.TopQuotInd q

let parser mod_def = ts:top_stmt* EOF -> Ext.ModDef ts

let parse_file = Earley.parse_file mod_def blank
