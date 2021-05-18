open Lib

module Ext = Ext_ast
module Int = Ast

type constr_entry = (string, string) Either.t
type constr_ctx = constr_entry StrM.t
type var_entry = int option
type var_ctx = var_entry list StrM.t

exception DuplicatedConstrIds of string * (constr_entry * constr_entry)
exception UnknownConstrId of string * loc
exception UnknownVarId of string * loc
exception InvalidQITKind of Ext.ty
exception InvalidQITQuotient of Ext.ty
exception InvalidQITConstructor of Ext.ty

let vctx_shiftn n = Map.map ~f:(List.map ~f:(Option.map ~f:(( + ) n)))
let vctx_shift1 = vctx_shiftn 1

let vctx_add vctx id = Map.add_multi (vctx_shiftn 1 vctx) ~key:id ~data:(Some 0)

let rec elab_tm (cctx : constr_ctx) (vctx : var_ctx) : Ext.tm -> Int.tm =
  function
  | Ext.TmUniv (loc, lev) -> Int.U (lev, loc)
  | Ext.TmConstr (loc, id) -> (
      let open Option in
      let open Either in
      match Map.find cctx id with
      | Some (First tid)  -> Int.Constr (tid, Loc.put loc id)
      | Some (Second tid) -> Int.EqConstr (tid, Loc.put loc id)
      | None              -> raise (UnknownConstrId (id, loc)))
  | Ext.TmVar (loc, id) -> (
      let open Option in
      match Map.find vctx id >>= List.hd with
      | Some (Some idx) -> Int.Var (idx, Loc.put loc (Some id))
      | Some None       -> Int.Glob (Loc.put loc id)
      | None            -> raise (UnknownVarId (id, loc)))
  | Ext.TmLam (loc, id, e_tau, e_t) ->
      let vctx' = vctx_add vctx id in
      Int.Lam (elab_tm cctx vctx e_tau, elab_tm cctx vctx' e_t, loc)
  | Ext.TmPi (_, id, e_tau0, e_tau1) ->
      let vctx' = vctx_add vctx id in
      Int.Pi (elab_tm cctx vctx e_tau0, elab_tm cctx vctx' e_tau1)
  | Ext.TmMatch (loc, e_scr, e_cstr_bs, e_quot_bs) ->
      Int.Case
        ( elab_tm cctx vctx e_scr,
          List.map ~f:(elab_branch cctx vctx) e_cstr_bs,
          List.map ~f:(elab_branch cctx vctx) e_quot_bs,
          loc )
  | Ext.TmApp (_, e_f, e_a) ->
      Int.App (elab_tm cctx vctx e_f, elab_tm cctx vctx e_a)
  | Ext.TmEq (_, e_lhs, e_rhs) ->
      Int.Eq
        { tm_ltm = elab_tm cctx vctx e_lhs; tm_rtm = elab_tm cctx vctx e_rhs }
  | Ext.TmRefl (loc, e_t) -> Int.Refl (elab_tm cctx vctx e_t, loc)

and elab_branch (cctx : constr_ctx) (vctx : var_ctx) :
    Ext.branch -> Int.pattern * Int.tm =
 fun (e_p, e_t) ->
  let vctx, i_p = elab_pattern cctx vctx e_p in
  (i_p, elab_tm cctx vctx e_t)

and elab_pattern (cctx : constr_ctx) (vctx : var_ctx) :
    Ext.pattern -> var_ctx * Int.pattern = function
  | Ext.PatWildcard loc        -> (vctx_shift1 vctx, Int.PVar (Loc.put loc None))
  | Ext.PatVar (loc, id)       ->
      (vctx_add vctx id, Int.PVar (Loc.put loc (Some id)))
  | Ext.PatInd (loc, id, e_ps) ->
      let tid =
        let open Option in
        match Map.find cctx id with
        | Some (First tid)  -> tid
        | Some (Second tid) -> tid
        | None              -> raise (UnknownConstrId (id, loc))
      in
      let vctx, i_ps = List.fold_map ~f:(elab_pattern cctx) ~init:vctx e_ps in
      ( vctx,
        Int.PCase
          (Int.IndCase
             { tm_ind_name = tid; tm_constr = Loc.put loc id; tm_args = i_ps })
      )
  | Ext.PatEq (_, e_p)         ->
      let vctx, i_p = elab_pattern cctx vctx e_p in
      (vctx, Int.PCase (Int.EqCase i_p))

let elab_fun_def (cctx : constr_ctx) (vctx : var_ctx) :
    Ext.fun_def -> Int.fun_def =
 fun (Ext.FunDef (loc, id, e_tau, e_t)) ->
  Int.
    {
      fun_name = Loc.put loc id;
      fun_type = elab_tm cctx vctx e_tau;
      fun_body = elab_tm cctx vctx e_t;
    }

let elab_constructor (cctx : constr_ctx) (vctx : var_ctx) :
    Ext.quotient_inductive_entry_def -> string * (Int.telescope * Int.tm list) =
 fun (QuotIndEntryDef (loc, id, e_tau)) ->
  let rec destruct_apps acc = function
    | Int.App (i_tau, idx) -> destruct_apps (idx :: acc) i_tau
    | Int.Glob gloc when Loc.equal String.equal gloc (Loc.put loc id) -> []
    | _ -> raise (InvalidQITConstructor e_tau)
  in
  let rec destruct_pis = function
    | Int.Pi (arg, i_tau) ->
        let args, idxs = destruct_pis i_tau in
        (arg :: args, idxs)
    | Int.App _ as i_tau  -> ([], destruct_apps [] i_tau)
    | _                   -> raise (InvalidQITConstructor e_tau)
  in
  (id, destruct_pis (elab_tm cctx vctx e_tau))

let elab_quotient (cctx : constr_ctx) (vctx : var_ctx) :
    Ext.quotient_inductive_entry_def -> string * Int.quotient =
 fun (QuotIndEntryDef (_, id, e_tau)) ->
  let rec destruct_tau = function
    | Int.Pi (arg, i_tau)       ->
        let args, lhs, rhs = destruct_tau i_tau in
        (arg :: args, lhs, rhs)
    | Int.Eq { tm_ltm; tm_rtm } -> ([], tm_ltm, tm_rtm)
    | _                         -> raise (InvalidQITQuotient e_tau)
  in
  let qit_args, qit_lhs, qit_rhs = destruct_tau (elab_tm cctx vctx e_tau) in
  (id, Int.{ qit_args; qit_lhs; qit_rhs })

let elab_qit_def (cctx : constr_ctx) (vctx : var_ctx) :
    Ext.quotient_inductive_def -> Int.qit_def =
 fun (Ext.QuotIndDef (loc, id, e_idxs, e_kappa, e_cstrs, e_quots)) ->
  let rec destruct_kappa = function
    | Int.Pi (idxed, i_tau) ->
        let idxeds, lv = destruct_kappa i_tau in
        (idxed :: idxeds, lv)
    | Int.U (lv, _)         -> ([], lv)
    | _                     -> raise (InvalidQITKind e_kappa)
  in
  let f vctx (id, e_t) = (vctx_add vctx id, elab_tm cctx vctx e_t) in
  let vctx, i_idxs = List.fold_map ~f ~init:vctx e_idxs in
  let i_idxeds, lv = destruct_kappa (elab_tm cctx vctx e_kappa) in
  Int.
    {
      qit_name = Loc.put loc id;
      qit_index = i_idxs;
      qit_indexed = i_idxeds;
      qit_ret_lv = lv;
      qit_constr =
        List.map ~f:(elab_constructor cctx vctx) e_cstrs
        |> Map.of_alist_exn (module String);
      qit_quot =
        List.map ~f:(elab_quotient cctx vctx) e_quots
        |> Map.of_alist_exn (module String);
    }

let build_constr_ctx : Ext.quotient_inductive_def list -> constr_ctx =
  let f ctx (Ext.QuotIndDef (_, id, _, _, e_cstrs, e_quots)) =
    let extend_with m f d =
      let combine ~key v0 v1 = raise (DuplicatedConstrIds (key, (v0, v1))) in
      d
      |> List.map ~f:(fun (Ext.QuotIndEntryDef (_, x, _)) -> (x, f id))
      |> Map.of_alist_exn (module String)
      |> Map.merge_skewed m ~combine
    in
    let ctx = extend_with ctx Either.first e_cstrs in
    let ctx = extend_with ctx Either.second e_quots in
    ctx
  in
  List.fold_left ~f ~init:(Map.empty (module String))

let build_var_ctx (e_fds : Ext.fun_def list)
    (e_qis : Ext.quotient_inductive_def list) : var_ctx =
  let f vctx (Ext.FunDef (_, id, _, _)) =
    Map.add_exn vctx ~key:id ~data:[ None ]
  in
  let vctx = List.fold_left ~f ~init:(Map.empty (module String)) e_fds in
  let f vctx (Ext.QuotIndDef (_, id, _, _, _, _)) =
    Map.add_exn vctx ~key:id ~data:[ None ]
  in
  List.fold_left ~f ~init:vctx e_qis

let elab_module_def (Ext.ModDef stmts) : Int.module_def =
  let separator = function
    | Ext.TopFunDef t  -> Either.First t
    | Ext.TopQuotInd t -> Either.Second t
  in
  let e_fds, e_qis = List.partition_map ~f:separator stmts in
  let cctx = build_constr_ctx e_qis in
  let vctx = build_var_ctx e_fds e_qis in
  let i_qis = List.map ~f:(elab_qit_def cctx vctx) e_qis in
  let i_fds = List.map ~f:(elab_fun_def cctx vctx) e_fds in
  Int.{ fun_defs = i_fds; qit_defs = i_qis }
