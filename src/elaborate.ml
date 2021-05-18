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
  | Ext.TmLam (loc, id, tau, t) ->
      let vctx' = vctx_add vctx id in
      Int.Lam (elab_tm cctx vctx tau, elab_tm cctx vctx' t, loc)
  | Ext.TmPi (_, id, tau0, tau1) ->
      let vctx' = vctx_add vctx id in
      Int.Pi (elab_tm cctx vctx tau0, elab_tm cctx vctx' tau1)
  | Ext.TmMatch (loc, scr, cstr_bs, quot_bs) ->
      Int.Case
        ( elab_tm cctx vctx scr,
          List.map ~f:(elab_branch cctx vctx) cstr_bs,
          List.map ~f:(elab_branch cctx vctx) quot_bs,
          loc )
  | Ext.TmApp (_, f, a) -> Int.App (elab_tm cctx vctx f, elab_tm cctx vctx a)
  | Ext.TmEq (_, lhs, rhs) ->
      Int.Eq { tm_ltm = elab_tm cctx vctx lhs; tm_rtm = elab_tm cctx vctx rhs }
  | Ext.TmRefl (loc, t) -> Int.Refl (elab_tm cctx vctx t, loc)

and elab_branch (cctx : constr_ctx) (vctx : var_ctx) :
    Ext.branch -> Int.pattern * Int.tm =
 fun (p, t) ->
  let vctx, p = elab_pattern cctx vctx p in
  (p, elab_tm cctx vctx t)

and elab_pattern (cctx : constr_ctx) (vctx : var_ctx) :
    Ext.pattern -> var_ctx * Int.pattern = function
  | Ext.PatWildcard loc      -> (vctx_shift1 vctx, Int.PVar (Loc.put loc None))
  | Ext.PatVar (loc, id)     ->
      (vctx_add vctx id, Int.PVar (Loc.put loc (Some id)))
  | Ext.PatInd (loc, id, ps) ->
      let tid =
        let open Option in
        match Map.find cctx id with
        | Some (First tid)  -> tid
        | Some (Second tid) -> tid
        | None              -> raise (UnknownConstrId (id, loc))
      in
      let vctx, ps = List.fold_map ~f:(elab_pattern cctx) ~init:vctx ps in
      ( vctx,
        Int.PCase
          (Int.IndCase
             { tm_ind_name = tid; tm_constr = Loc.put loc id; tm_args = ps }) )
  | Ext.PatEq (_, p)         ->
      let vctx, p = elab_pattern cctx vctx p in
      (vctx, Int.PCase (Int.EqCase p))

let elab_fun_def (cctx : constr_ctx) (vctx : var_ctx) :
    Ext.fun_def -> Int.fun_def =
 fun (Ext.FunDef (loc, id, tau, t)) ->
  Int.
    {
      fun_name = Loc.put loc id;
      fun_type = elab_tm cctx vctx tau;
      fun_body = elab_tm cctx vctx t;
    }

let elab_constructor :
    Ext.quotient_inductive_entry_def -> string * Int.telescope * Int.tm list =
  raise NotImplemented

let elab_quotient : Ext.quotient_inductive_entry_def -> string * Int.quotient =
  raise NotImplemented

let elab_qit_def : Ext.quotient_inductive_def -> Int.qit_def =
  raise NotImplemented

let build_constr_ctx : Int.qit_def list -> constr_ctx =
  let open Int in
  let f ctx qi =
    let extend_with m f d =
      let combine ~key v0 v1 = raise (DuplicatedConstrIds (key, (v0, v1))) in
      Map.keys d
      |> List.map ~f:(fun x -> (x, f (loc_data qi.qit_name)))
      |> Map.of_alist_exn (module String)
      |> Map.merge_skewed m ~combine
    in
    let ctx = extend_with ctx Either.first qi.qit_constr in
    let ctx = extend_with ctx Either.second qi.qit_quot in
    ctx
  in
  List.fold_left ~f ~init:(Map.empty (module String))

let build_var_ctx (e_fds : Ext.fun_def list) (i_qis : Int.qit_def list) :
    var_ctx =
  let open Int in
  let f vctx (Ext.FunDef (_, id, _, _)) =
    Map.add_exn vctx ~key:id ~data:[ None ]
  in
  let vctx = List.fold_left ~f ~init:(Map.empty (module String)) e_fds in
  let f vctx { qit_name; _ } =
    Map.add_exn vctx ~key:(loc_data qit_name) ~data:[ None ]
  in
  List.fold_left ~f ~init:vctx i_qis

let elab_module_def (Ext.ModDef stmts) : Int.module_def =
  let separator = function
    | Ext.TopFunDef t  -> Either.First t
    | Ext.TopQuotInd t -> Either.Second t
  in
  let e_fds, e_qis = List.partition_map ~f:separator stmts in
  let i_qis = List.map ~f:elab_qit_def e_qis in
  let cctx = build_constr_ctx i_qis in
  let vctx = build_var_ctx e_fds i_qis in
  let i_fds = List.map ~f:(elab_fun_def cctx vctx) e_fds in
  Int.{ fun_defs = i_fds; qit_defs = i_qis }
