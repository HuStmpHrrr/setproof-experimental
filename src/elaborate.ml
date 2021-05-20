open Lib

module Ext = Ext_ast
module Int = Ast

type constr_entry = (string, string) Either.t
type constr_ctx = constr_entry StrM.t
type var_entry = int option
type var_ctx = var_entry list StrM.t
type ctx = constr_ctx * var_ctx

exception DuplicatedConstrIds of string * (constr_entry * constr_entry)
exception UnknownConstrId of string * loc
exception UnknownVarId of string * loc
exception InvalidQITKind of string * Ext.ty
exception InvalidQITQuotient of string * Ext.ty
exception InvalidQITConstructor of string * Ext.ty

let vctx_shiftn n = Map.map ~f:(List.map ~f:(Option.map ~f:(( + ) n)))
let vctx_shift1 = vctx_shiftn 1

let vctx_add_local vctx id =
  Map.add_multi (vctx_shiftn 1 vctx) ~key:id ~data:(Some 0)
let vctx_add_global vctx id = Map.add_exn vctx ~key:id ~data:[ None ]

let rec elab_tm ((cctx, vctx) : ctx) : Ext.tm -> Int.tm = function
  | Ext.TmUniv (loc, lev) -> Int.U (lev, loc)
  | Ext.TmConstr (loc, id) -> (
      let open Option in
      let open Either in
      match Map.find cctx id with
      | Some (First tid)  -> Int.Constr (tid, Loc.put loc id)
      | Some (Second tid) -> Int.EqConstr (tid, Loc.put loc id)
      | None              -> raise (UnknownConstrId (id, loc))
    )
  | Ext.TmVar (loc, id) -> (
      let open Option in
      match Map.find vctx id >>= List.hd with
      | Some (Some idx) -> Int.Var (idx, Loc.put loc (Some id))
      | Some None       -> Int.Glob (Loc.put loc id)
      | None            -> raise (UnknownVarId (id, loc))
    )
  | Ext.TmLam (loc, id, e_tau, e_t) ->
      let vctx' = vctx_add_local vctx id in
      Int.Lam (elab_tm (cctx, vctx) e_tau, elab_tm (cctx, vctx') e_t, loc)
  | Ext.TmPi (_, id, e_tau0, e_tau1) ->
      let vctx' = vctx_add_local vctx id in
      Int.Pi (elab_tm (cctx, vctx) e_tau0, elab_tm (cctx, vctx') e_tau1)
  | Ext.TmMatch (loc, e_scr, e_cstr_bs, e_quot_bs) ->
      Int.Case
        ( elab_tm (cctx, vctx) e_scr,
          List.map ~f:(elab_branch (cctx, vctx)) e_cstr_bs,
          List.map ~f:(elab_branch (cctx, vctx)) e_quot_bs,
          loc
        )
  | Ext.TmApp (_, e_f, e_a) ->
      Int.App (elab_tm (cctx, vctx) e_f, elab_tm (cctx, vctx) e_a)
  | Ext.TmEq (_, e_lhs, e_rhs) ->
      Int.Eq
        {
          tm_ltm = elab_tm (cctx, vctx) e_lhs;
          tm_rtm = elab_tm (cctx, vctx) e_rhs;
        }
  | Ext.TmRefl (loc, e_t) -> Int.Refl (elab_tm (cctx, vctx) e_t, loc)

and elab_branch ((cctx, vctx) : ctx) : Ext.branch -> Int.pattern * Int.tm =
 fun (e_p, e_t) ->
  let vctx, i_p = elab_pattern (cctx, vctx) e_p in
  (i_p, elab_tm (cctx, vctx) e_t)

and elab_pattern ((cctx, vctx) : ctx) : Ext.pattern -> var_ctx * Int.pattern =
  function
  | Ext.PatVar (loc, id)       ->
      if String.equal id "_"
      then (vctx_shift1 vctx, Int.PVar (Loc.put loc None))
      else (vctx_add_local vctx id, Int.PVar (Loc.put loc (Some id)))
  | Ext.PatInd (loc, id, e_ps) ->
      let tid =
        let open Option in
        match Map.find cctx id with
        | Some (First tid)  -> tid
        | Some (Second tid) -> tid
        | None              -> raise (UnknownConstrId (id, loc))
      in
      let i_ps = e_ps |> List.map ~f:(fun c -> Some c) |> List.rev in
      ( vctx,
        Int.PInd
          { tm_ind_name = tid; tm_constr = Loc.put loc id; tm_args = i_ps }
      )
  | Ext.PatEq (loc, id)        -> (vctx, Int.PEq (Loc.put loc (Some id)))

let elab_fun_def ((cctx, vctx) : ctx) : Ext.fun_def -> var_ctx * Int.fun_def =
 fun (Ext.FunDef (loc, id, e_tau, e_t)) ->
  let fun_name = Loc.put loc id in
  let fun_type = elab_tm (cctx, vctx) e_tau in
  let vctx = vctx_add_global vctx id in
  let fun_body = elab_tm (cctx, vctx) e_t in
  (vctx, Int.{ fun_name; fun_type; fun_body })

let elab_constructor ((cctx, vctx) : ctx) (qid_name : string) :
    Ext.quotient_inductive_entry_def ->
    constr_ctx * (string * (Int.telescope * Int.tm list)) =
 fun (QuotIndEntryDef (_, id, e_tau)) ->
  let rec destruct_apps acc = function
    | Int.App (i_tau, idx) -> destruct_apps (idx :: acc) i_tau
    | Int.Glob gloc when String.equal (loc_data gloc) qid_name -> []
    | _ -> raise (InvalidQITConstructor (id, e_tau))
  in
  let rec destruct_pis = function
    | Int.Pi (arg, i_tau) ->
        let args, idxs = destruct_pis i_tau in
        (arg :: args, idxs)
    | Int.App _ as i_tau  -> ([], destruct_apps [] i_tau)
    | Int.Glob _ as i_tau -> ([], destruct_apps [] i_tau)
    | _                   -> raise (InvalidQITConstructor (id, e_tau))
  in
  let args, idxs = destruct_pis (elab_tm (cctx, vctx) e_tau) in
  ( Map.add_exn cctx ~key:id ~data:(Either.First qid_name),
    (id, (List.rev args, List.rev idxs))
  )

let elab_quotient ((cctx, vctx) : ctx) (qid_name : string) :
    Ext.quotient_inductive_entry_def -> constr_ctx * (string * Int.quotient) =
 fun (QuotIndEntryDef (_, id, e_tau)) ->
  let rec destruct_tau = function
    | Int.Pi (arg, i_tau)       ->
        let args, lhs, rhs = destruct_tau i_tau in
        (arg :: args, lhs, rhs)
    | Int.Eq { tm_ltm; tm_rtm } -> ([], tm_ltm, tm_rtm)
    | _                         -> raise (InvalidQITQuotient (id, e_tau))
  in
  let qit_args, qit_lhs, qit_rhs = destruct_tau (elab_tm (cctx, vctx) e_tau) in
  ( Map.add_exn cctx ~key:id ~data:(Either.Second qid_name),
    (id, Int.{ qit_args = List.rev qit_args; qit_lhs; qit_rhs })
  )

let elab_qit_def ((cctx, vctx) : ctx) :
    Ext.quotient_inductive_def -> ctx * Int.qit_def =
 fun (Ext.QuotIndDef e_quot) ->
  let rec destruct_kappa idxeds = function
    | Int.Pi (idxed, i_tau) -> destruct_kappa (idxed :: idxeds) i_tau
    | Int.U (lv, _)         -> (lv, idxeds)
    | _                     ->
        raise (InvalidQITKind (e_quot.quot_id, e_quot.quot_kind))
  in
  let elab_idx vctx (id, e_t) =
    (vctx_add_local vctx id, elab_tm (cctx, vctx) e_t)
  in
  let qit_name = Loc.put e_quot.quot_loc e_quot.quot_id in
  let local_vctx, qit_index =
    List.fold_map ~f:elab_idx ~init:vctx e_quot.quot_indices
    |> Tuple2.map2 ~f:List.rev
  in
  let qit_ret_lv, qit_indexed =
    elab_tm (cctx, local_vctx) e_quot.quot_kind |> destruct_kappa []
  in
  let local_vctx = vctx_add_global local_vctx e_quot.quot_id in
  let folder_with f cctx = f (cctx, local_vctx) e_quot.quot_id in
  let cctx, qit_constr =
    List.fold_map
      ~f:(folder_with elab_constructor)
      ~init:cctx e_quot.quot_constrs
    |> Tuple2.map2 ~f:(Map.of_alist_exn (module String))
  in
  let cctx, qit_quot =
    List.fold_map ~f:(folder_with elab_quotient) ~init:cctx e_quot.quot_constrs
    |> Tuple2.map2 ~f:(Map.of_alist_exn (module String))
  in
  ( (cctx, vctx_add_global vctx e_quot.quot_id),
    Int.{ qit_name; qit_index; qit_indexed; qit_ret_lv; qit_constr; qit_quot }
  )

let elab_module_def (Ext.ModDef stmts) : Int.module_def =
  let f ctx = function
    | Ext.TopFunDef e_t  ->
        let var_ctx, i_t = elab_fun_def ctx e_t in
        ((fst ctx, var_ctx), Int.Fun i_t)
    | Ext.TopQuotInd e_t ->
        let ctx, i_t = elab_qit_def ctx e_t in
        (ctx, Int.Qit i_t)
  in
  let init = (Map.empty (module String), Map.empty (module String)) in
  stmts |> List.fold_map ~f ~init |> snd
