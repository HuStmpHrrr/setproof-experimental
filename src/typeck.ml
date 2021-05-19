open Lib

module A = Ast
module T = Tast

exception VariableNotFound of string location
exception TypeExpected of T.tm
exception EqDiffLevel of T.ty * int * T.ty * int
exception ExpectPi of T.ty * loc

exception NotConvertible of T.tm * T.tm * loc

let whnf_red (_g : T.env) (_t : T.tm) : T.tm = raise NotImplemented

let check_is_ty (g : T.env) (t : T.tm) : int =
  match whnf_red g t with
  | T.U (i, _) -> i
  | _          -> raise (TypeExpected t)

let check_convertible_exn (_g : T.env) (_s : T.tm) (_t : T.tm) : unit =
  raise NotImplemented

let check_convertible (g : T.env) (s : T.tm) (t : T.tm) : bool =
  try
    check_convertible_exn g s t;
    true
  with
  | NotConvertible _ -> false

(** get the type of a typed term.  *)
let rec get_ty (g : T.env) (t : T.tm) : T.ty =
  match t with
  | T.U (i, _)              -> T.U (i + 1, loc_dummy)
  | T.Glob n                ->
      let _, tp, _ = T.env_glookup g (loc_data n) in
      tp
  | T.Var (x, _)            -> T.env_llookup_ty g x
  | T.Pi (a, b)             ->
      let ta = get_ty g a
      and tb = get_ty (T.env_linsert g a) b in
      let ia = check_is_ty g ta
      and ib = check_is_ty g tb in
      T.U (Int.max ia ib, loc_dummy)
  | T.Eq e                  -> T.U (check_is_ty g (get_ty g e.tm_lty), loc_dummy)
  | T.Lam (a, t, _)         ->
      let g' = T.env_linsert g a in
      let tt = get_ty g' t in
      T.Pi (a, tt)
  | T.App (s, t)            -> (
      let st = get_ty g s in
      match whnf_red g st with
      | Pi (_, b) -> T.subst b t
      | _         -> raise Impossible
    )
  | T.Constr (qn, n)        -> T.get_constr_ty g qn n
  | T.EqConstr (qn, n)      -> T.get_eqconstr_ty g qn n
  | T.Case (tp, _, _, _, _) -> tp
  | T.Refl (t, _)           ->
      let tt = get_ty g t in
      T.Eq { tm_lty = tt; tm_rty = tt; tm_ltm = t; tm_rtm = t }

(** synthesize a type from untyped AST based on a typing environment
 * to a typed term and its (typed) type
 *)
let rec type_syn (g : T.env) (t : A.tm) : T.tm * T.ty =
  match t with
  | A.U (i, l) -> (T.U (i, l), T.U (i + 1, loc_dummy))
  | A.Glob n -> (
      match T.env_glookup_opt g (loc_data n) with
      | None            -> raise (VariableNotFound n)
      | Some (_, tp, _) -> (T.Glob n, tp)
    )
  | A.Var (x, n) -> (
      match T.env_llookup_ty_opt g x with
      | None    ->
          raise (VariableNotFound (Loc.map n (Option.value ~default:"_")))
      | Some tp -> (T.Var (x, n), tp)
    )
  | A.Pi (a, b) ->
      let a', ta = type_syn g a in
      let b', tb = type_syn (T.env_linsert g a') b in
      let ia = check_is_ty g ta
      and ib = check_is_ty g tb in
      (T.Pi (a', b'), T.U (Int.max ia ib, loc_dummy))
  | A.Eq e ->
      let l, lt = type_syn g e.tm_ltm in
      let r, rt = type_syn g e.tm_rtm in
      let il = check_is_ty g lt
      and ir = check_is_ty g rt in
      (* it could look strange, but we only do equality between types with equal level *)
      if Int.(il <> ir)
      then raise (EqDiffLevel (lt, il, rt, ir))
      else
        ( T.Eq { tm_lty = lt; tm_rty = rt; tm_ltm = l; tm_rtm = r },
          T.U (il, loc_dummy)
        )
  | A.Lam (a, t, loc) ->
      let a', _ = type_syn g a in
      ignore (check_is_ty g a');
      let g' = T.env_linsert g a' in
      let t', _ = type_syn g' t in
      (T.Lam (a', t', loc), T.Pi (a', t'))
  | A.App (s, t) -> (
      let s', st = type_syn g s
      and t', tt = type_syn g t in
      match whnf_red g st with
      | Pi (a, b) ->
          check_convertible_exn g tt a;
          (T.App (s', t'), T.subst b t')
      | tp        -> raise (ExpectPi (tp, A.tm_loc s))
    )
  | A.Constr (qn, n) -> (T.Constr (qn, n), T.get_constr_ty g qn n)
  | A.EqConstr (qn, n) -> (T.EqConstr (qn, n), T.get_eqconstr_ty g qn n)
  | A.Case (_scr, _cs, _qs, _l) -> raise NotImplemented
  | A.Refl (t, loc) ->
      let t', tt = type_syn g t in
      ( T.Refl (t', loc),
        T.Eq { tm_lty = tt; tm_rty = tt; tm_ltm = t'; tm_rtm = t' }
      )

and type_check (g : T.env) (e : A.tm) (et : T.ty) : T.tm =
  match e with
  | A.Case (s, _cps, _qps, loc) ->
      let s', st = type_syn g s in
      let cps' =
        raise NotImplemented
        (* TODO: Implement constructor branches checkings *)
      in
      let qps' =
        raise NotImplemented
        (* TODO: Implement quotient branches checkings *)
      in
      T.Case (s', st, cps', qps', loc)
  | _ ->
      let e', et' = type_syn g e in
      check_convertible_exn g et' et;
      e'

and constr_case_check (g : T.env) ((p, e) : A.pattern * A.tm)
    ((pt, et) : T.ty * T.ty) : T.pattern =
  raise NotImplemented
