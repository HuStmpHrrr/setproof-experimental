(* typed AST. AST is converted to typed AST after type checking *)

open Lib

module A = Ast

type case =
  | IndCase of {
      tm_ind_name : string;
      tm_constr   : string location;
      tm_args     : pattern list;
    }
  | EqCase of pattern
and pattern =
  | PVar of (string option) location
  | PCase of case

type tm =
  | U of int * loc
  | Glob of string location
  | Var of int * (string option) location
  | Pi of ty * ty         (* carry the universe level it lives in *)
  | Eq of {
      tm_lty   : ty;
      tm_rty   : ty;
      tm_ltm   : tm;
      tm_rtm   : tm;
    }
  | Lam of ty * tm * loc
  | App of tm * tm
  | Constr   of string * string location
  | EqConstr of string * string location
  | Case     of ty * tm * (case * tm) list * loc
  | Refl     of tm * loc  (* location for the refl header *)
and ty = tm

type telescope = ty list

type qit_def = {
    qit_name    : string location;
    qit_index   : telescope;
    qit_indexed : telescope;
    qit_ret_lv  : int;
    qit_constr  : (telescope * tm list) StrM.t;
    qit_quot    : quotient StrM.t
  }
and quotient = {
    qit_args : telescope;
    qit_lty  : ty;
    qit_rty  : ty;
    qit_lhs  : tm;
    qit_rhs  : tm;
  }

(* DuplicatedDefinition (n1, n2) where n1 is the original definition and n2 is the conflicting definition *)
exception DuplicatedDefinition of string location * string location

(* various kinds of global definitions *)
type globdef =
  | DInd of qit_def                       (* an inductive definition *)
  | DConstr of string * string location   (* a constructor *)
  | DEqConstr of string * string location (* an equality constructor *)
  | DDecl of ty                           (* a global declaration (undefined) *)
  | DDef of ty * tm                       (* a global definition *)

(* for global definition, we use name based *)
type globenv  = (globdef * ty * loc) StrM.t
(* the type of variables and possibly it's value *)
type localenv = (ty * tm option) list

type env = {
    glob  : globenv;
    (* this one is CONTEXT, not telescope *)
    local : localenv;
  }

(** location info for a term *)
let rec tm_loc t : loc =
  match t with
  | U (_, l)          -> l
  | Glob n            -> loc_erase n
  | Var (_, n)        -> loc_erase n
  | Pi (a, b)         -> loc_combine (tm_loc a) (tm_loc b)
  | Eq eq             -> loc_combine (tm_loc eq.tm_ltm) (tm_loc eq.tm_rtm)
  | Lam (_, t, l)     -> loc_combine l (tm_loc t)
  | App (l, r)        -> loc_combine (tm_loc l) (tm_loc r)
  | Constr (_, n)
    | EqConstr (_, n) -> loc_erase n
  | Case (_, _, _, l) -> l
  | Refl (t, l)       -> loc_combine l (tm_loc t)

(** count number of vars in a case pattern *)
let rec case_vars c : int =
  match c with
  | IndCase ic -> List.sum (module Int) ic.tm_args ~f:pattern_vars
  | EqCase p   -> pattern_vars p
and pattern_vars p  : int =
  match p with
  | PVar _     -> 1
  | PCase c    -> case_vars c

(** shift_gen t by k if the de Bruijn index >= l *)
let rec shift_gen t k l : tm =
  match t with
  | U (_, _)
    | Glob _          -> t
  | Var (i, n)        ->
     if i >= l then Var (i + k, n) else t
  | Pi (a, b)         ->
     Pi (shift_gen a k l, shift_gen b k (1 + l))
  | Eq e              -> Eq {
                             tm_lty = shift_gen e.tm_lty k l;
                             tm_rty = shift_gen e.tm_rty k l;
                             tm_ltm = shift_gen e.tm_ltm k l;
                             tm_rtm = shift_gen e.tm_rtm k l;
                           }
  | Lam (a, t, loc)   -> Lam (shift_gen a k l, shift_gen t k (l + 1), loc)
  | App (t, s)        -> App (shift_gen t k l, shift_gen s k l)
  | Constr (_, _)
    | EqConstr (_, _) -> t
  | Case (a, t, cs, loc) -> Case (shift_gen a k l,
                                  shift_gen t k l,
                                  List.map cs ~f:(fun (c, t') -> (c, shift_gen t' k (l + case_vars c))),
                                  loc)
  | Refl (t, loc)     -> Refl (shift_gen t k l, loc)

(**
 * G |- t : T
 * ---------------------------------
 * G, D |- shift t |D| : shift T |D|
 *)
let shift t k : tm = shift_gen t k 0

(** substitute variables k in t for s shifted by k
 *
 * G, S, D |- t          : T   G |- s : S
 * -------------------------------------
 * G, D |- t [ s / |D| ] : T [ s / |D| ]
 *)
let rec subst_gen t k s  : tm =
  match t with
  | U (_, _)
    | Glob _             -> t
  | Var (i, _)           ->
     if Int.(i = k) then shift s k else t
  | Pi (a, b)            -> Pi (subst_gen a k s, subst_gen b (1 + k) s)
  | Eq e                 -> Eq {
                             tm_lty = subst_gen e.tm_lty k s;
                             tm_rty = subst_gen e.tm_rty k s;
                             tm_ltm = subst_gen e.tm_ltm k s;
                             tm_rtm = subst_gen e.tm_rtm k s;
                           }
  | Lam (a, t, loc)      -> Lam (subst_gen a k s, subst_gen t (1 + k) s, loc)
  | App (t, t')          -> App (subst_gen t k s, subst_gen t' k s)
  | Constr (_, _)
    | EqConstr (_, _)    -> t
  | Case (a, t, cs, loc) -> Case (subst_gen a k s,
                                  subst_gen t k s,
                                  List.map cs ~f:(fun (c, t') -> (c, subst_gen t' (k + case_vars c) s)),
                                  loc)
  | Refl (t, loc)        -> Refl (subst_gen t k s, loc)

let subst t s : tm = subst_gen t 0 s

let env_glookup_opt (g : env) (n : string) : (globdef * ty * loc) option =
  Map.find g.glob n

let env_llookup_ty_opt, env_llookup_tm_opt, env_llookup_ty_tm_opt =
  let env_lookup_opt (g : env) (x : int) : (ty * tm option) option =
    List.nth g.local x
  in
  let ty_opt (g : env) (x : int) : ty option =
    Option.map (env_lookup_opt g x) ~f:(fun (t, _) -> shift t (1 + x))
  and tm_opt (g : env) (x : int) : tm option option =
    Option.map (env_lookup_opt g x) ~f:(fun (_, ot) ->
                 Option.map ot ~f:(fun t -> shift t (1 + x)))
  and ty_tm_opt (g : env) (x : int) : (ty * tm option) option =
    Option.map (env_lookup_opt g x) ~f:(fun (t, ot) ->
                 shift t (1 + x),
                 Option.map ot ~f:(fun t -> shift t (1 + x)))
  in
  ty_opt, tm_opt, ty_tm_opt

let env_linsert (g : env) (t : ty) : env =
  { g with
    local = (t, None) :: g.local
  }

let env_linsert_v (g : env) (t : ty) (a : tm) : env =
  { g with
    local = (t, Some a) :: g.local
  }


(* invocations of functions in this module must make sure the definition exists *)
module ExnLookup = struct
  exception LookupException

  let env_glookup (g : env) (n : string) : globdef * ty * loc =
    match env_glookup_opt g n with
    | None     -> raise LookupException
    | Some tup -> tup

  let env_llookup_ty (g : env) (x : int) : ty =
    match env_llookup_ty_opt g x with
    | None     -> raise LookupException
    | Some t   -> t

  let env_llookup_tm (g : env) (x : int) : tm option =
    match env_llookup_tm_opt g x with
    | None     -> raise LookupException
    | Some t   -> t

  let env_llookup_ty_tm (g : env) (x : int) : ty * tm option =
    match env_llookup_ty_tm_opt g x with
    | None     -> raise LookupException
    | Some t   -> t

  let env_lookup_qit (g : env) (n : string) : qit_def =
    let gd, _, _ = env_glookup g n in
    match gd with
    | DInd qd -> qd
    | _ -> raise LookupException

end
include ExnLookup

module TmOps = struct

  let rec telescope_to_pi ts rt : ty =
    match ts with
    | []       -> rt
    | t :: ts' -> Pi (t, telescope_to_pi ts' rt)

  let rec iter_app t ts : tm =
    match ts with
    | [] -> t
    | t' :: ts' -> iter_app (App (t', t')) ts'

  (** whether a QIT definition is quotiented? if so, then it has no injectivity *)
  let is_quotiented (d : qit_def) : bool =
    not (Map.is_empty d.qit_quot)


  let qit_ty qd : ty =
    telescope_to_pi qd.qit_index (telescope_to_pi qd.qit_indexed (U (qd.qit_ret_lv, loc_dummy)))

  (** get the type of a constructor *)
  let get_constr_ty g qn n : ty =
    let qd = env_lookup_qit g qn in
    begin match Map.find qd.qit_constr (loc_data n) with
    | None -> raise LookupException
    | Some (tl, ts) -> telescope_to_pi tl (iter_app (Glob (loc_ghost qn)) ts)
    end

  let get_eqconstr_ty g qn n : ty =
    let qd = env_lookup_qit g qn in
    begin match Map.find qd.qit_quot (loc_data n) with
    | None -> raise LookupException
    | Some q -> telescope_to_pi q.qit_args (Eq {
                                                tm_lty = q.qit_lty;
                                                tm_rty = q.qit_rty;
                                                tm_ltm = q.qit_lhs;
                                                tm_rtm = q.qit_rhs
                                           })
    end

  let globdef_ty_gen g gd : ty =
    match gd with
    | DInd qd           -> qit_ty qd
    | DConstr (qn, n)   -> get_constr_ty g qn n
    | DEqConstr (qn, n) -> get_eqconstr_ty g qn n
    | DDecl t           -> t
    | DDef (t, _)       -> t

end

include TmOps
