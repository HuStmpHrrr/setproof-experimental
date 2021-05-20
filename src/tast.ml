(* typed AST. AST is converted to typed AST after type checking *)

open Lib

module A = Ast

type pattern =
  | PInd of {
      tm_ind_name : string;
      tm_constr   : string location;
      tm_args     : string option list;
    }
  | PEq  of string option location
  | PVar of string option location

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
  | Case     of ty * tm * (pattern * tm) list * (pattern * tm) list * loc
  | Refl     of tm * loc  (* location for the refl header *)
  | Subst    of tm * subst
and ty = tm
and subst =
  (**
   *       |D| = i
   * -------------------
   *  G,D |- Proj i : G
   *
   * notice that i can be negative
   *)
  | Proj of int
  (** G |- s : D   G |- t : S[s]   |D'| = i
   *  -------------------------------------
   *    G, D' |- Cons (s, t, i) : D, S
   *)
  | Cons of subst * tm * int

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
  | U (_, l)             -> l
  | Glob n               -> loc_erase n
  | Var (_, n)           -> loc_erase n
  | Pi (a, b)            -> loc_combine (tm_loc a) (tm_loc b)
  | Eq eq                -> loc_combine (tm_loc eq.tm_ltm) (tm_loc eq.tm_rtm)
  | Lam (_, t, l)        -> loc_combine l (tm_loc t)
  | App (l, r)           -> loc_combine (tm_loc l) (tm_loc r)
  | Constr (_, n)
    | EqConstr (_, n)    -> loc_erase n
  | Case (_, _, _, _, l) -> l
  | Refl (t, l)          -> loc_combine l (tm_loc t)
  | Subst (t, _)         -> tm_loc t

(** count number of vars in a case pattern *)
let pattern_vars c : int =
  match c with
  | PInd ic -> List.length ic.tm_args
  | PEq _   -> 1
  | PVar _  -> 1

(** substitution operations *)
module Subst = struct

  let id_subst = Proj 0

  let is_id_subst t : bool =
    match t with
    | Proj 0 -> true
    | _ -> false

  let cons s t : subst = Cons (s, t, 0)

  (** compute s1 . s2
   *  t[s1][s2] = t[s1 . s2]
   *
   * G1 |- s1 : G0    G2 |- s2 : G1
   * ------------------------------
   *   G2 |- compose s1 s2 : G0
   *
   *)
  let rec compose s1 s2 : subst =
    (* assume G |- t : A *)
    match s1 with
    | Proj i ->
       (* s1 = p^i *)
       (* returns p^f . s2 . p^b *)
       let rec helper s2 f b =
         match s2 with
         | Proj j           -> Proj (f + j + b)
         | Cons (s2', t, j) ->
            (* s2 = (s2', t) . p^j *)
            if f > 0 then
              (* p^f . (s2', t) . p^j . p^b = p^(f - 1) . s2' . p^(j + b)  *)
              helper s2' (f - 1) (j + b)
            else                (* f = 0, so p^f is identity *)
              Cons (s2', t, j + b)
       in
       helper s2 i 0
    | Cons (s1', t, i) ->
       (* s1 = (s1', t) . p^i *)
       (* returns (s1', t) . p^f . s2 . p^b *)
       let rec helper s2 f b =
         match s2 with
         | Proj j           -> Cons (s1', t, f + j + b)
         | Cons (s2', t, j) ->
            (* (s1', t) . p^f . (s2', t) . p^j . p^b *)
            if f > 0 then
              (* (s1', t) . p^(f - 1) . s2' . p^j . p^b *)
              helper s2' (f - 1) (j + b)
            else                (* f = 0 *)
              (* (s1', t) . (s2', t) . p^j . p^b = (s1' . (s2', t) , t[(s2', t)]) . p^(j + b) *)
              let s' = Cons (s2', t, 0) in
              Cons (compose s1' s', apply_subst t s', j + b)
       in
       helper s2 i 0

  and apply_subst t s : tm =
    if is_id_subst s then t
    else
      match t with
      | U (_, _)
        | Glob _      -> t
      | Var (x, n)    -> apply_subst_var x n s
      | Subst (t, s') -> Subst (t, compose s' s)
      | t             -> Subst (t, s)

  (** s : G -> D, x in D, then return x[s] : G |- A *)
  and apply_subst_var x n s : tm =
    match s with
    (* s : G, D -> G, x in G *)
    | Proj i -> Var (x + i, n)
    (* i : G, D -> G, s : G -> G', t : G |- A, x in G',A *)
    | Cons (s, t, i) ->
       if x = 0
       (* G', x : A *)
       then apply_subst t (Proj i)
       (* x in G' *)
       else apply_subst (apply_subst_var (x - 1) n s) (Proj i)

  (**
   *    s : G -> D   n = |G'|
   * ----------------------------
   * lift_n s n : (G, G'[s]) -> (D, G')
   *)
  let lift_n s n : subst =
    if n <= 0 then s
    else
      let rec repeat s m =
        if m >= 0 then
          (* TODO: fetch a more meaningful name *)
          repeat (cons s (Var (m, loc_ghost (Some ("x" ^ Int.to_string m))))) (m - 1)
        else s
      in
      repeat s (n - 1)

  let lift s : subst =
    lift_n s 1

  (**
   * G |- t : T
   * ---------------------------------
   * G, D |- shift t |D| : shift T |D|
   *)
  let shift t k : tm = apply_subst t (Proj k)

  (**
   * G, A |- t : T    G |- s : S
   * ---------------------------
   * G |- subst t s : shift T S
   *)
  let subst t s : tm = apply_subst t (Cons (id_subst, s, 0))

  (** push substitution inwards *)
  let rec push_subst t : tm =
    match t with
    | Subst (t, s)            -> elim_top_subst t s
    | _                       -> t

  (** eliminate top level Subst of t[s] *)
  and elim_top_subst t s : tm =
    match t with
    | U (_, _)
      | Glob _                 -> t
    | Var (x, n)               -> push_subst (apply_subst_var x n s)
    | Pi (a, b)                -> Pi (Subst (a, s), Subst (b, lift s))
    | Eq e                     -> Eq {
                                   tm_lty = Subst (e.tm_lty, s);
                                   tm_rty = Subst (e.tm_rty, s);
                                   tm_ltm = Subst (e.tm_ltm, s);
                                   tm_rtm = Subst (e.tm_rtm, s);
                                 }
    | Lam (a, t, l)            -> Lam (Subst (a, s), Subst (t, lift s), l)
    | App (t, t')              -> App (Subst (t, s), Subst (t', s))
    | Constr (_, _)
    | EqConstr (_, _)          -> t
    | Case (at, a, cs, eqs, l) -> Case (Subst (at, s),
                                        Subst (a, s),
                                        List.map cs ~f:(fun (p, t) -> p, Subst (t, lift_n s (pattern_vars p))),
                                        List.map eqs ~f:(fun (p, t) -> p, Subst (t, lift_n s (pattern_vars p))),
                                        l)
    | Refl (t, l)              -> Refl (Subst (t, s), l)
    | Subst (t, s')            -> elim_top_subst t (compose s' s)

end

include Subst

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
