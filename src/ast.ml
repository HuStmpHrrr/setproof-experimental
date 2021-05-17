open Lib

type tm =
  | U of int * loc              (* universe, with nat level *)
  (* variable with de Bruijn index. remember string name (None when wildcard) and location *)
  | Var of int * (string option) location
  (* we then look into type definitions *)
  (* G |- A : U    G, x : A |- B : U
   * --------------------------------
   * G |- Pi A B : U
   *)
  | Pi of ty * ty
  | Ind of string location      (* (quotient) inductive family with a name *)
  (* G |- a : A   G |- b : B
   * -----------------------
   * G |- a = b : U
   *)
  | Eq of {
      tm_ltm : tm;
      tm_rtm : tm;
    }
  (* next we look into terms *)
  | Lam of tm * loc             (* the location is for the lambda header *)
  | App of tm * tm
  (* name of the inductive type + the name of constructor
   * we must make sure the inductive type and the constructor exist
   *)
  | Constr of string * string location
  (* Similarly, a constructor for equality *)
  | EqConstr of string * string location
  | Case of tm * (case * tm) list * loc
  | Refl of tm * loc            (* location for the refl header *)
and ty = tm
and case =
  | IndCase of {
      tm_ind_name : string;
      tm_constr   : string location;
      (* similar to telescope, in reverse order *)
      tm_args     : pattern list;
    }
  | EqCase of (string option) location
and pattern =
  | PVar of (string option) location
  | PCase of case

(* a telescope is a reverse context, which is good for unification *)
type telescope = ty list

type qit_def = {
    qit_def_loc : loc;          (* definition location *)
    qit_index   : telescope;     (* a telescope for the indices *)
    qit_indexed : telescope;     (* a telescope for the argument *)
    qit_ret_lv  : int;           (* the level of universe in which the inductive definition reside *)
    qit_constr  : (telescope * tm list) StrM.t; (* a telescope for the argument + a list of terms to apply to the inductive type *)
    qit_quot    : quotient StrM.t
  }
and quotient = {
    qit_args : telescope;
    qit_lhs  : tm;
    qit_rhs  : tm;
  }

let rec telescope_to_pi ts rt : ty =
  match ts with
  | [] -> rt
  | t :: ts' -> Pi (t, telescope_to_pi ts' rt)

let rec tm_loc t : loc =
  match t with
  | U (_, l)          -> l
  | Var (_, n)        -> loc_erase n
  | Pi (a, b)         -> loc_combine (tm_loc a) (tm_loc b)
  | Ind n             -> loc_erase n
  | Eq eq             -> loc_combine (tm_loc eq.tm_ltm) (tm_loc eq.tm_rtm)
  | Lam (t, l)        -> loc_combine l (tm_loc t)
  | App (l, r)        -> loc_combine (tm_loc l) (tm_loc r)
  | Constr (_, n)
    | EqConstr (_, n) -> loc_erase n
  | Case (_, _, l)    -> l
  | Refl (t, l)       -> loc_combine l (tm_loc t)