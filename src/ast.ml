(* Untyped AST. need to convert AST to Typed AST *)

open Lib

type pattern =
  | PInd of {
      tm_ind_name : string;
      tm_constr : string location;
      tm_args : string option list;  (** similar to telescope, in reverse order *)
    }
  | PEq  of string option location
     (** wildcard is None, otherwise it's Some *)
  | PVar of string option location

type tm =
  | U        of int * loc  (** universe, with nat level *)
  | Glob     of string location  (** a global reference to some definition *)
  | Var      of int * string option location
      (** variable with de Bruijn index. remember string name (None when wildcard) and location *)
  (* we then look into type definitions *)
  (* G |- A : U    G, x : A |- B : U
   * --------------------------------
   * G |- Pi A B : U
   *)
  | Pi       of ty * ty
  (* G |- a : A   G |- b : B  G |- A : Ui G |- B : Ui
   * ------------------------------------------------
   * G |- a = b : Ui
   *)
  | Eq       of {
      tm_ltm : tm;
      tm_rtm : tm;
    }
  (* next we look into terms *)
  | Lam      of ty * tm * loc  (** the location is for the lambda header *)
  | App      of tm * tm
  | Constr   of string * string location
      (** name    of the inductive type + the name of constructor
       * we must make sure the inductive type and the constructor exist
       *)
  | EqConstr of string * string location
      (** Similarly, a constructor for equality *)
  | Case     of tm * (pattern * tm) list * (pattern * tm) list * loc
      (** scrutinee, patterns for constructors, and patterns for quotients. *)
  | Refl     of tm * loc  (** location for the refl header *)

and ty = tm

type fun_def = {
  fun_name : string location;
  fun_type : ty;
  fun_body : tm;
}

(** a telescope is a reverse context, which is good for unification *)
type telescope = ty list

type qit_def = {
  qit_name : string location;  (** definition name and location *)
  qit_index : telescope;  (** a telescope for the indices *)
  qit_indexed : telescope;  (** a telescope for the argument *)
  qit_ret_lv : int;
      (** the level of universe in which the inductive definition reside *)
  qit_constr : (telescope * tm list) StrM.t;
      (** a telescope for the argument + a list of terms to apply to the inductive type *)
  qit_quot : quotient StrM.t;
}

and quotient = {
  qit_args : telescope;
  qit_lhs : tm;
  qit_rhs : tm;
}

type def =
  | Fun of fun_def
  | Qit of qit_def

type module_def = def list

(** location info for a term *)
let rec tm_loc t : loc =
  match t with
  | U (_, l) -> l
  | Glob n -> loc_erase n
  | Var (_, n) -> loc_erase n
  | Pi (a, b) -> loc_combine (tm_loc a) (tm_loc b)
  | Eq eq -> loc_combine (tm_loc eq.tm_ltm) (tm_loc eq.tm_rtm)
  | Lam (_, t, l) -> loc_combine l (tm_loc t)
  | App (l, r) -> loc_combine (tm_loc l) (tm_loc r)
  | Constr (_, n)
  | EqConstr (_, n) ->
      loc_erase n
  | Case (_, _, _, l) -> l
  | Refl (t, l) -> loc_combine l (tm_loc t)
