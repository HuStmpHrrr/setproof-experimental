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
  | Pi of int * ty * ty         (* carry the universe level it lives in *)
  | Eq of {
      tm_eq_lv : int;           (* its universe level *)
      tm_lty   : ty;
      tm_rty   : ty;
      tm_ltm   : tm;
      tm_rtm   : tm;
    }
  | Lam of ty * tm * loc
  | App of tm * tm
  | Constr   of string * string location
  | EqConstr of string * string location
  | Case     of tm * (case * tm) list * loc
  | Refl     of int * tm * loc  (* location for the refl header *)
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
type globenv  = (globdef * loc) StrM.t
type localenv = ty list

type env = {
    glob  : globenv;
    (* this one is CONTEXT, not telescope *)
    local : localenv;
  }

(* whether a QIT definition is quotiented? if so, then it has no injectivity *)
let is_quotiented (d : qit_def) : bool =
  not (Map.is_empty d.qit_quot)
