open Lib

type identifier = string

(** Terms *)
type tm =
  | TmUniv   of loc * int
  | TmConstr of loc * identifier
  | TmVar    of loc * identifier
  | TmLam    of loc * identifier * ty * tm
  | TmPi     of loc * identifier * ty * ty
  | TmMatch  of loc * tm * branch list * branch list
      (** Match with scrutinee, constructor branches, and quotient branches *)
  | TmApp    of loc * tm * tm
  | TmEq     of loc * tm * tm
  | TmRefl   of loc * tm

and ty = tm
(** Types *)

and branch = pattern * tm
(** Match branches *)

(** Match patterns *)
and pattern =
  | PatVar      of loc * identifier
  | PatInd      of loc * identifier * pattern list
  | PatEq       of loc * pattern

(** definition *)
type fun_def = FunDef of loc * identifier * ty * tm

(** Quotient inductive type constructor/quotient *)
type quotient_inductive_entry_def =
  | QuotIndEntryDef of loc * identifier * ty  (** Entry with name and type *)

(** Quotient inductive type declaration *)
type quotient_inductive_def =
  | QuotIndDef of {
      quot_loc : loc;
      quot_id : identifier;
      quot_indices : (identifier * ty) list;  (** index names and kinds *)
      quot_kind : ty;
      quot_constrs : quotient_inductive_entry_def list;
      quot_quotients : quotient_inductive_entry_def list;
    }

(** Top statements *)
type top_statement =
  | TopFunDef  of fun_def
  | TopQuotInd of quotient_inductive_def

(** Module definition *)
type module_def = ModDef of top_statement list
