open Lib

type identifier = string

(** Terms *)
type tm =
  | TmUniv   of loc * int
  | TmConstr of loc * identifier
  | TmVar    of loc * identifier
  | TmLam    of loc * identifier * ty * tm
  | TmPi     of loc * identifier * ty * ty
  | TmMatch  of
      loc
      * tm                                 (* scrutinee *)
      * branch list                        (* constructor branches *)
      * branch list                        (* quotient branches *)
  | TmApp    of loc * tm * tm
  | TmEq     of loc * tm * tm
  | TmRefl   of loc * tm

and ty = tm
(** Types *)

and branch = pattern * tm
(** Match branches *)

(** Match patterns *)
and pattern =
  | PatWildcard of loc
  | PatVar      of loc * identifier
  | PatInd      of loc * identifier * pattern list
  | PatEq       of loc * pattern

(** definition *)
type fun_def = FunDef of loc * identifier * ty * tm

(** Quotient inductive type constructor/quotient *)
type quotient_inductive_entry_def =
  QuotIndEntryDef of
    loc
    * identifier     (* quotient inductive type entry name *)
    * ty             (* quotient inductive type entry type *)

(** Quotient inductive type declaration *)
type quotient_inductive_def =
  QuotIndDef of
    loc
    * identifier                         (* type name *)
    * (identifier * ty option) list      (* index names and kinds *)
    * ty                                 (* kind *)
    * quotient_inductive_entry_def list (* constructors *)
    * quotient_inductive_entry_def list (* quotients *)

(** Top statements *)
type top_statement =
  | TopFunDef  of fun_def
  | TopQuotInd of quotient_inductive_def

(** Module definition *)
type module_def = ModDef of top_statement list
