open Lib

type identifier = string

(** Terms *)
type tm =
  | TmVar   of loc * identifier
  | TmLam   of loc * identifier * ty * tm
  | TmPi    of loc * identifier * ty * ty
  | TmMatch of loc * tm * branch list
  | TmApp   of loc * tm * tm
  | TmEq    of loc * tm * tm
  | TmRefl  of loc * tm

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

(** Quotient inductive type constructor/quotient declaration *)
type quotient_inductive_entry_decl =
  | QuotIndEntryDecl of
      loc
      * identifier      (* quotient inductive type entry name *)
      * ty              (* quotient inductive type entry type *)

(** Quotient inductive type declaration *)
type quotient_inductive_decl =
  | QuotIndDecl of
      loc
      * identifier                         (* type name *)
      * ty list                            (* indices *)
      * ty                                 (* kind *)
      * quotient_inductive_entry_decl list

(** definition *)
type def =
  | Def of loc * identifier * ty * tm

(** Top statements *)
type top_statement =
  | TopQuotInd of quotient_inductive_decl
  | TopDef     of def

(** Module definition *)
type module_def = ModDef of top_statement list
