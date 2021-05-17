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

(** Quotient inductive type constructor declaration *)
type constructor_decl =
  | CtrDecl of
      loc
      * identifier (* constructor name *)
      * ty list    (* constructor arguments *)
      * tm list    (* type arguments *)

(** Quotient inductive type quotient declaration *)
type quotient_decl =
  | QuotDecl of
      loc
      * identifier (* quotient name *)
      * ty list    (* arguments *)
      * tm         (* lhs *)
      * tm         (* rhs *)

(** Quotient inductive type declaration *)
type quotient_inductive_decl =
  | QuotIndDecl of
      loc
      * identifier            (* type name *)
      * ty list               (* indices *)
      * ty list               (* arguments *)
      * int                   (* level *)
      * constructor_decl list
      * quotient_decl list

type quotient_inductive_decls = quotient_inductive_decl list
(** (Mutually recursive) quotient inductive type declarations *)

(** Top definition *)
type top_def = TopDef of loc * identifier * ty * tm

type top_defs = top_def list
(** Top (mutually recursive) definitions *)

(** Top statements *)
type top_statement =
  | TopQuotInds of loc * quotient_inductive_decls
  | TopDefs     of loc * top_defs

(** Module definition *)
type module_def = ModDef of top_statement list
