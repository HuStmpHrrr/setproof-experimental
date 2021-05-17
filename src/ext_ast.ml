open Lib

type identifier = string

(** Terms *)
type tm =
  | TmVar   of loc * identifier
  | TmLam   of loc * identifier * ty * tm
  | TmPi    of loc * identifier * ty * ty
  | TmMatch of loc * tm * branch list

and ty = tm
(** Types *)

and branch = pattern * tm
(** Match branches *)

(** Match patterns *)
and pattern =
  | PatWildcard  of loc
  | PatVar       of loc * identifier
  | PatInductive of loc * identifier * pattern list

(** Inductive type constructor declaration *)
type constructor_decl = CtrDecl of loc * identifier * ty

(** Inductive type declaration *)
type inductive_decl =
  | IndDecl of loc * identifier * ty * constructor_decl list

type inductive_decls = inductive_decl list
(** (Mutually recursive) inductive type declarations *)

(** Top definition *)
type top_def = TopDef of loc * identifier * ty * tm

type top_defs = top_def list
(** Top (mutually recursive) definitions *)

(** Top statements *)
type top_statement =
  | TopInds of loc * inductive_decls
  | TopDefs of loc * top_defs

(** Module definition *)
type module_def = ModDef of top_statement list
