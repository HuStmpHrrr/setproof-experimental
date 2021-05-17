open Base

type position = {
  line : int;
  col : int;
}

type real_location = {
  file_name : string;
  start_pos : position;
  end_pos : position;
}

type location =
  | RealLoc  of real_location
  | GhostLoc

type identifier = string

(** Terms *)
type tm =
  | TmVar   of location * identifier
  | TmLam   of location * identifier * ty * tm
  | TmPi    of location * identifier * ty * ty
  | TmMatch of location * tm * branch list

and ty = tm
(** Types *)

and branch = pattern * tm
(** Match branches *)

(** Match patterns *)
and pattern =
  | PatWildcard  of location
  | PatVar       of location * identifier
  | PatInductive of location * identifier * pattern list

(** Inductive type constructor declaration *)
type constructor_decl = CtrDecl of location * identifier * ty

(** Inductive type declaration *)
type inductive_decl =
  | IndDecl of location * identifier * ty * constructor_decl list

type inductive_decls = inductive_decl list
(** (Mutually recursive) inductive type declarations *)

(** Top definition *)
type top_def = TopDef of location * identifier * ty * tm

type top_defs = top_def list
(** Top (mutually recursive) definitions *)

(** Top statements *)
type top_statement =
  | TopInds of location * inductive_decls
  | TopDefs of location * top_defs

(** Module definition *)
type module_def = ModDef of top_statement list
