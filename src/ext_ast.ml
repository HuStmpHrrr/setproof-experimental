open Lib

type identifier = string [@@deriving show { with_path = false }]

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
[@@deriving show { with_path = false }]

(** Types *)
and ty = tm [@@deriving show { with_path = false }]

(** Match branches *)
and branch = pattern * tm [@@deriving show { with_path = false }]

(** Match patterns *)
and pattern =
  | PatVar of loc * identifier
  | PatInd of loc * identifier * identifier list
  | PatEq  of loc * identifier
[@@deriving show { with_path = false }]

(** definition *)
type fun_def = FunDef of loc * identifier * ty * tm
[@@deriving show { with_path = false }]

(** Quotient inductive type constructor/quotient *)
type quotient_inductive_entry_def =
  | QuotIndEntryDef of loc * identifier * ty  (** Entry with name and type *)
[@@deriving show { with_path = false }]

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
[@@deriving show { with_path = false }]

(** Top statements *)
type top_statement =
  | TopFunDef  of fun_def
  | TopQuotInd of quotient_inductive_def
[@@deriving show { with_path = false }]

(** Module definition *)
type module_def = ModDef of top_statement list
[@@deriving show { with_path = false }]

let tm_loc = function
  | TmUniv (l, _)        -> l
  | TmConstr (l, _)      -> l
  | TmVar (l, _)         -> l
  | TmLam (l, _, _, _)   -> l
  | TmPi (l, _, _, _)    -> l
  | TmMatch (l, _, _, _) -> l
  | TmApp (l, _, _)      -> l
  | TmEq (l, _, _)       -> l
  | TmRefl (l, _)        -> l

let pattern_loc = function
  | PatVar (l, _)    -> l
  | PatInd (l, _, _) -> l
  | PatEq (l, _)     -> l
