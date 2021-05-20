%{
  let loc_conv (start_p, end_p) =
    Ppxlib.(Lib.(RealLoc {
      file = start_p.pos_fname;
      start_l = start_p.pos_lnum;
      start_c = start_p.pos_cnum - start_p.pos_bol;
      end_l = end_p.pos_lnum;
      end_c = end_p.pos_cnum - end_p.pos_bol;
      data = ();
    }))
%}

%token EOF
%token SYM_LPAR SYM_RPAR
%token SYM_DEFEQ SYM_ARROW SYM_COLON SYM_COMMA SYM_SEMI SYM_EQ
%token KEY_PI KEY_LAM KEY_DATA KEY_WHERE KEY_QUOTIENT KEY_MATCH KEY_WITH KEY_REFL KEY_UNIV
%token < string > UPPER_IDENT
%token < string > LOWER_IDENT
%token < int > INTEGER

%start < Ext_ast.module_def > modDef
%%

let modDef :=
  | ~ = topStmt*; EOF; < Ext_ast.ModDef >

let topStmt :=
  | ~ = quotInd; < Ext_ast.TopQuotInd >
  | ~ = funDef;  < Ext_ast.TopFunDef >

let quotInd :=
  | KEY_DATA; quot_id = LOWER_IDENT; quot_indices = quotIndArgument*; SYM_COLON; quot_kind = tm; KEY_WHERE;
      quot_constrs = quotIndEntry*;
    SYM_SEMI;
    { Ext_ast.QuotIndDef { quot_loc = loc_conv $loc; quot_id; quot_indices; quot_kind; quot_constrs; quot_quotients = []} }
  | KEY_DATA; quot_id = LOWER_IDENT; quot_indices = quotIndArgument*; SYM_COLON; quot_kind = tm; KEY_WHERE;
      quot_constrs = quotIndEntry*;
    KEY_QUOTIENT;
      quot_quotients = quotIndEntry*;
    SYM_SEMI;
    { Ext_ast.QuotIndDef { quot_loc = loc_conv $loc; quot_id; quot_indices; quot_kind; quot_constrs; quot_quotients} }

let quotIndArgument :=
  | SYM_LPAR; id = LOWER_IDENT; SYM_COLON; ~ = tm; SYM_RPAR; { (id, tm) }

let quotIndEntry :=
  | id = UPPER_IDENT; SYM_COLON; ~ = tm; SYM_SEMI; { Ext_ast.QuotIndEntryDef (loc_conv $loc, id, tm) }

let funDef :=
  | id = LOWER_IDENT; SYM_COLON; ty = tm; SYM_DEFEQ; ~ = tm; SYM_SEMI;
    { Ext_ast.FunDef (loc_conv $loc, id, ty, tm) }

let tm := tm0

let tm0 :=
  | KEY_LAM; id = LOWER_IDENT; SYM_COLON; ty = tm0; SYM_COMMA; tm = tm0;
    { Ext_ast.TmLam (loc_conv $loc, id, ty, tm) }
  | KEY_PI; SYM_LPAR; id = LOWER_IDENT; SYM_COLON; ty0 = tm0; SYM_RPAR; SYM_ARROW; ty1 = tm0;
    { Ext_ast.TmPi (loc_conv $loc, id, ty0, ty1) }
  | KEY_MATCH; scr = tm0; KEY_WITH; constrBrs = branches;
    { Ext_ast.TmMatch (loc_conv $loc, scr, constrBrs, []) }
  | KEY_MATCH; scr = tm0; KEY_WITH; constrBrs = branches; KEY_QUOTIENT; quotBrs = branches;
    { Ext_ast.TmMatch (loc_conv $loc, scr, constrBrs, quotBrs) }
  | ty0 = tm1; SYM_ARROW; ty1 = tm0;
    { Ext_ast.TmPi (loc_conv $loc, "_", ty0, ty1) }
  | ~ = tm1; <>

let branches :=
  | ~ = branch*; <>

let branch :=
  | ~ = pattern; SYM_ARROW; ~ = tm; SYM_SEMI; { (pattern, tm) }

let pattern :=
  | ctr = UPPER_IDENT; args = LOWER_IDENT*; { Ext_ast.PatInd (loc_conv $loc, ctr, args) }
  | KEY_REFL; id = LOWER_IDENT;             { Ext_ast.PatEq (loc_conv $loc, id) }
  | id = LOWER_IDENT;                       { Ext_ast.PatVar (loc_conv $loc, id) }

let tm1 :=
  | lhs = tm2; SYM_EQ; rhs = tm2; { Ext_ast.TmEq (loc_conv $loc, lhs, rhs) }
  | ~ = tm2; <>

let tm2 :=
  | f = tm2; a = tm3; { Ext_ast.TmApp (loc_conv $loc, f, a) }
  | KEY_REFL; tm = tm3;    { Ext_ast.TmRefl (loc_conv $loc, tm) }
  | KEY_UNIV; i = INTEGER; { Ext_ast.TmUniv (loc_conv $loc, i) }
  | ~ = tm3; <>

let tm3 :=
  | id = UPPER_IDENT; { Ext_ast.TmConstr (loc_conv $loc, id) }
  | id = LOWER_IDENT; { Ext_ast.TmVar (loc_conv $loc, id) }
  | ~ = tm4;          <>

let tm4 :=
  | SYM_LPAR; ~ = tm; SYM_RPAR; <>
