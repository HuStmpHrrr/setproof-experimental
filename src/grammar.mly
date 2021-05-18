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
%token SYM_DEFEQ SYM_ARROW SYM_COLON SYM_COMMA SYM_SEMI SYM_EQ SYM_UNDERSCORE
%token KEY_PI KEY_LAM KEY_QIND KEY_WHERE KEY_MATCH KEY_WITH KEY_REFL
%token <string> UPPER_IDENT
%token <string> LOWER_IDENT

%start <Ext_ast.module_def> modDef
%%

let modDef :=
  | ss = topStmt*; EOF; { Ext_ast.ModDef ss }

let topStmt :=
  | q = quotInd; { Ext_ast.TopQuotInd q }
  | d = def;     { Ext_ast.TopDef d }

let quotInd :=
  | KEY_QIND; id = LOWER_IDENT; inds = varTm*; SYM_COLON; kappa = tm; KEY_WHERE; entries = quotIndEntry*; SYM_SEMI;
    { Ext_ast.QuotIndDecl (loc_conv $loc, id, inds, kappa, entries) }

let quotIndEntry :=
  | id = UPPER_IDENT; SYM_COLON; ~ = tm; SYM_SEMI; { Ext_ast.QuotIndEntryDecl (loc_conv $loc, id, tm) }

let def :=
  | id = LOWER_IDENT; SYM_COLON; ty = tm; SYM_DEFEQ; ~ = tm; SYM_SEMI; { Ext_ast.Def (loc_conv $loc, id, ty, tm) }

let tm := tm0

let tm0 :=
  | KEY_LAM; id = LOWER_IDENT; SYM_COLON; ty = tm0; SYM_COMMA; tm = tm0;
    { Ext_ast.TmLam (loc_conv $loc, id, ty, tm) }
  | KEY_PI; SYM_LPAR; id = LOWER_IDENT; SYM_COLON; ty0 = tm0; SYM_RPAR; SYM_ARROW; ty1 = tm0;
    { Ext_ast.TmPi (loc_conv $loc, id, ty0, ty1) }
  | KEY_MATCH; scr = tm0; KEY_WITH; ~ = branches;
    { Ext_ast.TmMatch (loc_conv $loc, scr, branches) }
  | ty0 = tm1; SYM_ARROW; ty1 = tm0;
    { Ext_ast.TmPi (loc_conv $loc, "_", ty0, ty1) }
  | ~ = tm1; <>

let branches :=
  | bs = branch*; { bs }

let branch :=
  | ~ = pattern; SYM_ARROW; ~ = tm; SYM_SEMI; { (pattern, tm) }

let pattern :=
  | ctr = UPPER_IDENT; args = atomicPattern*; { Ext_ast.PatInd (loc_conv $loc, ctr, args) }
  | KEY_REFL; ~ = atomicPattern;              { Ext_ast.PatEq (loc_conv $loc, atomicPattern) }
  | ~ = atomicPattern;                        <>

let atomicPattern :=
  | SYM_UNDERSCORE;                  { Ext_ast.PatWildcard (loc_conv $loc) }
  | id = LOWER_IDENT;                { Ext_ast.PatVar (loc_conv $loc, id) }
  | SYM_LPAR; ~ = pattern; SYM_RPAR; <>

let tm1 :=
  | lhs = tm2; SYM_EQ; rhs = tm2; { Ext_ast.TmEq (loc_conv $loc, lhs, rhs) }
  | ~ = tm2; <>

let tm2 :=
  | f = tm2; a = tm3; { Ext_ast.TmApp (loc_conv $loc, f, a) }
  | ~ = tm3; <>

let tm3 :=
  | KEY_REFL; tm = tm4; { Ext_ast.TmRefl (loc_conv $loc, tm) }
  | ~ = tm4; <>

let tm4 :=
  | ~ = varTm; <>
  | ~ = tm5;   <>

let tm5 :=
  | SYM_LPAR; ~ = tm; SYM_RPAR; <>

let varTm :=
  | id = LOWER_IDENT; { Ext_ast.TmVar (loc_conv $loc, id) }
