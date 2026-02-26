//! The frontend of our compiler processes source code into an
//! abstract syntax tree (AST). During this process, the frontend
//! ensures that variables are in scope and renames them to use unique
//! identifiers.

use crate::ast::*;
use crate::identifiers::*;
use crate::span::SrcLoc;
use im::{HashMap, HashSet};

pub struct Resolver {
    pub vars: IdGen<VarName>,
    pub funs: IdGen<FunName>,
    pub extern_funs: HashSet<String>
}

#[derive(Clone)]
pub struct VarInfo {
    pub name: VarName,
    pub src: SrcLoc,
}

#[derive(Clone)]
pub struct FunInfo {
    label: FunName,
    arity: usize,
}

/// CompileErr is an error type that is used to report errors during
/// compilation.
///
/// In the following constructors, the String argument is the original
/// name of the variable or function and the SrcLoc argument is where
/// in the source program the error occurred.
#[derive(Debug, Clone)]
pub enum CompileErr {
    UnboundVariable(String, SrcLoc),
    DuplicateVariable(String, SrcLoc),
    UnboundFunction(String, SrcLoc),
    DuplicateFunction(String, SrcLoc),
    DuplicateParameter(String, SrcLoc),
    ArityMismatch { name: String, expected: usize, found: usize, loc: SrcLoc },
}

/*
 * #[derive(Clone, Debug)]
pub struct Prog<Var, Fun> {
    pub externs: Vec<ExtDecl<Var, Fun>>,
    /// The name of the main function. Should always be "main".
    pub name: Fun,
    pub param: (Var, SrcLoc),
    pub body: Expr<Var, Fun>,
    pub loc: SrcLoc,
}
*/

impl Resolver {
    pub fn new() -> Self {
        Resolver { vars: IdGen::new(), funs: IdGen::new(), extern_funs: HashSet::new() }
    }

    pub fn resolve_prog(&mut self, prog: SurfProg) -> Result<BoundProg, CompileErr> {
        let mut vars_by_string = HashMap::<String, VarInfo>::new();
        let funs_by_string = HashMap::<String, FunInfo>::new();

        let v = VarInfo {
            name: self.vars.fresh(prog.param.0.clone()),
            src: prog.param.1,
        };

        vars_by_string.insert(prog.param.0.clone(), v.clone());

        let mut bound_externs = Vec::<BoundExtDecl>::new();

        // extract externs
        // unmangled
        for extern_fun in prog.externs {
            self.extern_funs.insert(extern_fun.name.clone());

            let bound = BoundExtDecl {
                name: FunName::Unmangled(extern_fun.name.clone()),
                params: extern_fun.params
                    .into_iter()
                    .map(|(param_name, src)| (self.vars.fresh(param_name), src))
                    .collect(),
                    loc: extern_fun.loc
            };

            bound_externs.push(bound);
        }

        let bound_expr = self.resolve_expr(prog.body, &vars_by_string, &funs_by_string, true)?;

        let bound_prog = BoundProg {
            externs: bound_externs,
            param: (v.name, v.src),
            body: bound_expr,
            name: FunName::Unmangled("entry".to_string()),
            loc: prog.loc,
        };

        Ok(bound_prog)
    }

    fn resolve_expr(
        &mut self,
        expr: SurfExpr,
        prev_vars: &HashMap<String, VarInfo>,
        prev_funs: &HashMap<String, FunInfo>,
        is_tail: bool,
    ) -> Result<BoundExpr, CompileErr> {
        let mut cur_vars = prev_vars.clone();
        let cur_funs = prev_funs.clone();

        let bound_expr = match expr {
            Expr::Num(i, src) => Expr::Num(i, src),

            Expr::Bool(b, src) => Expr::Bool(b, src),

            Expr::Var(v, src) => {
                let var = cur_vars.get(&v).cloned();
                if var.is_none() {
                    return Err(CompileErr::UnboundVariable(v, src));
                }
                let var = var.unwrap();
                Expr::Var(var.name, var.src)
            }

            Expr::Prim { prim, args, loc } => Expr::Prim {
                prim,
                args: {
                    let mut v = Vec::<Expr<VarName, FunName>>::new();
                    for ex in args {
                        let bound_ex = self.resolve_expr(ex, &cur_vars, &cur_funs, false)?;
                        v.push(bound_ex);
                    }
                    v
                },
                loc,
            },

            Expr::If { cond, thn, els, loc } => {
                let bound_cond = self.resolve_expr(*cond, &cur_vars, &cur_funs, false)?;
                let bound_thn = self.resolve_expr(*thn, &cur_vars, &cur_funs, is_tail)?;
                let bound_els = self.resolve_expr(*els, &cur_vars, &cur_funs, is_tail)?;

                Expr::If {
                    cond: Box::new(bound_cond),
                    thn: Box::new(bound_thn),
                    els: Box::new(bound_els),
                    loc
                }
            },

            Expr::Let {
                bindings,
                body,
                loc,
            } => Expr::Let {
                bindings: {
                    let mut vars_being_bound = HashSet::<String>::new();
                    let mut bound_bindings = Vec::<Binding<VarName, FunName>>::new();
                    for bind in bindings {
                        if vars_being_bound.contains(&bind.var.0) {
                            return Err(CompileErr::DuplicateVariable(bind.var.0, bind.var.1));
                        }
                        vars_being_bound.insert(bind.var.0.clone());

                        let bound_expr = self.resolve_expr(bind.expr, &cur_vars, &cur_funs, false)?;

                        let v = self.vars.fresh(bind.var.0.clone());
                        cur_vars.insert(
                            bind.var.0,
                            VarInfo {
                                name: v.clone(),
                                src: bind.var.1,
                            },
                        );

                        let bound_bind = Binding::<VarName, FunName> {
                            var: (v, bind.var.1),
                            expr: bound_expr,
                        };

                        bound_bindings.push(bound_bind);
                    }
                    bound_bindings
                },
                body: {
                    let b = self.resolve_expr(*body, &cur_vars, &cur_funs, is_tail)?;
                    Box::new(b)
                },
                loc,
            },

            Expr::FunDefs { decls, body, loc } => {
                let new_vars = cur_vars.clone();
                let mut new_funs = cur_funs.clone();

                let mut name_set = HashSet::new();

                // first pass: register all function names to allow mutual recursion
                for decl in &decls {
                    if name_set.contains(&decl.name) {
                        return Err(CompileErr::DuplicateFunction(decl.name.clone(), decl.loc));
                    }
                    name_set.insert(decl.name.clone());
                    let label = self.funs.fresh(decl.name.clone());
                    new_funs.insert(
                        decl.name.clone(),
                        FunInfo {
                            label: label.clone(),
                            arity: decl.params.len(),
                        },
                    );
                }

                // second pass: resolve each function body
                let mut bound_decls = Vec::new();
                for decl in decls {
                    let mut param_vars = new_vars.clone();
                    let mut param_names = HashSet::new();
                    let mut bound_params = Vec::new();

                    for param in decl.params {
                        if param_names.contains(&param.0) {
                            return Err(CompileErr::DuplicateParameter(param.0, param.1));
                        }
                        param_names.insert(param.0.clone());

                        let v = self.vars.fresh(param.0.clone());
                        param_vars.insert(
                            param.0,
                            VarInfo {
                                name: v.clone(),
                                src: param.1,
                            },
                        );
                        bound_params.push((v, param.1));
                    }

                    let bound_body = self.resolve_expr(decl.body, &param_vars, &new_funs, true)?;
                    let info = new_funs.get(&decl.name).unwrap();

                    bound_decls.push(FunDecl {
                        name: info.label.clone(),
                        params: bound_params,
                        body: bound_body,
                        loc: decl.loc,
                    });
                }

                let bound_body = self.resolve_expr(*body, &new_vars, &new_funs, is_tail)?;

                Expr::FunDefs {
                    decls: bound_decls,
                    body: Box::new(bound_body),
                    loc
                }
            },

            Expr::Call { fun, args, loc } => {
                // check if extern
                let mut bound_args = Vec::new();

                for arg in args.clone() {
                    bound_args.push(self.resolve_expr(arg, &cur_vars, &cur_funs, false)?);
                }

                if self.extern_funs.contains(&fun) {
                    Expr::Call {
                        fun: FunName::Unmangled(fun),
                        args: bound_args,
                        loc
                    }
                }
                else if fun == "main" {
                    Expr::Call {
                        fun: FunName::Unmangled("entry".to_string()),
                        args: bound_args,
                        loc
                    }
                }
                // locally defined?
                else if let Some(info) = cur_funs.get(&fun).cloned() {
                    if info.arity != args.len() {
                        return Err(CompileErr::ArityMismatch {
                            name: fun,
                            expected: info.arity,
                            found: args.len(),
                            loc
                        });
                    }

                    Expr::Call {
                        fun: info.label,
                        args: bound_args,
                        loc
                    }
                }
                // unbound
                else {
                    return Err(CompileErr::UnboundFunction(fun, loc));
                }
            }
        };

        Ok(bound_expr)
    }
}

