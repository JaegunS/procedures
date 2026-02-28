//! The middle "end" of our compiler is the part that transforms our well-formed
//! source-language abstract syntax tree (AST) into the intermediate representation

use crate::ast::{self, *};
use crate::ssa::{self, *};
use crate::{frontend::Resolver, identifiers::*};

pub struct Lowerer {
    pub vars: IdGen<VarName>,
    pub funs: IdGen<FunName>,
    pub blocks: IdGen<BlockName>,
    program: Program,
    extern_names: std::collections::HashSet<FunName>,
}

/// Indicates whether the expression being compiled is in a tail position.
#[derive(Clone, Debug)]
enum Continuation {
    Return,
    Block(VarName, BlockBody),
}

impl From<Resolver> for Lowerer {
    fn from(resolver: Resolver) -> Self {
        let Resolver { vars, funs, .. } = resolver;
        Lowerer { vars, funs, blocks: IdGen::new(), program: Program { externs: Vec::new(), funs: Vec::new(), blocks: Vec::new() }, extern_names: std::collections::HashSet::<FunName>::new() }
    }
}

/// OPTIONAL:
/// Determine which functions should be lambda lifted.
/// If you skip this (which is totally fine), the default implementation
/// should lift all functions that are defined.
fn should_lift(_prog: &BoundProg) -> std::collections::HashSet<FunName> {
    todo!("should_lift not implemented")
    // lift all non-tailed called functions and functions called by lifted functions
}

impl Lowerer {
    pub fn lower_prog(&mut self, prog: BoundProg) -> Program {
        let BoundProg { externs, name, param, body, loc: _ } = prog;

        for ext in externs {
            let (v, _l): (Vec<VarName>, Vec<SrcLoc>) = ext.params.into_iter().unzip();
            self.extern_names.insert(ext.name.clone());
            self.program.externs.push( Extern { name: ext.name, params: v} )
        }

        let main_body = self.blocks.fresh("main_tail");
        self.program.funs.push( FunBlock { name, params: vec![param.0.clone()], body: Branch { target: main_body.clone(), args: vec![Immediate::Var(param.0.clone())]}} );

        let body = BasicBlock { label: main_body, params: vec![param.0.clone()], body: self.lower_expr_kont(body, Continuation::Return, vec![param.0.clone()], true, None) };
        self.program.blocks.push(body);

        eprintln!("SSA: {:#?}", self.program.clone());

        self.program.clone()
    }

    /// Compiles an expression to a basic block that uses the continuation k on
    /// the value e produces.
    fn lower_expr_kont(&mut self, e: BoundExpr, k: Continuation, params: Vec<VarName>, is_tail: bool, current_fun: Option<&FunName>) -> BlockBody {
        let dest: VarName;
        let next_body: BlockBody;
        match k {
            Continuation::Return => {
                dest = self.vars.fresh("return_value");
                next_body = BlockBody::Terminator(Terminator::Return(Immediate::Var(dest.clone())));
            }
            Continuation::Block(d, body) => {
                dest = d;
                next_body = body;
            }
        };
        match e {
            Expr::Num(n, _src) => BlockBody::Operation {
                dest,
                op: Operation::Immediate(Immediate::Const(n)),
                next: Box::new(next_body),
            },
            Expr::Bool(b, _src) => BlockBody::Operation {
                dest,
                op: Operation::Immediate(Immediate::Const(b.into())),
                next: Box::new(next_body),
            },
            Expr::Var(x, _src) => BlockBody::Operation {
                dest,
                op: Operation::Immediate(Immediate::Var(x)),
                next: Box::new(next_body),
            },
            Expr::Prim { prim, args, loc: _ } => match prim {
                ast::Prim::Add1 => {
                    let tmp = self.vars.fresh("add1_arg");
                    self.lower_expr_kont(
                        args[0].clone(),
                        Continuation::Block(
                            tmp.clone(),
                            BlockBody::Operation {
                                op: Operation::Prim2(
                                    ssa::Prim2::Add,
                                    Immediate::Var(tmp),
                                    Immediate::Const(1),
                                ),
                                dest,
                                next: Box::new(next_body),
                            },
                        ),
                        params,
                        false,
                        current_fun
                    )
                }
                ast::Prim::Sub1 => {
                    let tmp = self.vars.fresh("sub1_arg");
                    self.lower_expr_kont(
                        args[0].clone(),
                        Continuation::Block(
                            tmp.clone(),
                            BlockBody::Operation {
                                op: Operation::Prim2(
                                    ssa::Prim2::Sub,
                                    Immediate::Var(tmp),
                                    Immediate::Const(1),
                                ),
                                dest,
                                next: Box::new(next_body),
                            },
                        ),
                        params,
                        false,
                        current_fun
                    )
                }
                ast::Prim::Add => {
                    let tmp1 = self.vars.fresh("add_arg1");
                    let tmp2 = self.vars.fresh("add_arg2");
                    let block_body = self.lower_expr_kont(
                        args[1].clone(),
                        Continuation::Block(
                            tmp2.clone(),
                            BlockBody::Operation {
                                op: Operation::Prim2(
                                    ssa::Prim2::Add,
                                    Immediate::Var(tmp1.clone()),
                                    Immediate::Var(tmp2),
                                ),
                                dest,
                                next: Box::new(next_body),
                            },
                        ),
                        params.clone(),
                        false,
                        current_fun
                    );
                    self.lower_expr_kont(args[0].clone(), Continuation::Block(tmp1, block_body), params, false, current_fun)
                }
                ast::Prim::Sub => {
                    let tmp1 = self.vars.fresh("sub_arg1");
                    let tmp2 = self.vars.fresh("sub_arg2");
                    let block_body = self.lower_expr_kont(
                        args[1].clone(),
                        Continuation::Block(
                            tmp2.clone(),
                            BlockBody::Operation {
                                op: Operation::Prim2(
                                    ssa::Prim2::Sub,
                                    Immediate::Var(tmp1.clone()),
                                    Immediate::Var(tmp2),
                                ),
                                dest,
                                next: Box::new(next_body),
                            },
                        ),
                        params.clone(),
                        false,
                        current_fun
                    );
                    self.lower_expr_kont(args[0].clone(), Continuation::Block(tmp1, block_body), params, false, current_fun)
                }
                ast::Prim::Mul => {
                    let tmp1 = self.vars.fresh("mul_arg1");
                    let tmp2 = self.vars.fresh("mul_arg2");
                    let block_body = self.lower_expr_kont(
                        args[1].clone(),
                        Continuation::Block(
                            tmp2.clone(),
                            BlockBody::Operation {
                                op: Operation::Prim2(
                                    ssa::Prim2::Mul,
                                    Immediate::Var(tmp1.clone()),
                                    Immediate::Var(tmp2),
                                ),
                                dest,
                                next: Box::new(next_body),
                            },
                        ),
                        params.clone(),
                        false,
                        current_fun
                    );
                    self.lower_expr_kont(args[0].clone(), Continuation::Block(tmp1, block_body), params, false, current_fun)
                }
                ast::Prim::Not => {
                    let tmp1 = self.vars.fresh("not_arg");
                    let tmp2 = self.vars.fresh("not_arg_bool");
                    self.lower_expr_kont(
                        args[0].clone(),
                        Continuation::Block(
                            tmp1.clone(),
                            BlockBody::Operation {
                                op: Operation::Prim1(ssa::Prim1::IntToBool, Immediate::Var(tmp1)),
                                dest: tmp2.clone(),
                                next: Box::new(BlockBody::Operation {
                                    op: Operation::Prim2(
                                        ssa::Prim2::BitXor,
                                        Immediate::Var(tmp2),
                                        Immediate::Const(1),
                                    ),
                                    dest,
                                    next: Box::new(next_body),
                                }),
                            },
                        ),
                        params,
                        false,
                        current_fun
                    )
                }
                ast::Prim::And => {
                    let and1 = self.vars.fresh("and_arg1");
                    let and1_bool = self.vars.fresh("and_arg1_bool");
                    let and2 = self.vars.fresh("and_arg2");
                    let and2_bool = self.vars.fresh("and_arg2_bool");
                    let block_body = self.lower_expr_kont(
                        args[1].clone(),
                        Continuation::Block(
                            and2.clone(),
                            BlockBody::Operation {
                                op: Operation::Prim1(
                                    ssa::Prim1::IntToBool,
                                    Immediate::Var(and1.clone()),
                                ),
                                dest: and1_bool.clone(),
                                next: Box::new(BlockBody::Operation {
                                    op: Operation::Prim1(
                                        ssa::Prim1::IntToBool,
                                        Immediate::Var(and2),
                                    ),
                                    dest: and2_bool.clone(),
                                    next: Box::new(BlockBody::Operation {
                                        op: Operation::Prim2(
                                            ssa::Prim2::BitAnd,
                                            Immediate::Var(and1_bool),
                                            Immediate::Var(and2_bool),
                                        ),
                                        dest,
                                        next: Box::new(next_body),
                                    }),
                                }),
                            },
                        ),
                        params.clone(),
                        false,
                        current_fun
                    );
                    self.lower_expr_kont(args[0].clone(), Continuation::Block(and1, block_body), params, false, current_fun)
                }
                ast::Prim::Or => {
                    let or1 = self.vars.fresh("or_arg1");
                    let or1_bool = self.vars.fresh("or_arg1_bool");
                    let or2 = self.vars.fresh("or_arg2");
                    let or2_bool = self.vars.fresh("or_arg2_bool");
                    let block_body = self.lower_expr_kont(
                        args[1].clone(),
                        Continuation::Block(
                            or2.clone(),
                            BlockBody::Operation {
                                op: Operation::Prim1(
                                    ssa::Prim1::IntToBool,
                                    Immediate::Var(or1.clone()),
                                ),
                                dest: or1_bool.clone(),
                                next: Box::new(BlockBody::Operation {
                                    op: Operation::Prim1(
                                        ssa::Prim1::IntToBool,
                                        Immediate::Var(or2),
                                    ),
                                    dest: or2_bool.clone(),
                                    next: Box::new(BlockBody::Operation {
                                        op: Operation::Prim2(
                                            ssa::Prim2::BitOr,
                                            Immediate::Var(or1_bool),
                                            Immediate::Var(or2_bool),
                                        ),
                                        dest,
                                        next: Box::new(next_body),
                                    }),
                                }),
                            },
                        ),
                        params.clone(),
                        false,
                        current_fun
                    );
                    self.lower_expr_kont(args[0].clone(), Continuation::Block(or1, block_body), params, false, current_fun)
                }
                ast::Prim::Lt => {
                    let tmp1 = self.vars.fresh("lt_arg1");
                    let tmp2 = self.vars.fresh("lt_arg2");
                    let block_body = self.lower_expr_kont(
                        args[1].clone(),
                        Continuation::Block(
                            tmp2.clone(),
                            BlockBody::Operation {
                                op: Operation::Prim2(
                                    ssa::Prim2::Lt,
                                    Immediate::Var(tmp1.clone()),
                                    Immediate::Var(tmp2),
                                ),
                                dest,
                                next: Box::new(next_body),
                            },
                        ),
                        params.clone(),
                        false,
                        current_fun
                    );
                    self.lower_expr_kont(args[0].clone(), Continuation::Block(tmp1, block_body), params, false, current_fun)
                }
                ast::Prim::Le => {
                    let tmp1 = self.vars.fresh("le_arg1");
                    let tmp2 = self.vars.fresh("le_arg2");
                    let block_body = self.lower_expr_kont(
                        args[1].clone(),
                        Continuation::Block(
                            tmp2.clone(),
                            BlockBody::Operation {
                                op: Operation::Prim2(
                                    ssa::Prim2::Le,
                                    Immediate::Var(tmp1.clone()),
                                    Immediate::Var(tmp2),
                                ),
                                dest,
                                next: Box::new(next_body),
                            },
                        ),
                        params.clone(),
                        false,
                        current_fun
                    );
                    self.lower_expr_kont(args[0].clone(), Continuation::Block(tmp1, block_body), params, false, current_fun)
                }
                ast::Prim::Gt => {
                    let tmp1 = self.vars.fresh("gt_arg1");
                    let tmp2 = self.vars.fresh("gt_arg2");
                    let block_body = self.lower_expr_kont(
                        args[1].clone(),
                        Continuation::Block(
                            tmp2.clone(),
                            BlockBody::Operation {
                                op: Operation::Prim2(
                                    ssa::Prim2::Gt,
                                    Immediate::Var(tmp1.clone()),
                                    Immediate::Var(tmp2),
                                ),
                                dest,
                                next: Box::new(next_body),
                            },
                        ),
                        params.clone(),
                        false,
                        current_fun
                    );
                    self.lower_expr_kont(args[0].clone(), Continuation::Block(tmp1, block_body), params, false, current_fun)
                }
                ast::Prim::Ge => {
                    let tmp1 = self.vars.fresh("ge_arg1");
                    let tmp2 = self.vars.fresh("ge_arg2");
                    let block_body = self.lower_expr_kont(
                        args[1].clone(),
                        Continuation::Block(
                            tmp2.clone(),
                            BlockBody::Operation {
                                op: Operation::Prim2(
                                    ssa::Prim2::Ge,
                                    Immediate::Var(tmp1.clone()),
                                    Immediate::Var(tmp2),
                                ),
                                dest,
                                next: Box::new(next_body),
                            },
                        ),
                        params.clone(),
                        false,
                        current_fun
                    );
                    self.lower_expr_kont(args[0].clone(), Continuation::Block(tmp1, block_body), params, false, current_fun)
                }
                ast::Prim::Eq => {
                    let tmp1 = self.vars.fresh("eq_arg1");
                    let tmp2 = self.vars.fresh("eq_arg2");
                    let block_body = self.lower_expr_kont(
                        args[1].clone(),
                        Continuation::Block(
                            tmp2.clone(),
                            BlockBody::Operation {
                                op: Operation::Prim2(
                                    ssa::Prim2::Eq,
                                    Immediate::Var(tmp1.clone()),
                                    Immediate::Var(tmp2),
                                ),
                                dest,
                                next: Box::new(next_body),
                            },
                        ),
                        params.clone(),
                        false,
                        current_fun
                    );
                    self.lower_expr_kont(args[0].clone(), Continuation::Block(tmp1, block_body), params, false, current_fun)
                }
                ast::Prim::Neq => {
                    let tmp1 = self.vars.fresh("neq_arg1");
                    let tmp2 = self.vars.fresh("neq_arg2");
                    let block_body = self.lower_expr_kont(
                        args[1].clone(),
                        Continuation::Block(
                            tmp2.clone(),
                            BlockBody::Operation {
                                op: Operation::Prim2(
                                    ssa::Prim2::Neq,
                                    Immediate::Var(tmp1.clone()),
                                    Immediate::Var(tmp2),
                                ),
                                dest,
                                next: Box::new(next_body),
                            },
                        ),
                        params.clone(), false,
                        current_fun
                    );
                    self.lower_expr_kont(args[0].clone(), Continuation::Block(tmp1, block_body), params, false, current_fun)
                }
            },
            Expr::Let {
                bindings,
                body,
                loc: _,
            } => {
                // create blockbody for the body of let
                let body_value = self.vars.fresh("let_body_value");
                let mut next_block_body = self.lower_expr_kont(
                    *body,
                    Continuation::Block(
                        body_value.clone(),
                        BlockBody::Operation {
                            dest,
                            op: Operation::Immediate(Immediate::Var(body_value)),
                            next: Box::new(next_body),
                        },
                    ),
                    params.clone(),
                    is_tail,
                    current_fun
                );

                // iterate over bindings in reverse, linking to the blockbody which should be executed next
                for binding in bindings.iter().rev() {
                    let current_block_body = self.lower_expr_kont(
                        binding.expr.clone(),
                        Continuation::Block(binding.var.0.clone(), next_block_body),
                        params.clone(),
                        false,
                        current_fun
                    );
                    next_block_body = current_block_body;
                }
                next_block_body
            }
            Expr::If { cond, thn, els, .. } => {
                let cond_value = self.vars.fresh("cond_value");
                let thn_label = self.blocks.fresh("thn_label");
                let thn_value = self.vars.fresh("thn_value");
                let els_label = self.blocks.fresh("els_label");
                let els_value = self.vars.fresh("els_value");
                let continuation_label = self.blocks.fresh("cont_label");

                let cond_block_body = self.lower_expr_kont(
                    *cond,
                    Continuation::Block(
                        cond_value.clone(),
                        BlockBody::Terminator(Terminator::ConditionalBranch {
                            cond: Immediate::Var(cond_value),
                            thn: thn_label.clone(),
                            els: els_label.clone(),
                        }),
                    ),
                    params.clone(),
                    false,
                    current_fun
                );

                BlockBody::SubBlocks {
                    blocks: {
                        vec![
                            BasicBlock {
                                label: thn_label,
                                params: vec![],
                                body: {
                                    self.lower_expr_kont(
                                        *thn,
                                        Continuation::Block(
                                            thn_value.clone(),
                                            BlockBody::Terminator(Terminator::Branch(Branch {
                                                target: continuation_label.clone(),
                                                args: vec![Immediate::Var(thn_value)],
                                            })),
                                        ),
                                        params.clone(),
                                        is_tail,
                                        current_fun
                                    )
                                },
                            },
                            BasicBlock {
                                label: els_label,
                                params: vec![],
                                body: {
                                    self.lower_expr_kont(
                                        *els,
                                        Continuation::Block(
                                            els_value.clone(),
                                            BlockBody::Terminator(Terminator::Branch(Branch {
                                                target: continuation_label.clone(),
                                                args: vec![Immediate::Var(els_value)],
                                            })),
                                        ),
                                        params,
                                        is_tail,
                                        current_fun
                                    )
                                },
                            },
                            BasicBlock {
                                label: continuation_label.clone(),
                                params: vec![dest],
                                body: next_body,
                            },
                        ]
                    },
                    next: Box::new(cond_block_body),
                }
            }
            Expr::FunDefs { decls, body, .. } => {
                let mut fun_body_names = Vec::new();
                // first pass to collect
                for fun in &decls {
                    // get params for function and functions in scope at decl
                    let (v, _l): (Vec<VarName>, Vec<SrcLoc>) = fun.params.clone().into_iter().unzip();
                    let mut fun_params = params.clone();
                    fun_params.extend(v);

                    let fun_body_name = self.blocks.fresh(fun.name.to_string() + "_tail");
                    let fun_args: Vec<Immediate> = fun_params.iter().map(|p| Immediate::Var(p.clone())).collect();

                    self.program.funs.push(FunBlock {
                        name: fun.name.clone(),
                        params: fun_params.clone(),
                        body: Branch { target: fun_body_name.clone(), args: fun_args },
                    });
                    fun_body_names.push((fun_body_name, fun_params));
                }

                // second pass
                for (fun, (fun_body_name, fun_params)) in decls.into_iter().zip(fun_body_names) {
                    let fun_body = BasicBlock {
                        label: fun_body_name,
                        params: fun_params.clone(),
                        body: self.lower_expr_kont(fun.body, Continuation::Return, fun_params, true, Some(&fun.name)),
                    };
                    self.program.blocks.push(fun_body);
                }

                self.lower_expr_kont(*body, Continuation::Block(dest, next_body), params, is_tail, current_fun)
            }

            Expr::Call { fun, args, .. } => {
                let mut a = Vec::<Immediate>::new();
                let mut arg_values = Vec::<VarName>::new();
                let mut target = self.blocks.fresh("if you see this then call didnt find the function");

                // find the function in program
                for fun_decl in self.program.funs.clone() {
                    if fun == fun_decl.name {
                        target = fun_decl.body.target;

                        // add args from functions in scope at decl
                        for i in params.iter().take(fun_decl.params.len() - args.len()) {
                            arg_values.push(i.clone());
                            a.push(Immediate::Var(i.clone()));
                        }

                        break;
                    }
                }

                for _i in 0..args.len() {
                    let arg_value = self.vars.fresh("arg_value");
                    arg_values.push(arg_value.clone());
                    a.push(Immediate::Var(arg_value));
                }

                let is_self_tail = is_tail 
                    && !self.extern_names.contains(&fun)
                    && current_fun.map_or(false, |cf| *cf == fun);

                let mut next_block_body = if is_self_tail {
                    BlockBody::Terminator(Terminator::Branch(Branch { target, args: a }))
                } else {
                    BlockBody::Operation {
                        dest,
                        op: Operation::Call { fun, args: a },
                        next: Box::new(next_body),
                    }
                };

                // iterate over arguments in reverse
                for (arg, arg_value) in args.into_iter().rev().zip(arg_values.into_iter().rev()) {
                    next_block_body =
                        self.lower_expr_kont(arg, Continuation::Block(arg_value, next_block_body), params.clone(), false, current_fun);
                }
                next_block_body
            }
        }
    }
}
