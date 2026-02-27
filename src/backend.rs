//! The backend of our compiler translates our intermediate
//! representation into assembly code, mapping intermediate
//! representation variables into concrete memory locations.

use crate::asm::*;
use crate::identifiers::*;
use crate::middle_end::Lowerer;
use crate::ssa::*;

use im::HashMap;
use im::HashSet;

pub struct Emitter {
    // the output buffer for the sequence of instructions we are generating
    instrs: Vec<Instr>,
}

impl From<Lowerer> for Emitter {
    fn from(Lowerer { .. }: Lowerer) -> Self {
        Emitter { instrs: Vec::new() }
    }
}

impl Emitter {
    pub fn new() -> Self {
        Emitter { instrs: Vec::new() }
    }

    pub fn to_asm(self) -> Vec<Instr> {
        self.instrs
    }

    fn emit(&mut self, instr: Instr) {
        self.instrs.push(instr);
    }

    fn collect_variables(&mut self, body: &BlockBody, variables: &mut HashMap<VarName, i64>, next_offset: &mut i64) {
        match body {
            BlockBody::Terminator(_) => {}

            BlockBody::Operation { dest, next, .. } => {
                variables.insert(dest.clone(), *next_offset);
                *next_offset += 8;
                self.collect_variables(next, variables, next_offset);
            }

            BlockBody::SubBlocks { blocks, next } => {
                // collect variables from all basic blocks
                for block in blocks {
                    // collect block parameters
                    for param in &block.params {
                        variables.insert(param.clone(), *next_offset);
                        *next_offset += 8;
                    }
                    // collect variables from block body
                    self.collect_variables(&block.body, variables, next_offset);
                }
                // continue with next
                self.collect_variables(next, variables, next_offset);
            }
        }
    }

    fn collect_all_variables(&mut self, prog: &Program) -> (HashMap<VarName, i64>, i64) {
        let mut variables: HashMap<VarName, i64> = HashMap::new();
        let mut next_offset: i64 = 8;

        for fun in &prog.funs {
            for param in &fun.params {
                variables.insert(param.clone(), next_offset);
                next_offset += 8;
            }
        }

        for block in &prog.blocks {
            for param in &block.params {
                variables.insert(param.clone(), next_offset);
                next_offset += 8;
            }
            self.collect_variables(&block.body, &mut variables, &mut next_offset);
        }

        (variables, next_offset)
    }

    pub fn emit_prog(&mut self, prog: &Program) {
        let top_level_labels: HashSet<String> = prog.blocks
            .iter()
            .map(|b| b.label.to_string())
            .collect();

        // externs
        for ext in &prog.externs {
            self.emit(Instr::Extern(ext.name.to_string()));
        }

        self.emit(Instr::Section(".data".to_string()));
        self.emit(Instr::Section(".text".to_string()));

        // entry point is now handled like an extern
        // collect_all_variables now handles creating the containers too
        let (variables, next_offset) = self.collect_all_variables(prog);

        // build block map for branch resolution
        let mut block_map: HashMap<BlockName, &BasicBlock> = HashMap::new();
        for block in &prog.blocks {
            block_map.insert(block.label.clone(), block);
        }

        // emit fun blocks
        for fun in &prog.funs {
            self.emit(Instr::Global(fun.name.to_string()));
            self.emit_fun_block(fun, &variables);
        }

        // emit basic blocks (label + prologue + body + epilogue)
        for block in &prog.blocks {
            self.emit(Instr::Label(block.label.to_string()));

            // prologue
            self.emit(Instr::Push(Arg32::Reg(Reg::Rbp)));
            self.emit(Instr::Mov(MovArgs::ToReg(Reg::Rbp, Arg64::Reg(Reg::Rsp))));
            self.emit(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Signed(next_offset as i32))));

            // for tail calls, skip the prologue
            self.emit(Instr::Label(format!("{}_body", block.label)));

            self.emit_body(&block.body, &variables, &block_map, next_offset, &top_level_labels);

            // epilogue label
            // each needs their own leave label
            let leave_label = format!("{}_leave", block.label);
            self.emit(Instr::Label(leave_label.clone()));
            self.emit(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Signed(next_offset as i32))));
            self.emit(Instr::Pop(Loc::Reg(Reg::Rbp)));
            self.emit(Instr::Ret);
        }
    }

    // delegator
    fn emit_body(&mut self, body: &BlockBody, variables: &HashMap<VarName, i64>, blocks: &HashMap<BlockName, &BasicBlock>, next_offset: i64, top_level_labels: &HashSet<String>) {
        match body {
            BlockBody::Terminator(terminator) => {
                match terminator {
                    Terminator::Return(imm) => {
                        self.emit_imm(imm, Reg::Rax, variables);
                        self.emit(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Signed(next_offset as i32))));
                        self.emit(Instr::Pop(Loc::Reg(Reg::Rbp)));
                        self.emit(Instr::Ret);
                    }
                    Terminator::Branch(branch) => {
                        let target_block = blocks.get(&branch.target).expect("block not found");
                        for (arg, param_name) in branch.args.iter().zip(target_block.params.iter()) {
                            self.emit_imm(arg, Reg::Rax, variables);
                            self.store_rax(param_name, variables);
                        }
                        let target_label = if top_level_labels.contains(&branch.target.to_string()) {
                            format!("{}_body", branch.target)
                        } else {
                            branch.target.to_string()
                        };
                        self.emit(Instr::Jmp(JmpArgs::Label(target_label)));
                    }
                    Terminator::ConditionalBranch { cond, thn, els } => {
                        // evaluate the condition
                        self.emit_imm(cond, Reg::Rax, variables);

                        // compare to 0 (false)
                        self.emit(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Signed(0))));

                        // jump to els if equal to 0 (false)
                        self.emit(Instr::JCC(ConditionCode::E, els.to_string()));

                        // fall through / jump to thn
                        self.emit(Instr::Jmp(JmpArgs::Label(thn.to_string())));
                    }
                }
            }

            BlockBody::Operation { dest, op, next } => {
                self.emit_op(op, dest, variables, next_offset);
                self.emit_body(next, variables, blocks, next_offset, top_level_labels);
            }

            BlockBody::SubBlocks { blocks: sub_blocks, next } => {
                let mut block_map = HashMap::new();
                for block in sub_blocks {
                    block_map.insert(block.label.clone(), block);
                }

                for (l, block) in blocks.clone() {
                    block_map.insert(l, block);
                }

                // continue with next
                self.emit_body(next, variables, &block_map, next_offset, top_level_labels);

                // emit each basic block
                for block in sub_blocks {
                    self.emit(Instr::Label(block.label.to_string()));
                    self.emit_body(&block.body, variables, &block_map, next_offset, top_level_labels);
                }
            }
        }
    }

    /*
    pub enum Immediate {
        Const(i64),
        Var(VarName),
    }
    */
    fn emit_imm(&mut self, imm: &Immediate, reg: Reg, variables: &HashMap<VarName, i64>) {
        match imm {
            Immediate::Const(val) => {
                self.emit(Instr::Mov(MovArgs::ToReg(reg, Arg64::Signed(*val))));
            }
            Immediate::Var(var) => {
                let offset = *variables.get(var).unwrap();
                self.emit(Instr::Mov(MovArgs::ToReg(
                    reg,
                    Arg64::Mem(MemRef { reg: Reg::Rbp, offset: -(offset as i32) }) // MemRef offset is i32
                )));
            }
        }
    }

    fn emit_op(&mut self, op: &Operation, dest: &VarName, variables: &HashMap<VarName, i64>, next_offset: i64) {
        match op {
            Operation::Immediate(imm) => {
                self.emit_imm(imm, Reg::Rax, variables);
            }
            Operation::Prim1(prim, imm) => {
                self.emit_unary_op(prim, imm, variables);
            }
            Operation::Prim2(prim, imm1, imm2) => {
                self.emit_binary_op(prim, imm1, imm2, variables);
            }
            Operation::Call { fun, args } => {
                let reg_args_regs = [Reg::Rdi, Reg::Rsi, Reg::Rdx, Reg::Rcx, Reg::R8, Reg::R9];
                let reg_args = &args[..args.len().min(6)];
                let stack_args = if args.len() > 6 { &args[6..] } else { &[] };

                let l = next_offset / 8; // number of local variable slots
                let a = stack_args.len() as i64;
                let p = if (l + a) % 2 == 0 { 1i64 } else { 0 };

                assert!((l + p + a) % 2 == 1, "stack misaligned before call");

                // register-passed args: load into rax first to avoid clobbering
                // (e.g. rdi might itself be a variable we need to read)
                for (imm, &reg) in reg_args.iter().zip(reg_args_regs.iter()) {
                    self.emit_imm(imm, Reg::Rax, variables);
                    self.emit(Instr::Mov(MovArgs::ToReg(reg, Arg64::Reg(Reg::Rax))));
                }

                // stack-passed args
                for (i, imm) in stack_args.iter().enumerate() {
                    self.emit_imm(imm, Reg::Rax, variables);
                    let offset = (l + p + a - i as i64) * 8;
                    self.emit(Instr::Mov(MovArgs::ToMem(
                                MemRef { reg: Reg::Rsp, offset: -(offset as i32) },
                                Reg32::Reg(Reg::Rax),
                    )));
                }

                let adj = (l + p + a) * 8;
                self.emit(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Signed(adj as i32))));
                self.emit(Instr::Call(JmpArgs::Label(fun.to_string())));
                self.emit(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Signed(adj as i32))));
                // result left in rax, emit_op will call store_rax after this
            }
        }

        self.store_rax(dest, variables);
    }

    fn clear_upper_bits(&mut self) {
        self.emit(Instr::And(BinArgs::ToReg(Reg::Rax, Arg32::Unsigned(0xFF))));
    }

    fn emit_unary_op(&mut self, prim: &Prim1, imm: &Immediate,
        variables: &HashMap<VarName, i64>) {
        // load args
        self.emit_imm(imm, Reg::Rax, variables);

        // emit the op
        match prim {
            Prim1::BitNot => {
                self.emit(Instr::Xor(BinArgs::ToReg(Reg::Rax, Arg32::Signed(-1))));
            }
            Prim1::IntToBool => {
                // check if rax is 0
                self.emit(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Unsigned(0))));
                self.emit(Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(0))));
                self.emit(Instr::SetCC(ConditionCode::NE, Reg8::Al));
                self.clear_upper_bits();
            }
        };
    }

    fn emit_binary_op(&mut self, prim: &Prim2, imm1: &Immediate, imm2: &Immediate,
        variables: &HashMap<VarName, i64>) {
        // load args
        self.emit_imm(imm1, Reg::Rax, variables);
        self.emit_imm(imm2, Reg::Rdx, variables);

        // emit the op
        let bin_args = BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx));
        match prim {
            Prim2::Add => self.emit(Instr::Add(bin_args)),
            Prim2::Sub => self.emit(Instr::Sub(bin_args)),
            Prim2::Mul => self.emit(Instr::IMul(bin_args)),

            Prim2::BitAnd => self.emit(Instr::And(bin_args)),
            Prim2::BitOr => self.emit(Instr::Or(bin_args)),
            Prim2::BitXor => self.emit(Instr::Xor(bin_args)),

            Prim2::Lt => {
                self.emit(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                self.emit(Instr::SetCC(ConditionCode::L, Reg8::Al));
                self.clear_upper_bits();
            }
            Prim2::Le => {
                self.emit(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                self.emit(Instr::SetCC(ConditionCode::LE, Reg8::Al));
                self.clear_upper_bits();
            }
            Prim2::Gt => {
                self.emit(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                self.emit(Instr::SetCC(ConditionCode::G, Reg8::Al));
                self.clear_upper_bits();
            }
            Prim2::Ge => {
                self.emit(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                self.emit(Instr::SetCC(ConditionCode::GE, Reg8::Al));
                self.clear_upper_bits();
            }
            Prim2::Eq => {
                self.emit(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                self.emit(Instr::SetCC(ConditionCode::E, Reg8::Al));
                self.clear_upper_bits();
            }
            Prim2::Neq => {
                self.emit(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rdx))));
                self.emit(Instr::SetCC(ConditionCode::NE, Reg8::Al));
                self.clear_upper_bits();
            }
        };
    }

    fn emit_fun_block(&mut self, fun: &FunBlock, variables: &HashMap<VarName, i64>) {
        self.emit(Instr::Label(fun.name.to_string()));
        let reg_args = [Reg::Rdi, Reg::Rsi, Reg::Rdx, Reg::Rcx, Reg::R8, Reg::R9];

        for (i, param) in fun.params.iter().enumerate() {
            // what rbp-relative offset will be before prologue
            let offset = *variables.get(param).unwrap();
            // rsp is 8 higher than rbp will be, so add 8
            let mem = MemRef { reg: Reg::Rsp, offset: -(offset as i32 + 8) };

            if i < 6 {
                self.emit(Instr::Mov(MovArgs::ToMem(mem, Reg32::Reg(reg_args[i]))));
            } else {
                let caller_offset = ((i - 6) + 1) * 8;
                self.emit(Instr::Mov(MovArgs::ToReg(
                            Reg::Rax,
                            Arg64::Mem(MemRef { reg: Reg::Rsp, offset: caller_offset as i32 }),
                )));
                self.emit(Instr::Mov(MovArgs::ToMem(mem, Reg32::Reg(Reg::Rax))));
            }
        }

        self.emit(Instr::Jmp(JmpArgs::Label(fun.body.target.to_string())));
    }

    fn store_rax(&mut self, dest: &VarName, variables: &HashMap<VarName, i64>) {
        let dest_offset = *variables.get(dest).unwrap();
        self.emit(Instr::Mov(MovArgs::ToMem(
            MemRef { reg: Reg::Rbp, offset: -(dest_offset as i32) },
            Reg32::Reg(Reg::Rax)
        )));
    }
}
