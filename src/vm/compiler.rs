use std::{borrow::Cow, cell::RefCell, rc::Rc};

use crate::{
    builtin::BUILTIN_FNS,
    monke_error::MonkeError,
    object::Object,
    parser::parser::{Expression, Statement},
    vm::{bytecode::Bytecode, op_code::op_code::OpCode, symbol_table::SymbolTable},
};

use super::{
    op_code::op_code::Operands,
    symbol_table::{Symbol, SymbolScope},
};

pub type Instruction = (OpCode, Operands);

#[derive(Debug, Clone, PartialEq)]
pub struct CompilationScope {
    pub instrs: Vec<Instruction>,
}

impl CompilationScope {
    fn new() -> Self {
        Self { instrs: vec![] }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Compiler<'i> {
    pub scopes: Vec<CompilationScope>,
    pub scope_idx: usize,
    pub constants: Vec<Rc<Object<'i>>>,
    pub symbol_table: Rc<RefCell<SymbolTable<'i>>>,
}

impl<'i> Compiler<'i> {
    pub fn new() -> Self {
        let main_scope = CompilationScope::new();
        let symbol_table = Rc::new(RefCell::new(SymbolTable::new()));

        for (idx, (bfn_name, _)) in BUILTIN_FNS.iter().enumerate() {
            symbol_table.borrow_mut().define_builtin(idx, bfn_name);
        }

        Self {
            scopes: vec![main_scope],
            scope_idx: 0,
            constants: vec![],
            symbol_table,
        }
    }

    pub fn new_with_state(
        mut symbol_table: SymbolTable<'i>,
        constants: Vec<Rc<Object<'i>>>,
    ) -> Self {
        let mut compiler = Self::new();

        compiler.symbol_table = Rc::new(RefCell::new(symbol_table));
        compiler.constants = constants;

        compiler
    }

    pub fn compile(
        mut self,
        stmns: &[Statement<'i>],
    ) -> Result<(Bytecode, Vec<Rc<Object<'i>>>, Rc<RefCell<SymbolTable<'i>>>), MonkeError> {
        self.process_stmns(stmns)?;

        let scope = self.cur_scope();
        let bytecode = self.compile_bytes(&scope.instrs)?;

        Ok((bytecode, self.constants, self.symbol_table))
    }

    fn compile_bytes(&self, instrs: &[Instruction]) -> Result<Bytecode, MonkeError> {
        let mut bytecode = Bytecode(Vec::with_capacity(instrs.len() * 4));

        let mut rest_instrs = &instrs[..];

        loop {
            let instr = match rest_instrs {
                [] => break,
                [instr, rest @ ..] => {
                    rest_instrs = rest;

                    instr
                }
            };

            match instr {
                (op_code, Operands::Raw(raw)) => {
                    bytecode.extend_from_slice(&OpCode::make(op_code, raw));
                }

                (op_code, Operands::InstrOffset(instr_offset)) => {
                    let instrs_to_target = &rest_instrs[..*instr_offset as usize];

                    let address_offset = {
                        let instr_width = op_code.meta().op_bytes_width;
                        let instrs_before_target_width =
                            OpCode::compute_bytes_width(instrs_to_target);

                        instr_width + instrs_before_target_width
                    };

                    let instr =
                        OpCode::make(op_code, &vec![(bytecode.len() + address_offset) as isize]);

                    bytecode.extend_from_slice(&instr);
                }

                (_, Operands::Placeholder) => {
                    panic!("Operands::Placeholder should not exist when compile_bytes is called");
                }
            };
        }

        Ok(bytecode)
    }

    fn process_stmns(&mut self, stmns: &[Statement<'i>]) -> Result<(), MonkeError> {
        for stmn in stmns {
            self.process_stmn(stmn)?;
        }

        Ok(())
    }

    fn process_stmn(&mut self, stmn: &Statement<'i>) -> Result<(), MonkeError> {
        match stmn {
            Statement::Let { name, expr } => {
                let symbol = self.symbol_table.borrow_mut().define(name); // placed before process_expr to allow recursive functions

                self.process_expr(expr)?;

                let op_code = match symbol.scope {
                    SymbolScope::Global => OpCode::SetGlobal,
                    SymbolScope::Local => OpCode::SetLocal,

                    SymbolScope::Builtin | SymbolScope::Free | SymbolScope::Function => panic!(
                        "SymbolTable.define produces only SymbolScope::Global or SymbolScope::Local"
                    ),
                };

                self.add_instr(op_code, vec![symbol.idx as isize]);
            }

            Statement::ExprStmn { expr } => {
                self.process_expr(expr)?;
                self.add_instr(OpCode::Pop, vec![]);
            }

            Statement::Return { expr } => {
                self.process_expr(expr)?;
                self.add_instr(OpCode::ReturnValue, vec![]);
            }

            Statement::Block { statements } => {
                self.process_stmns(statements)?;
            }
        }

        Ok(())
    }

    fn process_expr(&mut self, expr: &Expression<'i>) -> Result<(), MonkeError> {
        match expr {
            Expression::Identifier(name) => {
                let symbol = self
                    .symbol_table
                    .borrow_mut()
                    .resolve_or_define_free(name)?;

                self.add_get_symbol_instr(symbol);
            }

            Expression::Integer(int) => {
                let constant_id = self.add_constant(Object::Integer(*int)) as isize;

                self.add_instr(OpCode::Constant, vec![constant_id]);
            }

            Expression::Float(float) => {
                let constant_id = self.add_constant(Object::Float(*float)) as isize;

                self.add_instr(OpCode::Constant, vec![constant_id]);
            }

            Expression::Str(str) => {
                let constant_id = self.add_constant(Object::String(Cow::from(*str))) as isize;

                self.add_instr(OpCode::Constant, vec![constant_id]);
            }

            Expression::Bool(bool_value) => {
                match bool_value {
                    true => self.add_instr(OpCode::True, vec![]),
                    false => self.add_instr(OpCode::False, vec![]),
                };
            }

            Expression::Prefix { op, right } => {
                self.process_expr(right)?;

                match *op {
                    "!" => self.add_instr(OpCode::Bang, vec![]),
                    "-" => self.add_instr(OpCode::Minus, vec![]),
                    _ => panic!("{op:?} is not implemented"),
                };
            }

            Expression::Infix { left, op, right } if matches!(*op, "<" | "<=") => {
                self.process_expr(right)?; // NOTE process `right` before `left`
                self.process_expr(left)?;

                match *op {
                    "<" => self.add_instr(OpCode::Greater, vec![]),
                    "<=" => self.add_instr(OpCode::GreaterEqual, vec![]),
                    _ => panic!("{op:?} is not implemented"),
                };
            }

            Expression::Infix { left, op, right } => {
                self.process_expr(left)?;
                self.process_expr(right)?;

                match *op {
                    "+" => self.add_instr(OpCode::Add, vec![]),
                    "-" => self.add_instr(OpCode::Sub, vec![]),
                    "*" => self.add_instr(OpCode::Mul, vec![]),
                    "/" => self.add_instr(OpCode::Div, vec![]),
                    ">" => self.add_instr(OpCode::Greater, vec![]),
                    ">=" => self.add_instr(OpCode::GreaterEqual, vec![]),
                    "==" => self.add_instr(OpCode::Equal, vec![]),
                    "!=" => self.add_instr(OpCode::NotEqual, vec![]),
                    _ => panic!("{op:?} is not implemented"),
                };
            }

            Expression::If { condition, yes, no } => {
                self.process_expr(condition)?;

                let jnt_idx = self.add_instr_with_placeholder(OpCode::JumpNotTrue);

                let after_yes_idx = {
                    self.process_stmn(yes)?;
                    self.remove_last_instr_if_eq(&OpCode::Pop);
                    self.cur_instrs_mut().len()
                };

                let jmp_idx = self.add_instr_with_placeholder(OpCode::Jump);

                match no {
                    None => {
                        let no_as_null_idx = self.add_instr(OpCode::Null, vec![]);

                        self.cur_instrs_mut()[jnt_idx] = (
                            OpCode::JumpNotTrue,
                            Operands::InstrOffset(no_as_null_idx as isize - jnt_idx as isize - 1),
                        );

                        self.cur_instrs_mut()[jmp_idx] = (OpCode::Jump, Operands::InstrOffset(1));
                    }

                    Some(no) => {
                        let after_no_idx = {
                            self.process_stmn(no)?;
                            self.remove_last_instr_if_eq(&OpCode::Pop);
                            self.cur_instrs_mut().len()
                        };

                        let no_start_idx = jmp_idx + 1;

                        self.cur_instrs_mut()[jnt_idx] = (
                            OpCode::JumpNotTrue,
                            Operands::InstrOffset(no_start_idx as isize - jnt_idx as isize - 1),
                        );

                        self.cur_instrs_mut()[jmp_idx] = (
                            OpCode::Jump,
                            Operands::InstrOffset(after_no_idx as isize - jmp_idx as isize - 1),
                        );
                    }
                };
            }

            Expression::Fn {
                parameters,
                body,
                name,
            } => {
                let (fn_scope, fn_free_symbols, num_locals) = {
                    self.enter_scope();

                    if let Some(name) = name {
                        self.symbol_table.borrow_mut().define_function_name(name);
                    }

                    for param in parameters {
                        let Expression::Identifier(name) = param else {
                            return MonkeError::new(format!(
                                "Expected Expression::Identifier in function parameters, instead got {:?}",
                                param
                            )).into();
                        };

                        self.symbol_table.borrow_mut().define(name);
                    }

                    self.process_stmn(body)?;

                    let instrs_mut = self.cur_instrs_mut();
                    match &instrs_mut[..] {
                        [] => {
                            self.add_instr(OpCode::ReturnNull, vec![]);
                        }

                        [.., (OpCode::Pop, _)] => {
                            instrs_mut.remove(instrs_mut.len() - 1);
                            self.add_instr(OpCode::ReturnValue, vec![]);
                        }

                        _ => (),
                    };

                    self.leave_scope()
                };

                let fn_free_symbols_len = fn_free_symbols.len();

                for symbol in fn_free_symbols {
                    self.add_get_symbol_instr(symbol);
                }

                let bytecode = self.compile_bytes(&fn_scope.instrs)?;

                let fn_compiled = Object::CompiledFunction {
                    bytecode,
                    num_locals,
                    num_args: parameters.len(),
                };

                let fn_cnst_idx = self.add_constant(fn_compiled) as isize;

                self.add_instr(
                    OpCode::Closure,
                    vec![fn_cnst_idx, fn_free_symbols_len as isize],
                );
            }

            Expression::Call {
                function,
                arguments,
            } => {
                self.process_expr(function)?;

                for arg in arguments {
                    self.process_expr(arg)?;
                }

                self.add_instr(OpCode::Call, vec![arguments.len() as isize]);
            }

            Expression::Array(elements) => {
                for el in elements {
                    self.process_expr(el)?;
                }

                self.add_instr(OpCode::Array, vec![elements.len() as isize]);
            }

            Expression::Map(keys_values) => {
                for (key, value) in keys_values {
                    self.process_expr(key)?;
                    self.process_expr(value)?;
                }

                self.add_instr(OpCode::Map, vec![keys_values.len() as isize * 2]);
            }

            Expression::Indexing { left, index } => {
                self.process_expr(left)?;
                self.process_expr(index)?;

                self.add_instr(OpCode::Indexing, vec![]);
            }
        };

        Ok(())
    }

    #[inline]
    fn add_get_symbol_instr(&mut self, symbol: Rc<Symbol<'i>>) {
        let op_code = match symbol.scope {
            SymbolScope::Global => OpCode::GetGlobal,
            SymbolScope::Local => OpCode::GetLocal,
            SymbolScope::Builtin => OpCode::GetBuiltin,
            SymbolScope::Free => OpCode::GetFree,
            SymbolScope::Function => OpCode::CurrentClosure,
        };

        self.add_instr(op_code, vec![symbol.idx as isize]);
    }

    #[inline]
    fn remove_last_instr_if_eq(&mut self, exp_op_code: &OpCode) -> bool {
        let cur_instrs = self.cur_instrs_mut();

        match cur_instrs.last() {
            Some((op_code, _)) if op_code == exp_op_code => {
                cur_instrs.remove(cur_instrs.len() - 1);
                true
            }
            _ => false,
        }
    }

    #[inline]
    fn add_constant(&mut self, obj: Object<'i>) -> usize {
        self.constants.push(Rc::new(obj));
        self.constants.len() - 1
    }

    #[inline]
    fn add_instr(&mut self, op_code: OpCode, operands: Vec<isize>) -> usize {
        let cur_instrs = self.cur_instrs_mut();

        cur_instrs.push((op_code, Operands::Raw(operands)));
        cur_instrs.len() - 1
    }

    #[inline]
    fn add_instr_with_placeholder(&mut self, op_code: OpCode) -> usize {
        let cur_instrs = self.cur_instrs_mut();

        cur_instrs.push((op_code, Operands::Placeholder));
        cur_instrs.len() - 1
    }

    #[inline]
    fn enter_scope(&mut self) {
        self.symbol_table = Rc::new(RefCell::new(SymbolTable::with_outer(Rc::clone(
            &self.symbol_table,
        ))));

        self.scopes.push(CompilationScope::new());
        self.scope_idx += 1;
    }

    #[inline]
    fn leave_scope(&mut self) -> (CompilationScope, Vec<Rc<Symbol<'i>>>, usize) {
        let removed_scope = self.scopes.remove(self.scopes.len() - 1);
        self.scope_idx -= 1;

        let outer_symbol_table = self
            .symbol_table
            .borrow_mut()
            .outer
            .take()
            .expect("call to `leave_scope` assumes that an `outer_scope` exists");

        let removed_free_symbols =
            std::mem::replace(&mut self.symbol_table.borrow_mut().free_symbols, vec![]);

        // besides actual num of locals, contains num_args, since args treated like locals
        let num_locals = self.symbol_table.borrow().num_definitions;

        self.symbol_table = outer_symbol_table;

        (removed_scope, removed_free_symbols, num_locals)
    }

    #[inline]
    pub fn cur_scope_mut(&mut self) -> &mut CompilationScope {
        &mut self.scopes[self.scope_idx]
    }

    #[inline]
    pub fn cur_scope(&self) -> &CompilationScope {
        &self.scopes[self.scope_idx]
    }

    #[inline]
    pub fn cur_instrs_mut(&mut self) -> &mut Vec<Instruction> {
        &mut self.cur_scope_mut().instrs
    }

    #[inline]
    pub fn cur_instrs(&self) -> &Vec<Instruction> {
        &self.cur_scope().instrs
    }
}

#[cfg(test)]
mod compiler_tests {
    use crate::{
        builtin::BUILTIN_FNS,
        lexer::Lexer,
        parser::parser::{Parser, Statement},
    };

    use super::*;

    #[test]
    fn debug() {
        let input = "{ }";
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);

        let program: Vec<Statement> = (&mut parser).collect();

        let mut compiler = Compiler::new();

        let (bytecode, constants, symbol_table) = compiler.compile(&program).unwrap();

        println!("{}", bytecode.to_string());
        dbg!(constants);
        dbg!(symbol_table);
    }

    fn test_cases<'i>(cases: &'i [(&str, (Bytecode, Vec<Object<'i>>))]) {
        for _case @ (input, (instrs_bytes, exp_constants)) in cases {
            let lexer = Lexer::new(input);
            let mut parser = Parser::new(lexer);

            let program: Vec<Statement> = (&mut parser).collect();

            let mut compiler = Compiler::new();

            let (bytecode, constants, symbol_table) = compiler.compile(&program).unwrap();

            assert_eq!(
                instrs_bytes,
                &bytecode,
                "TEST ERROR at case\n
                    \t ({input},\n
                    \t ({instrs_bytes:?},\n
                    \t {exp_constants:?})) \n\n\n
                    \t EXPECTED:\n{}\n\n
                    \t INSTEAD: \n{}",
                instrs_bytes.to_string(),
                bytecode.to_string(),
            );

            for cnt in constants {
                assert!(
                    exp_constants.contains(cnt.as_ref()),
                    "TEST ERROR at case\n
                    \t ({input},\n
                    \t ({instrs_bytes:?},\n
                    \t {exp_constants:?})) \n\n\n
                    {:#?} doesnt contains {:#?}",
                    exp_constants,
                    cnt.as_ref()
                )
            }
        }
    }

    #[test]
    fn integer() {
        let cases = vec![(
            "
                    3;
                    4;
                    9823;
                    23;
                    65537;
                ",
            (
                Bytecode(vec![
                    0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 2, 1, 0, 0, 3, 1, 0, 0, 4, 1,
                ]),
                vec![
                    Object::Integer(3),
                    Object::Integer(4),
                    Object::Integer(9823),
                    Object::Integer(23),
                    Object::Integer(65537),
                ],
            ),
        )];

        test_cases(&cases);
    }

    #[test]
    fn array() {
        let cases = vec![
            (
                "[]",
                (
                    Bytecode::from(vec![(OpCode::Array, vec![0]), (OpCode::Pop, vec![])]),
                    vec![],
                ),
            ),
            (
                "[1, 2, 3]",
                (
                    Bytecode::from(vec![
                        (OpCode::Constant, vec![0]),
                        (OpCode::Constant, vec![1]),
                        (OpCode::Constant, vec![2]),
                        (OpCode::Array, vec![3]),
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![Object::Integer(1), Object::Integer(2), Object::Integer(3)],
                ),
            ),
            (
                "[1 + 2, 3 - 4, 5 * 6]",
                (
                    Bytecode::from(vec![
                        (OpCode::Constant, vec![0]),
                        (OpCode::Constant, vec![1]),
                        (OpCode::Add, vec![]),
                        (OpCode::Constant, vec![2]),
                        (OpCode::Constant, vec![3]),
                        (OpCode::Sub, vec![]),
                        (OpCode::Constant, vec![4]),
                        (OpCode::Constant, vec![5]),
                        (OpCode::Mul, vec![]),
                        (OpCode::Array, vec![3]),
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::Integer(1),
                        Object::Integer(2),
                        Object::Integer(3),
                        Object::Integer(4),
                        Object::Integer(5),
                        Object::Integer(6),
                    ],
                ),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn map() {
        let cases = vec![
            (
                "let m = {}",
                (
                    Bytecode::from(vec![(OpCode::Map, vec![0]), (OpCode::SetGlobal, vec![0])]),
                    vec![],
                ),
            ),
            (
                "let m = { 1: 2, 3: 4, 5: 6 }",
                (
                    Bytecode::from(vec![
                        (OpCode::Constant, vec![0]),
                        (OpCode::Constant, vec![1]),
                        (OpCode::Constant, vec![2]),
                        (OpCode::Constant, vec![3]),
                        (OpCode::Constant, vec![4]),
                        (OpCode::Constant, vec![5]),
                        (OpCode::Map, vec![6]),
                        (OpCode::SetGlobal, vec![0]),
                    ]),
                    vec![
                        Object::Integer(1),
                        Object::Integer(2),
                        Object::Integer(3),
                        Object::Integer(4),
                        Object::Integer(5),
                        Object::Integer(6),
                    ],
                ),
            ),
            (
                "let m = { 1: 2 + 3, 3: 4 * 5, 5 + 9: 6 }",
                (
                    Bytecode::from(vec![
                        (OpCode::Constant, vec![0]),
                        (OpCode::Constant, vec![1]),
                        (OpCode::Constant, vec![2]),
                        (OpCode::Add, vec![]),
                        (OpCode::Constant, vec![3]),
                        (OpCode::Constant, vec![4]),
                        (OpCode::Constant, vec![5]),
                        (OpCode::Mul, vec![]),
                        (OpCode::Constant, vec![6]),
                        (OpCode::Constant, vec![7]),
                        (OpCode::Add, vec![]),
                        (OpCode::Constant, vec![8]),
                        (OpCode::Map, vec![6]),
                        (OpCode::SetGlobal, vec![0]),
                    ]),
                    vec![
                        Object::Integer(1),
                        Object::Integer(2),
                        Object::Integer(3),
                        Object::Integer(4),
                        Object::Integer(5),
                        Object::Integer(6),
                        Object::Integer(9),
                    ],
                ),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn indexing() {
        let cases = vec![
            (
                "[1, 2, 3][5 - 1];",
                (
                    Bytecode::from(vec![
                        (OpCode::Constant, vec![0]),
                        (OpCode::Constant, vec![1]),
                        (OpCode::Constant, vec![2]),
                        (OpCode::Array, vec![3]),
                        (OpCode::Constant, vec![3]),
                        (OpCode::Constant, vec![4]),
                        (OpCode::Sub, vec![4]),
                        (OpCode::Indexing, vec![]),
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::Integer(1),
                        Object::Integer(2),
                        Object::Integer(3),
                        Object::Integer(5),
                        Object::Integer(1),
                    ],
                ),
            ),
            (
                "let m = { 1: 2, 3: 4, 5: 6 }; m[3]",
                (
                    Bytecode::from(vec![
                        (OpCode::Constant, vec![0]),
                        (OpCode::Constant, vec![1]),
                        (OpCode::Constant, vec![2]),
                        (OpCode::Constant, vec![3]),
                        (OpCode::Constant, vec![4]),
                        (OpCode::Constant, vec![5]),
                        (OpCode::Map, vec![6]),
                        (OpCode::SetGlobal, vec![0]),
                        (OpCode::GetGlobal, vec![0]),
                        (OpCode::Constant, vec![6]),
                        (OpCode::Indexing, vec![]),
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::Integer(1),
                        Object::Integer(2),
                        Object::Integer(3),
                        Object::Integer(4),
                        Object::Integer(5),
                        Object::Integer(6),
                        Object::Integer(3),
                    ],
                ),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn strings() {
        let cases = vec![(
            "
                    \"hello\";
                    \"world\";
                ",
            (
                Bytecode::from(vec![
                    (OpCode::Constant, vec![0]),
                    (OpCode::Pop, vec![]),
                    (OpCode::Constant, vec![1]),
                    (OpCode::Pop, vec![]),
                ]),
                vec![
                    Object::String(Cow::from("hello")),
                    Object::String(Cow::from("world")),
                ],
            ),
        )];

        test_cases(&cases);
    }

    #[test]
    fn conditional() {
        let cases = vec![
            (
                "if (true) { 10; } 333;",
                (
                    Bytecode::from(vec![
                        // 0000
                        (OpCode::True, vec![]),
                        // 0001
                        (OpCode::JumpNotTrue, vec![10]),
                        // 0004
                        (OpCode::Constant, vec![0]),
                        // 0007
                        (OpCode::Jump, vec![11]),
                        // 0010
                        (OpCode::Null, vec![]),
                        // 0011
                        (OpCode::Pop, vec![]),
                        // 0012
                        (OpCode::Constant, vec![1]),
                        // 0015
                        (OpCode::Pop, vec![0]),
                    ]),
                    vec![Object::Integer(10), Object::Integer(333)],
                ),
            ),
            (
                "if (true) { 10; } else { 20; } 333;",
                (
                    Bytecode::from(vec![
                        // if
                        //
                        // 0000
                        (OpCode::True, vec![]),
                        // 0001
                        (OpCode::JumpNotTrue, vec![10]),
                        //
                        //yes block
                        //
                        // 0004
                        (OpCode::Constant, vec![0]),
                        // 0007
                        (OpCode::Jump, vec![13]),
                        //
                        // no block
                        //
                        // 0010
                        (OpCode::Constant, vec![1]),
                        //
                        // after whole if stmn
                        //
                        //
                        // Pop for if expression
                        // 0013
                        (OpCode::Pop, vec![]),
                        //
                        // 0014
                        (OpCode::Constant, vec![2]),
                        // 0017
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::Integer(10),
                        Object::Integer(20),
                        Object::Integer(333),
                    ],
                ),
            ),
            (
                "if ((if (false) { true } else { false })) { 10 } else { 20 }",
                (
                    Bytecode::from(vec![
                        (OpCode::False, vec![]),
                        (OpCode::JumpNotTrue, vec![8]),
                        (OpCode::True, vec![]),
                        (OpCode::Jump, vec![9]),
                        (OpCode::False, vec![]),
                        (OpCode::JumpNotTrue, vec![18]),
                        (OpCode::Constant, vec![0]),
                        (OpCode::Jump, vec![21]),
                        (OpCode::Constant, vec![1]),
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![Object::Integer(10), Object::Integer(20)],
                ),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn let_stmn() {
        let cases = vec![
            (
                "let one = 1; let two = one; two;",
                (
                    Bytecode::from(vec![
                        (OpCode::Constant, vec![0]),
                        (OpCode::SetGlobal, vec![0]),
                        (OpCode::GetGlobal, vec![0]),
                        (OpCode::SetGlobal, vec![1]),
                        (OpCode::GetGlobal, vec![1]),
                        (OpCode::Pop, vec![1]),
                    ]),
                    vec![Object::Integer(1)],
                ),
            ),
            (
                "let one = 1; let two = 2; one;",
                (
                    Bytecode::from(vec![
                        (OpCode::Constant, vec![0]),
                        (OpCode::SetGlobal, vec![0]),
                        (OpCode::Constant, vec![1]),
                        (OpCode::SetGlobal, vec![1]),
                        (OpCode::GetGlobal, vec![0]),
                        (OpCode::Pop, vec![1]),
                    ]),
                    vec![Object::Integer(1), Object::Integer(2)],
                ),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn builtins() {
        let cases = vec![
            (
                "len([]); puts([], 1)",
                (
                    Bytecode::from(vec![
                        (OpCode::GetBuiltin, vec![2]),
                        (OpCode::Array, vec![0]),
                        (OpCode::Call, vec![1]),
                        (OpCode::Pop, vec![]),
                        (OpCode::GetBuiltin, vec![3]),
                        (OpCode::Array, vec![0]),
                        (OpCode::Constant, vec![0]),
                        (OpCode::Call, vec![2]),
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![Object::Integer(1)],
                ),
            ),
            (
                "fn() { len([]) }",
                (
                    Bytecode::from(vec![
                        (OpCode::Closure, vec![0, 0]), // fn
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![Object::CompiledFunction {
                        num_args: 0,
                        num_locals: 0,
                        bytecode: Bytecode::from(vec![
                            (OpCode::GetBuiltin, vec![2]),
                            (OpCode::Array, vec![0]),
                            (OpCode::Call, vec![1]),
                            (OpCode::ReturnValue, vec![]),
                        ]),
                    }],
                ),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn functions() {
        let cases = vec![
            (
                "fn() { 5; 1 }",
                (
                    Bytecode::from(vec![
                        (OpCode::Closure, vec![2, 0]), // fn
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::Integer(5),
                        Object::Integer(1),
                        Object::CompiledFunction {
                            num_args: 0,
                            num_locals: 0,
                            bytecode: Bytecode::from(vec![
                                (OpCode::Constant, vec![0]),
                                (OpCode::Pop, vec![]),
                                (OpCode::Constant, vec![1]),
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                    ],
                ),
            ),
            (
                "fn() { }",
                (
                    Bytecode::from(vec![
                        (OpCode::Closure, vec![0, 0]), // fn
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![Object::CompiledFunction {
                        num_args: 0,
                        num_locals: 0,
                        bytecode: Bytecode::from(vec![(OpCode::ReturnNull, vec![])]),
                    }],
                ),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn function_calls() {
        let cases = vec![
            (
                "let num = 2; fn() { num; }",
                (
                    Bytecode::from(vec![
                        (OpCode::Constant, vec![0]),
                        (OpCode::SetGlobal, vec![0]),
                        (OpCode::Closure, vec![1, 0]), // fn
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::Integer(2),
                        Object::CompiledFunction {
                            num_args: 0,
                            num_locals: 0,
                            bytecode: Bytecode::from(vec![
                                (OpCode::GetGlobal, vec![0]),
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                    ],
                ),
            ),
            (
                "fn() { 24 }()",
                (
                    Bytecode::from(vec![
                        (OpCode::Closure, vec![1, 0]), // fn
                        (OpCode::Call, vec![0]),
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::Integer(24),
                        Object::CompiledFunction {
                            num_args: 0,
                            num_locals: 0,
                            bytecode: Bytecode::from(vec![
                                (OpCode::Constant, vec![0]),
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                    ],
                ),
            ),
            (
                "
                    let noArgs = fn() { 5 + 10 };
                    noArgs();
                ",
                (
                    Bytecode::from(vec![
                        (OpCode::Closure, vec![2, 0]),
                        (OpCode::SetGlobal, vec![0]),
                        (OpCode::GetGlobal, vec![0]),
                        (OpCode::Call, vec![0]),
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::Integer(5),
                        Object::Integer(10),
                        Object::CompiledFunction {
                            num_args: 0,
                            num_locals: 0,
                            bytecode: Bytecode::from(vec![
                                (OpCode::Constant, vec![0]),
                                (OpCode::Constant, vec![1]),
                                (OpCode::Add, vec![]),
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                    ],
                ),
            ),
            (
                "
                    let oneArgNoBody = fn(a) {  };
                    oneArgNoBody(10);
                ",
                (
                    Bytecode::from(vec![
                        (OpCode::Closure, vec![0, 0]), // fn
                        (OpCode::SetGlobal, vec![0]),  // let oneArg... =
                        (OpCode::GetGlobal, vec![0]),  // oneArg..
                        (OpCode::Constant, vec![1]),   // 10
                        (OpCode::Call, vec![1]),       // oneArg(10)
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::CompiledFunction {
                            num_args: 1,
                            num_locals: 1,
                            bytecode: Bytecode::from(vec![(OpCode::ReturnNull, vec![])]),
                        },
                        Object::Integer(10),
                    ],
                ),
            ),
            (
                "
                    let manyArgsNoBody = fn(a, b, c) {  };
                    manyArgsNoBody(10, 11, 12);
                ",
                (
                    Bytecode::from(vec![
                        (OpCode::Closure, vec![0, 0]), // fn
                        (OpCode::SetGlobal, vec![0]),  // let many.. =
                        (OpCode::GetGlobal, vec![0]),  // many..
                        (OpCode::Constant, vec![1]),   // 10
                        (OpCode::Constant, vec![2]),   // 11
                        (OpCode::Constant, vec![3]),   // 12
                        (OpCode::Call, vec![3]),       // many...(10, 11, 12)
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::CompiledFunction {
                            num_args: 3,
                            num_locals: 3,
                            bytecode: Bytecode::from(vec![(OpCode::ReturnNull, vec![])]),
                        },
                        Object::Integer(10),
                        Object::Integer(11),
                        Object::Integer(12),
                    ],
                ),
            ),
            (
                "
                    let oneArg = fn(a) { a + 10 };
                    oneArg(12);
                ",
                (
                    Bytecode::from(vec![
                        (OpCode::Closure, vec![1, 0]), // fn
                        (OpCode::SetGlobal, vec![0]),  // let oneArg =
                        (OpCode::GetGlobal, vec![0]),  // oneArg
                        (OpCode::Constant, vec![2]),   // 12
                        (OpCode::Call, vec![1]),       // oneArg(12)
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::Integer(10),
                        Object::CompiledFunction {
                            num_args: 1,
                            num_locals: 1,
                            bytecode: Bytecode::from(vec![
                                (OpCode::GetLocal, vec![0]),
                                (OpCode::Constant, vec![0]),
                                (OpCode::Add, vec![]),
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                        Object::Integer(12),
                    ],
                ),
            ),
            (
                "
                    let manyArgs = fn(a, b, c) { a; b; c;  };
                    manyArgs(10, 11, 12);
                ",
                (
                    Bytecode::from(vec![
                        (OpCode::Closure, vec![0, 0]), // fn
                        (OpCode::SetGlobal, vec![0]),  // let manyArgs =
                        (OpCode::GetGlobal, vec![0]),  // manyArgs
                        (OpCode::Constant, vec![1]),   // 10
                        (OpCode::Constant, vec![2]),   // 11
                        (OpCode::Constant, vec![3]),   // 12
                        (OpCode::Call, vec![3]),       // manyArgs(10, 11, 12)
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::CompiledFunction {
                            num_args: 3,
                            num_locals: 3,
                            bytecode: Bytecode::from(vec![
                                (OpCode::GetLocal, vec![0]),
                                (OpCode::Pop, vec![]),
                                (OpCode::GetLocal, vec![1]),
                                (OpCode::Pop, vec![]),
                                (OpCode::GetLocal, vec![2]),
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                        Object::Integer(10),
                        Object::Integer(11),
                        Object::Integer(12),
                    ],
                ),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn closures_with_free_vars() {
        let cases = vec![
            (
                "fn(a) { fn(b) { a + b; } }",
                (
                    Bytecode::from(vec![
                        (OpCode::Closure, vec![1, 0]), // fn(a)
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::CompiledFunction {
                            num_args: 1,
                            num_locals: 1,
                            // body of fn(b)
                            bytecode: Bytecode::from(vec![
                                (OpCode::GetFree, vec![0]),
                                (OpCode::GetLocal, vec![0]),
                                (OpCode::Add, vec![]),
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                        Object::CompiledFunction {
                            num_args: 1,
                            num_locals: 1,
                            // body of fn(a)
                            bytecode: Bytecode::from(vec![
                                (OpCode::GetLocal, vec![0]),
                                (OpCode::Closure, vec![0, 1]),
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                    ],
                ),
            ),
            (
                "fn(a) { fn(b) { fn(c) { a + b + c; } } };",
                (
                    Bytecode::from(vec![
                        (OpCode::Closure, vec![2, 0]), // fn(a)
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::CompiledFunction {
                            num_args: 1,
                            num_locals: 1,
                            // body of fn(c)
                            bytecode: Bytecode::from(vec![
                                (OpCode::GetFree, vec![0]),  // a
                                (OpCode::GetFree, vec![1]),  // b
                                (OpCode::Add, vec![]),       // a + b
                                (OpCode::GetLocal, vec![0]), // c
                                (OpCode::Add, vec![]),       // (a + b) + c
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                        Object::CompiledFunction {
                            num_args: 1,
                            num_locals: 1,
                            // body of fn(b)
                            bytecode: Bytecode::from(vec![
                                (OpCode::GetFree, vec![0]),    // a
                                (OpCode::GetLocal, vec![0]),   // b
                                (OpCode::Closure, vec![0, 2]), // fn(c)
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                        Object::CompiledFunction {
                            num_args: 1,
                            num_locals: 1,
                            // body of fn(a)
                            bytecode: Bytecode::from(vec![
                                (OpCode::GetLocal, vec![0]),   // a
                                (OpCode::Closure, vec![1, 1]), // fn(b)
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                    ],
                ),
            ),
            (
                "
                    let global = 55;
                    fn() { 
                        let a = 66; 

                        fn() {
                            let b = 77;

                            fn() {
                                let c = 88;

                                global + a + b + c;
                            } 
                        }
                    };",
                (
                    Bytecode::from(vec![
                        (OpCode::Constant, vec![0]),  // 66
                        (OpCode::SetGlobal, vec![0]), // let a =
                        (OpCode::Closure, vec![6, 0]),
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::Integer(55),
                        Object::Integer(66),
                        Object::Integer(77),
                        Object::Integer(88),
                        Object::CompiledFunction {
                            num_args: 0,
                            num_locals: 1,
                            // body of fn(c)
                            bytecode: Bytecode::from(vec![
                                (OpCode::Constant, vec![3]),  // 88
                                (OpCode::SetLocal, vec![0]),  // let c
                                (OpCode::GetGlobal, vec![0]), // global
                                (OpCode::GetFree, vec![0]),   // a
                                (OpCode::Add, vec![]),        // global + a
                                (OpCode::GetFree, vec![1]),   // b
                                (OpCode::Add, vec![]),        // (global + a) + b
                                (OpCode::GetLocal, vec![0]),  // c
                                (OpCode::Add, vec![]),        // (global + a + b) + c
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                        Object::CompiledFunction {
                            num_args: 0,
                            num_locals: 1,
                            // body of fn(b)
                            bytecode: Bytecode::from(vec![
                                (OpCode::Constant, vec![2]),   // 77
                                (OpCode::SetLocal, vec![0]),   // let b
                                (OpCode::GetFree, vec![0]),    // ?
                                (OpCode::GetLocal, vec![0]),   // b
                                (OpCode::Closure, vec![4, 2]), // fn(c)
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                        Object::CompiledFunction {
                            num_args: 0,
                            num_locals: 1,
                            // body of fn(a)
                            bytecode: Bytecode::from(vec![
                                (OpCode::Constant, vec![1]),   // 66
                                (OpCode::SetLocal, vec![0]),   // let a
                                (OpCode::GetLocal, vec![0]),   // ?
                                (OpCode::Closure, vec![5, 1]), // fn(b)
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                    ],
                ),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn recursive_closures() {
        let cases = vec![
            (
                "
                    let countDown = fn(x) { countDown(x - 1); };
                    countDown(11);
                ",
                (
                    Bytecode::from(vec![
                        (OpCode::Closure, vec![1, 0]),
                        (OpCode::SetGlobal, vec![0]),
                        (OpCode::GetGlobal, vec![0]),
                        (OpCode::Constant, vec![2]),
                        (OpCode::Call, vec![1]),
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::Integer(1),
                        Object::CompiledFunction {
                            num_args: 1,
                            num_locals: 1,
                            bytecode: Bytecode::from(vec![
                                (OpCode::CurrentClosure, vec![]),
                                (OpCode::GetLocal, vec![0]),
                                (OpCode::Constant, vec![0]),
                                (OpCode::Sub, vec![]),
                                (OpCode::Call, vec![1]),
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                        Object::Integer(11),
                    ],
                ),
            ),
            (
                "
                    let wrapper = fn() {
                        let countDown = fn(x) { countDown(x - 1); };
                        countDown(11);
                    };

                    wrapper();
                ",
                (
                    Bytecode::from(vec![
                        (OpCode::Closure, vec![3, 0]),
                        (OpCode::SetGlobal, vec![0]),
                        (OpCode::GetGlobal, vec![0]),
                        (OpCode::Call, vec![0]),
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::Integer(1),
                        Object::CompiledFunction {
                            num_args: 1,
                            num_locals: 1,
                            bytecode: Bytecode::from(vec![
                                (OpCode::CurrentClosure, vec![]),
                                (OpCode::GetLocal, vec![0]),
                                (OpCode::Constant, vec![0]),
                                (OpCode::Sub, vec![]),
                                (OpCode::Call, vec![1]),
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                        Object::Integer(11),
                        Object::CompiledFunction {
                            num_args: 0,
                            num_locals: 1,
                            bytecode: Bytecode::from(vec![
                                (OpCode::Closure, vec![1, 0]),
                                (OpCode::SetLocal, vec![0]),
                                (OpCode::GetLocal, vec![0]),
                                (OpCode::Constant, vec![2]),
                                (OpCode::Call, vec![1]),
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                    ],
                ),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn let_stmnt_scopes() {
        let cases = vec![
            (
                "let num = 34; fn() { num; }",
                (
                    Bytecode::from(vec![
                        (OpCode::Constant, vec![0]),   // 34
                        (OpCode::SetGlobal, vec![0]),  // let num =
                        (OpCode::Closure, vec![1, 0]), // fn(), 0 free variables because num is global
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::Integer(34),
                        Object::CompiledFunction {
                            num_args: 0,
                            num_locals: 0,
                            bytecode: Bytecode::from(vec![
                                (OpCode::GetGlobal, vec![0]),
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                    ],
                ),
            ),
            (
                "fn() { let num = 3; num; }",
                (
                    Bytecode::from(vec![
                        (OpCode::Closure, vec![1, 0]), // fn
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::Integer(3),
                        Object::CompiledFunction {
                            num_args: 0,
                            num_locals: 1,
                            bytecode: Bytecode::from(vec![
                                (OpCode::Constant, vec![0]),
                                (OpCode::SetLocal, vec![0]),
                                (OpCode::GetLocal, vec![0]),
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                    ],
                ),
            ),
            (
                "fn() { let a = 3; let b = 4; a + b; }",
                (
                    Bytecode::from(vec![
                        (OpCode::Closure, vec![2, 0]), //fn
                        (OpCode::Pop, vec![]),
                    ]),
                    vec![
                        Object::Integer(3),
                        Object::Integer(4),
                        Object::CompiledFunction {
                            num_args: 0,
                            num_locals: 2,
                            bytecode: Bytecode::from(vec![
                                (OpCode::Constant, vec![0]),
                                (OpCode::SetLocal, vec![0]),
                                (OpCode::Constant, vec![1]),
                                (OpCode::SetLocal, vec![1]),
                                (OpCode::GetLocal, vec![0]),
                                (OpCode::GetLocal, vec![1]),
                                (OpCode::Add, vec![]),
                                (OpCode::ReturnValue, vec![]),
                            ]),
                        },
                    ],
                ),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn globals() {
        let cases = vec![
            (
                "let one = 1; let two = one; two;",
                (
                    Bytecode::from(vec![
                        (OpCode::Constant, vec![0]),
                        (OpCode::SetGlobal, vec![0]),
                        (OpCode::GetGlobal, vec![0]),
                        (OpCode::SetGlobal, vec![1]),
                        (OpCode::GetGlobal, vec![1]),
                        (OpCode::Pop, vec![1]),
                    ]),
                    vec![Object::Integer(1)],
                ),
            ),
            (
                "let one = 1; let two = 2; one;",
                (
                    Bytecode::from(vec![
                        (OpCode::Constant, vec![0]),
                        (OpCode::SetGlobal, vec![0]),
                        (OpCode::Constant, vec![1]),
                        (OpCode::SetGlobal, vec![1]),
                        (OpCode::GetGlobal, vec![0]),
                        (OpCode::Pop, vec![1]),
                    ]),
                    vec![Object::Integer(1), Object::Integer(2)],
                ),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn compilation_scopes() {
        let mut compiler = Compiler::new();
        assert_eq!(compiler.scope_idx, 0);

        let global_symbol_table = Rc::clone(&compiler.symbol_table);
        global_symbol_table.borrow_mut().define("global_test");

        compiler.add_instr(OpCode::Mul, vec![]);

        compiler.enter_scope();
        assert_eq!(compiler.scope_idx, 1);

        compiler.add_instr(OpCode::Sub, vec![]);
        assert_eq!(compiler.cur_scope().instrs.len(), 1);
        assert_eq!(
            *compiler.cur_scope().instrs.last().unwrap(),
            (OpCode::Sub, Operands::Raw(vec![]))
        );

        assert_eq!(
            compiler.symbol_table.borrow().outer.as_ref().unwrap(),
            &global_symbol_table
        );

        compiler.leave_scope();
        assert_eq!(compiler.scope_idx, 0);

        assert_eq!(compiler.symbol_table, global_symbol_table);

        compiler.add_instr(OpCode::Add, vec![]);

        assert_eq!(compiler.cur_scope().instrs.len(), 2);
        assert_eq!(
            *compiler.cur_scope().instrs.last().unwrap(),
            (OpCode::Add, Operands::Raw(vec![]))
        );

        assert_eq!(
            compiler.cur_scope().instrs.last_chunk::<2>().unwrap()[0],
            (OpCode::Mul, Operands::Raw(vec![]))
        );
    }
}
