use std::{borrow::Cow, cell::Cell, collections::HashMap, mem, rc::Rc};

use crate::{
    builtin::BUILTIN_FNS,
    lexer::Lexer,
    monke_error::MonkeError,
    object::Object,
    parser::parser::{Parser, Statement},
    vm::{
        bytecode::Bytecode,
        op_code::{
            meta::OperandWidth,
            op_code::{OP_CODE_LEN, OpCode},
        },
    },
};

use super::{compiler::Compiler, frame::Frame};

pub fn run_vm_on_input<'i>(input: &'i str) -> Result<Rc<Object<'i>>, MonkeError> {
    let lexer = Lexer::new(&input);
    let mut parser = Parser::new(lexer);
    let mut compiler = Compiler::new();

    let program: Vec<Statement> = (&mut parser).collect();

    assert_eq!(parser.errors, Vec::<String>::new());

    let (bytecode, constants, _) = compiler.compile(&program).unwrap();

    let mut vm = VM::new(bytecode, constants);

    let result = vm.run().inspect_err(|err| eprintln!("{err}"));

    return result;
}

pub const STACK_SIZE: usize = 2048;
pub const GLOBALS_SIZE: usize = 65536;
pub const MAX_FRAMES: usize = 1024;

#[derive(Debug, Clone, PartialEq)]
pub struct VM<'i> {
    pub constants: Vec<Rc<Object<'i>>>,

    pub globals: Vec<Rc<Object<'i>>>,

    pub stack: Vec<Rc<Object<'i>>>,
    pub sp: usize,

    pub frames: Vec<Frame<'i>>,
    pub frame_idx: usize,
}

impl<'i> VM<'i> {
    pub fn new(bytecode: Bytecode, constants: Vec<Rc<Object<'i>>>) -> Self {
        let mut frames = vec![
            Frame::new(
                Rc::new(Object::Closure {
                    cfn: Rc::new(Object::CompiledFunction {
                        bytecode: Bytecode(vec![]),
                        num_locals: 0,
                        num_args: 0
                    }),
                    free_vars: vec![]
                }),
                0
            );
            MAX_FRAMES
        ];

        let main_fn = Rc::new(Object::CompiledFunction {
            bytecode,
            num_locals: 0,
            num_args: 0,
        });

        let main_closure = Rc::new(Object::Closure {
            cfn: main_fn,
            free_vars: vec![],
        });

        frames[0] = Frame::new(main_closure, 0);

        Self {
            constants,
            globals: vec![Rc::new(Object::Integer(0)); GLOBALS_SIZE],
            stack: vec![Rc::new(Object::Integer(0)); STACK_SIZE],
            sp: 0,
            frames,
            frame_idx: 1,
        }
    }

    pub fn new_with_globals_store(
        bytecode: Bytecode,
        constants: Vec<Rc<Object<'i>>>,
        globals: Vec<Rc<Object<'i>>>,
    ) -> Self {
        let mut vm = Self::new(bytecode, constants);

        vm.globals = globals;

        vm
    }

    pub fn run(&mut self) -> Result<Rc<Object<'i>>, MonkeError> {
        loop {
            let (bytecode, _, ip, _) = self.cur_frame_inner();

            if ip.get() >= bytecode.len() {
                break;
            }

            let op_code = {
                let op_code_byte = bytecode[ip.get()];
                ip.set(ip.get() + OP_CODE_LEN);

                OpCode::try_from(op_code_byte).or_else(|_| {
                    MonkeError::new(&format!(
                        "no candidate for OpCode exists for byte {op_code_byte}",
                    ))
                    .into()
                })?
            };

            match op_code {
                OpCode::CurrentClosure => {
                    let Frame { closure, .. } = self.cur_frame();
                    self.push(Rc::clone(closure));
                }

                OpCode::Closure => {
                    let const_idx = self.read_operand(bytecode, ip, OperandWidth::TwoBytes);
                    let num_free_vars = self.read_operand(bytecode, ip, OperandWidth::OneByte);

                    let cfn = {
                        let compiled_fn = &self.constants[const_idx];

                        assert!(matches!(
                            compiled_fn.as_ref(),
                            Object::CompiledFunction { .. }
                        ));

                        Rc::clone(compiled_fn)
                    };

                    let free_vars = self.stack[self.sp - num_free_vars..self.sp]
                        .iter()
                        .map(Rc::clone)
                        .collect();

                    self.sp = self.sp - num_free_vars;

                    let closure = Rc::new(Object::Closure { cfn, free_vars });

                    self.push(closure)?;
                }

                OpCode::Call => {
                    let num_args = self.read_operand(bytecode, ip, OperandWidth::OneByte);

                    let callable = Rc::clone(&self.stack[self.sp - num_args - 1]); // callable placed before args, thats why - 1

                    match callable.as_ref() {
                        Object::Closure { cfn, .. } => {
                            let (num_locals, exp_num_args) = match cfn.as_ref() {
                                Object::CompiledFunction {
                                    num_locals,
                                    num_args: exp_num_args,
                                    ..
                                } => (*num_locals, *exp_num_args),

                                _ => panic!(
                                    "Object::Closure.cfn should contain Object::CompiledFunction, instead got {cfn:?}"
                                ),
                            };

                            if exp_num_args != num_args {
                                return MonkeError::new(format!(
                                    "Wrong number of arguments: want={exp_num_args}, got={num_args}"
                                ))
                                .into();
                            }

                            let first_arg_idx = self.sp - num_args;
                            let frame = Frame::new(callable, first_arg_idx);
                            self.push_frame(frame);

                            self.sp = first_arg_idx + num_locals; // num_args counted inside num_locals
                        }

                        Object::Builtin(bfn) => {
                            let args: Vec<Rc<Object<'i>>> = self.stack[self.sp - num_args..self.sp]
                                .iter()
                                .map(Rc::clone)
                                .collect();

                            let res = bfn(args)?;

                            self.sp = self.sp - 1 - num_args;

                            self.push(res);
                        }

                        obj => return MonkeError::new(format!("Cannot call {obj:?}")).into(),
                    };
                }

                OpCode::ReturnValue => {
                    let return_value = self.pop()?;

                    let poped_frame = self.pop_frame();
                    self.sp = poped_frame.base_pointer.get() - 1; // extra -1 to get rid of Object::Closure

                    self.push(return_value)?;
                }

                OpCode::ReturnNull => {
                    let poped_frame = self.pop_frame();
                    self.sp = poped_frame.base_pointer.get() - 1; // extra -1 to get rid of Object::Closure

                    self.push(Rc::new(Object::Null))?;
                }

                OpCode::Constant => {
                    let const_index = self.read_operand(bytecode, ip, OperandWidth::TwoBytes);
                    let constant = self.constants.get(const_index).ok_or_else(|| {
                        MonkeError::new(format!(
                            "No constant with index {const_index} was found in {:?}",
                            self.constants
                        ))
                    })?;

                    self.push(Rc::clone(constant))?;
                }

                OpCode::Array => {
                    let array_len = self.read_operand(bytecode, ip, OperandWidth::TwoBytes);

                    let elements = self.stack[self.sp - array_len..self.sp]
                        .iter()
                        .map(Rc::clone)
                        .collect();

                    self.sp -= array_len;

                    self.push(Rc::new(Object::Array(elements)))?;
                }

                OpCode::Map => {
                    let key_values_len = self.read_operand(bytecode, ip, OperandWidth::TwoBytes);
                    if key_values_len % 2 != 0 {
                        return MonkeError::new(format!(
                            "Cannot construct Object::Map with odd number of key_values_len"
                        ))
                        .into();
                    }

                    let map = self.stack[self.sp - key_values_len..self.sp]
                        .chunks(2)
                        .map(|key_value| match key_value {
                            [key, value] => (key.as_ref().clone(), Rc::clone(value)),

                            _ => unreachable!("iterating with chunks(2)"),
                        })
                        .collect();

                    self.sp -= key_values_len;

                    self.push(Rc::new(Object::Map(map)))?;
                }

                OpCode::Indexing => {
                    let (index, left) = (self.pop()?, self.pop()?);

                    let elem = match (left.as_ref(), index.as_ref()) {
                        (Object::Array(elements), Object::Integer(index)) => {
                            match elements.get(*index as usize) {
                                Some(obj) => Rc::clone(obj),
                                None => Rc::new(Object::Null),
                            }
                        }

                        (Object::Map(map), index @ (Object::Integer(_) | Object::String(_))) => {
                            match map.get(index) {
                                Some(obj) => Rc::clone(obj),
                                None => Rc::new(Object::Null),
                            }
                        }

                        (left, index) => panic!("Index = {index} not supported for {left}"),
                    };

                    self.push(elem)?
                }

                // prefix
                OpCode::Bang | OpCode::Minus => {
                    let right = self.pop()?;

                    let result = match (op_code, right.as_ref()) {
                        (OpCode::Bang, Object::Bool(value)) => Object::Bool(!value),
                        (OpCode::Minus, Object::Integer(value)) => Object::Integer(-value),
                        (OpCode::Minus, Object::Float(value)) => Object::Float(-value),

                        (op_code, right) => {
                            return MonkeError::new(format!(
                                "op = {op_code:?} not implemented for {right:?}",
                            ))
                            .into();
                        }
                    };

                    self.push(Rc::new(result))?;
                }

                OpCode::Add
                | OpCode::Sub
                | OpCode::Div
                | OpCode::Mul
                | OpCode::GreaterEqual
                | OpCode::Greater
                | OpCode::Equal
                | OpCode::NotEqual => {
                    use Object::*;
                    use OpCode::*;

                    let (right, left) = (self.pop()?, self.pop()?);

                    #[rustfmt::skip]
                    let result = match (op_code, left.as_ref(), right.as_ref()) {

                        (Equal,        Bool(left),    Bool(right))    => Bool(left == right),
                        (NotEqual,     Bool(left),    Bool(right))    => Bool(left != right),

                        (Add,          Integer(left), Integer(right)) => Integer(left + right),
                        (Sub,          Integer(left), Integer(right)) => Integer(left - right),
                        (Mul,          Integer(left), Integer(right)) => Integer(left * right),
                        (Div,          Integer(left), Integer(right)) => Integer(left / right),
                        (GreaterEqual, Integer(left), Integer(right)) => Bool(left >= right),
                        (Greater,      Integer(left), Integer(right)) => Bool(left > right),
                        (Equal,        Integer(left), Integer(right)) => Bool(left == right),
                        (NotEqual,     Integer(left), Integer(right)) => Bool(left != right),


                        (Add,          Float(left),   Float(right))   => Float(left + right),
                        (Sub,          Float(left),   Float(right))   => Float(left - right),
                        (Mul,          Float(left),   Float(right))   => Float(left * right),
                        (Div,          Float(left),   Float(right))   => Float(left / right),
                        (GreaterEqual, Float(left),   Float(right))   => Bool(left >= right),
                        (Greater,      Float(left),   Float(right))   => Bool(left > right),
                        (Equal,        Float(left),   Float(right))   => Bool(left == right),
                        (NotEqual,     Float(left),   Float(right))   => Bool(left != right),


                        (Add,          String(left),  String(right))  => String(Cow::from(left.to_string() + right)),
                        (GreaterEqual, String(left),  String(right))  => Bool(left >= right),
                        (Greater,      String(left),  String(right))  => Bool(left > right),
                        (Equal,        String(left),  String(right))  => Bool(left == right),
                        (NotEqual,     String(left),  String(right))  => Bool(left != right),


                        (op_code, left, right) => return MonkeError::new(format!(
                            "op = {op_code:?} not implemented for {left:?} and {right:?}"
                        )).into(),

                    };

                    self.push(Rc::new(result))?;
                }

                OpCode::True => {
                    self.push(Rc::new(Object::Bool(true)))?;
                }

                OpCode::False => {
                    self.push(Rc::new(Object::Bool(false)))?;
                }

                OpCode::JumpNotTrue => {
                    let cond_res = self.pop_expect(|got| matches!(got, Object::Bool(_)))?;
                    // reinitialize to allow borrow &mut self to get `cond_res`
                    let (bytecode, _, ip, _) = self.cur_frame_inner();

                    let address = self.read_operand(bytecode, ip, OperandWidth::TwoBytes);

                    if let Object::Bool(false) = cond_res.as_ref() {
                        ip.set(address);
                    }
                }

                OpCode::Jump => {
                    let address = self.read_operand(bytecode, ip, OperandWidth::TwoBytes);
                    ip.set(address);
                }

                OpCode::Pop => {
                    self.pop()?;
                }

                OpCode::SetGlobal => {
                    let global_idx = self.read_operand(bytecode, ip, OperandWidth::TwoBytes);
                    self.globals[global_idx] = self.pop()?;
                }

                OpCode::GetGlobal => {
                    let global_idx = self.read_operand(bytecode, ip, OperandWidth::TwoBytes);
                    let global = &self.globals[global_idx];
                    self.push(Rc::clone(global))?;
                }

                OpCode::SetLocal => {
                    let local_idx = self.read_operand(bytecode, ip, OperandWidth::OneByte);

                    let (_, _, _, base_pointer) = self.cur_frame_inner();
                    let base_pointer = base_pointer.get();

                    self.stack[base_pointer + local_idx] = self.pop()?;
                }

                OpCode::GetLocal => {
                    let local_idx = self.read_operand(bytecode, ip, OperandWidth::OneByte);

                    let (_, _, _, base_pointer) = self.cur_frame_inner();
                    let base_pointer = base_pointer.get();

                    let obj = Rc::clone(&self.stack[base_pointer + local_idx]);

                    self.push(obj)?;
                }

                OpCode::GetBuiltin => {
                    let builtin_idx = self.read_operand(bytecode, ip, OperandWidth::OneByte);

                    let (_, (_, bfn)) = BUILTIN_FNS
                        .iter()
                        .enumerate()
                        .find(|(idx, _)| *idx == builtin_idx)
                        .expect("can't find builtin");

                    self.push(Rc::new(Object::Builtin(*bfn)))?;
                }

                OpCode::GetFree => {
                    let free_idx = self.read_operand(bytecode, ip, OperandWidth::OneByte);

                    let (_, free_vars, _, _) = self.cur_frame_inner();

                    self.push(Rc::clone(&free_vars[free_idx]));
                }

                OpCode::Null => {
                    self.push(Rc::new(Object::Null))?;
                }
            }
        }

        Ok(Rc::clone(&self.stack[self.sp]))
    }

    #[inline]
    fn read_operand(&self, bytecode: &Bytecode, ip: &Cell<usize>, width: OperandWidth) -> usize {
        let bytes_slice = &bytecode[ip.get()..ip.get() + width as usize];
        ip.set(ip.get() + width as usize);

        match width {
            OperandWidth::OneByte => {
                u8::from_be_bytes(bytes_slice.try_into().expect("can't convert into arr")) as usize
            }

            OperandWidth::TwoBytes => {
                u16::from_be_bytes(bytes_slice.try_into().expect("can't convert into arr")) as usize
            }
        }
    }

    #[inline]
    fn push(&mut self, obj: Rc<Object<'i>>) -> Result<(), MonkeError> {
        if self.sp >= STACK_SIZE {
            return MonkeError::new("Stack Overflow dubra").into();
        }

        self.stack[self.sp] = obj;
        self.sp += 1;

        Ok(())
    }

    #[inline]
    fn pop(&mut self) -> Result<Rc<Object<'i>>, MonkeError> {
        if self.sp == 0 {
            return MonkeError::new("Stack is empty").into();
        }

        let obj = Rc::clone(&self.stack[self.sp - 1]);
        self.sp -= 1;

        Ok(obj)
    }

    #[inline]
    fn pop_expect(
        &mut self,
        check: impl Fn(&Object<'i>) -> bool,
    ) -> Result<Rc<Object<'i>>, MonkeError> {
        if self.sp == 0 {
            return MonkeError::new("Stack is empty").into();
        }

        let obj = Rc::clone(&self.stack[self.sp - 1]);

        if !check(obj.as_ref()) {
            return MonkeError::new(format!("check fn returned false for {obj:?}")).into();
        }

        self.sp -= 1;

        Ok(obj)
    }

    #[inline]
    fn cur_frame_inner(&self) -> (&Bytecode, &Vec<Rc<Object<'i>>>, &Cell<usize>, &Cell<usize>) {
        self.frames[self.frame_idx - 1].get_inner()
    }

    #[inline]
    fn cur_frame(&self) -> &Frame<'i> {
        &self.frames[self.frame_idx - 1]
    }

    #[inline]
    fn push_frame(&mut self, frame: Frame<'i>) -> usize {
        self.frames[self.frame_idx] = frame;
        self.frame_idx += 1;
        self.frame_idx
    }

    #[inline]
    fn pop_frame(&mut self) -> &Frame<'i> {
        self.frame_idx -= 1;
        &self.frames[self.frame_idx]
    }
}

#[cfg(test)]
mod vm_tests {
    use std::{collections::HashMap, time::Instant};

    use crate::{
        lexer::Lexer,
        object::Object,
        parser::parser::{Parser, Statement},
        vm::compiler::Compiler,
    };

    use super::*;

    fn test_cases<'i>(cases: &'i [(&'i str, Object<'i>)]) {
        let tim = Instant::now();

        for case @ (input, exp_res) in cases {
            let input = input.as_ref();
            let lexer = Lexer::new(input);
            let mut parser = Parser::new(lexer);
            let mut compiler = Compiler::new();

            let program: Vec<Statement> = (&mut parser).collect();

            assert_eq!(parser.errors, Vec::<String>::new());

            let (bytecode, constants, _) = compiler.compile(&program).unwrap();

            let mut vm = VM::new(bytecode, constants);

            let res = vm.run().unwrap();

            assert_eq!(vm.frame_idx, 1);

            assert_eq!(
                res.as_ref(),
                exp_res,
                "TEST ERROR at case\n
                    \t ({input},
                    \t {exp_res:?})\n\n
                    \t vm.sp = {:?},
                    \t vm.stack[..20] = {:?}\n\n
                ",
                vm.sp,
                &vm.stack[..20],
            );
        }

        dbg!(tim.elapsed());
    }

    fn test_cases_to_fail<'i>(cases: &'i [(&'i str, MonkeError)]) {
        let tim = Instant::now();

        for _case @ (input, exp_err) in cases {
            let input = input.as_ref();
            let lexer = Lexer::new(input);
            let mut parser = Parser::new(lexer);
            let mut compiler = Compiler::new();

            let program: Vec<Statement> = (&mut parser).collect();

            let (bytecode, constants, _) = compiler.compile(&program).unwrap();

            let mut vm = VM::new(bytecode, constants);

            let err = match vm.run() {
                Err(err) => err,
                Ok(_) => panic!("expected vm.run() to return Err(MonkeError), instead got Ok(())"),
            };

            assert_eq!(&err, exp_err);
        }

        dbg!(tim.elapsed());
    }

    #[test]
    fn integer_arithmetic() {
        // let case_100 = ["1"; 12000].join(" + ");
        //
        // dbg!(&case_100);
        let cases = vec![
            ("-2;", Object::Integer(-2)),
            ("1; 2;", Object::Integer(2)),
            ("2;", Object::Integer(2)),
            ("100 + 245;", Object::Integer(345)),
            ("100 + 245 + 3;", Object::Integer(348)),
            ("100 * 245;", Object::Integer(24500)),
            ("10 / 5;", Object::Integer(2)),
            ("10 / 245;", Object::Integer(0)),
            ("100 - 245;", Object::Integer(-145)),
            ("100 - 245;", Object::Integer(-145)),
            ("(4 * 3) - 2;", Object::Integer(10)),
            ("4 * 3 - 2;", Object::Integer(10)),
            ("4 * (3 - 2);", Object::Integer(4)),
            ("4 * (3 - -2);", Object::Integer(20)),
            // (&case_100, Object::Integer(348)),
        ];

        test_cases(&cases);
    }

    #[test]
    fn booleans() {
        let cases = vec![
            ("!true", Object::Bool(false)),
            ("!!true", Object::Bool(true)),
            ("!false", Object::Bool(true)),
            ("!!false", Object::Bool(false)),
            ("1 < 2", Object::Bool(true)),
            ("1 > 2", Object::Bool(false)),
            ("1 < 1", Object::Bool(false)),
            ("1 > 1", Object::Bool(false)),
            ("1 == 1", Object::Bool(true)),
            ("1 != 1", Object::Bool(false)),
            ("1 == 2", Object::Bool(false)),
            ("1 != 2", Object::Bool(true)),
            ("true == true", Object::Bool(true)),
            ("false == false", Object::Bool(true)),
            ("true == false", Object::Bool(false)),
            ("true != false", Object::Bool(true)),
            ("false != true", Object::Bool(true)),
            ("(1 < 2) == true", Object::Bool(true)),
            ("(1 < 2) == false", Object::Bool(false)),
            ("(1 > 2) == true", Object::Bool(false)),
            ("(1 > 2) == false", Object::Bool(true)),
        ];

        test_cases(&cases);
    }

    #[test]
    fn if_else() {
        let cases = vec![
            ("if (true) { 10 }", Object::Integer(10)),
            ("if (true) { 10 } else { 20 }", Object::Integer(10)),
            ("if (false) { 10 } else { 20 } ", Object::Integer(20)),
            ("if (1 == 1) { 10 }", Object::Integer(10)),
            ("if (1 < 2) { 10 }", Object::Integer(10)),
            ("if (1 < 2) { 10 } else { 20 }", Object::Integer(10)),
            ("if (1 > 2) { 10 } else { 20 }", Object::Integer(20)),
            ("if (false) { 10 }", Object::Null),
            (
                "if ((if (false) { true } else { false })) { 10 } else { 20 }",
                Object::Integer(20),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn let_stmn() {
        let cases = vec![
            (
                "let x = 5 * 5; if (x > 10) { let y = x * 2; y; }",
                Object::Integer(50),
            ),
            (
                "let one = 1; let two = one + one; one + two",
                Object::Integer(3),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn strings() {
        let cases = vec![
            (
                "\"hello\" + \" \" + \"world\"",
                Object::String(Cow::from("hello world")),
            ),
            (
                "let one = \"hello\"; let two = one + one; one + two",
                Object::String(Cow::from("hellohellohello")),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn array() {
        let cases = vec![
            ("[]", Object::Array(vec![])),
            (
                "[1, 2, 3]",
                Object::Array(vec![
                    Rc::new(Object::Integer(1)),
                    Rc::new(Object::Integer(2)),
                    Rc::new(Object::Integer(3)),
                ]),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn map() {
        let cases = vec![
            ("let m = {}; m", Object::Map(HashMap::new())),
            (
                "let m = { 1: 2, 3: 4, 5: 6 }; m",
                Object::Map(HashMap::from([
                    (Object::Integer(1), Rc::new(Object::Integer(2))),
                    (Object::Integer(3), Rc::new(Object::Integer(4))),
                    (Object::Integer(5), Rc::new(Object::Integer(6))),
                ])),
            ),
            (
                "let m = { 1 + 2: 2, \"hello\" + \" \" + \"world\": 4, 5: 6 }; m",
                Object::Map(HashMap::from([
                    (Object::Integer(3), Rc::new(Object::Integer(2))),
                    (
                        Object::String(Cow::from("hello world")),
                        Rc::new(Object::Integer(4)),
                    ),
                    (Object::Integer(5), Rc::new(Object::Integer(6))),
                ])),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn indexing() {
        let cases = vec![
            (
                "[182, 2, 3, 4, 5, 638, 7, 8932, 9][5 - 4]",
                Object::Integer(2),
            ),
            (
                "[182, 2, 3, \"hello world\"][3]",
                Object::String(Cow::from("hello world")),
            ),
            (
                "
                let m = { 1 + 2: 2, \"hello\" + \" \" + \"world\": 4, 5: 6 };
                m[\"hello world\"]
            ",
                Object::Integer(4),
            ),
            ("[182, 2, 3, \"hello world\"][8]", Object::Null),
            (
                "
                let m = { 1 + 2: 2, \"hello\" + \" \" + \"world\": 4, 5: 6 };
                m[\"jgldskjfaslkjf\"]
            ",
                Object::Null,
            ),
            (
                "
                let m = {};
                m[\"jgldskjfaslkjf\"]
            ",
                Object::Null,
            ),
            ("[][8]", Object::Null),
            ("[[1, 2, 3]][0][2]", Object::Integer(3)),
        ];

        test_cases(&cases);
    }

    #[test]
    fn calling_functions_without_arguments() {
        let cases = vec![
            (
                "
                    let null_fn = fn() {  }; null_fn();
                ",
                Object::Null,
            ),
            (
                "
                    fn() {  }();
                ",
                Object::Null,
            ),
            (
                "
                    let fivePlusTen = fn() { 5 + 10; }; fivePlusTen();
                ",
                Object::Integer(15),
            ),
            (
                "
                    fn() { 5 + 5; }();
                ",
                Object::Integer(10),
            ),
            (
                "
                    let one = fn() { 1; };
                    let two = fn() { 2; };
                    one() + two()
                ",
                Object::Integer(3),
            ),
            (
                "
                    let a = fn() { 1 };
                    let b = fn() { a() - 2 };
                    let c = fn() { b() * 3 };
                    c();
                ",
                Object::Integer(-3),
            ),
            (
                "
                    let earlyExit = fn() { return 1; 10 };
                    earlyExit();
                ",
                Object::Integer(1),
            ),
            (
                "
                    let earlyExit = fn() { return 1; return 10 };
                    earlyExit();
                ",
                Object::Integer(1),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn calling_first_class_functions() {
        let cases = vec![
            (
                "
                    let returnsOne = fn() { 1; };
                    let returnsOneReturner = fn() { returnsOne; };
                    returnsOneReturner()();
                ",
                Object::Integer(1),
            ),
            (
                "
                    fn() { fn() { 1 + 1 } }()();
                ",
                Object::Integer(2),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn calling_functions_with_locals() {
        let cases = vec![
            (
                "
                    let one = fn() { let one = 1; one };
                    one();
                ",
                Object::Integer(1),
            ),
            (
                "
                    let oneAndTwo = fn() { let one = 1; let two = 2; one + two; };
                    oneAndTwo();
                ",
                Object::Integer(3),
            ),
            (
                "
                let oneAndTwo = fn() { let one = 1; let two = 2; one + two; };
                let threeAndFour = fn() { let three = 3; let four = 4; three + four; };
                oneAndTwo() + threeAndFour();
                ",
                Object::Integer(10),
            ),
            (
                "
                let firstFoobar = fn() { let foobar = 50; foobar; };
                let secondFoobar = fn() { let foobar = 100; foobar; };
                firstFoobar() + secondFoobar();
                ",
                Object::Integer(150),
            ),
            (
                "
                let globalSeed = 50;
                let minusOne = fn() { let num = 1; globalSeed - num; }
                let minusTwo = fn() { let num = 2; globalSeed - num; }
                minusOne() + minusTwo();
                ",
                Object::Integer(97),
            ),
            (
                "
                let returnsOneReturner = fn() {
                    let returnsOne = fn() { 1; };
                    returnsOne; 
                };

                returnsOneReturner()();
                ",
                Object::Integer(1),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn calling_functions_with_args_and_locals() {
        let cases = vec![
            (
                "
                    let identity = fn(a) { a; };
                    identity(2);
                ",
                Object::Integer(2),
            ),
            (
                "
                    let notUsingArg = fn(a) { 2 };
                    notUsingArg(true);
                ",
                Object::Integer(2),
            ),
            (
                "
                    let inv = fn(a) { !a };
                    inv(true);
                ",
                Object::Bool(false),
            ),
            (
                "
                    let sum = fn(a, b, c) { let z = 3; let x = 2; let r = 5; x + a + b; };
                    sum(3, 4, 5);
                ",
                Object::Integer(9),
            ),
            (
                "
                    let sum = fn(a, b) { let c = a + b; c; };
                    sum(1, 2);
                ",
                Object::Integer(3),
            ),
            (
                "
                    let sum = fn(a, b) { let c = a + b; c; };
                    sum(1, 2) + sum(3, 4);
                ",
                Object::Integer(10),
            ),
            (
                "
                    let sum = fn(a, b) { let c = a + b; c; };
                    let outer = fn() { sum(1, 2) + sum(3, 4); };
                    outer();
                ",
                Object::Integer(10),
            ),
            (
                "
                    let arg_to_local = fn(a) { let x = a; x };
                    arg_to_local(2);
                ",
                Object::Integer(2),
            ),
            (
                "
                    let globalNum = 10;
                    let sum = fn(a, b) { let c = a + b; c + globalNum; };
                    let outer = fn() { sum(1, 2) + sum(3, 4) + globalNum; };
                    outer() + globalNum;
                ",
                Object::Integer(50),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn calling_functions_with_wrong_args() {
        let cases = vec![
            (
                "
                    fn() { 1; }(2);
                ",
                MonkeError::new(format!("Wrong number of arguments: want=0, got=1")),
            ),
            (
                "
                    fn(a) { a; }();
                ",
                MonkeError::new(format!("Wrong number of arguments: want=1, got=0")),
            ),
            (
                "
                    fn(a, b) { a; b; }(2);
                ",
                MonkeError::new(format!("Wrong number of arguments: want=2, got=1")),
            ),
        ];

        test_cases_to_fail(&cases);
    }

    #[test]
    fn calling_closures() {
        let cases = vec![
            (
                "
                    let newClosure = fn (a) {
                        fn () {
                            a;
                        };
                    };

                    let inner = newClosure(99);
                    inner();
                ",
                Object::Integer(99),
            ),
            (
                "
                    let newAdder = fn (a, b) {
                        fn (c) {
                            a + b + c;
                        };
                    };

                    let innerAdder = newAdder(99, 1);
                    innerAdder(5);
                ",
                Object::Integer(105),
            ),
            (
                "
                    let newAdder = fn (a, b) {
                        let c = a + b;

                        fn (d) {
                            c + d;
                        };
                    };

                    let innerAdder = newAdder(99, 1);
                    innerAdder(5);
                ",
                Object::Integer(105),
            ),
            (
                "
                    let newAdderWithFn = fn (a, b) {
                        let c = a + b;

                        fn (func) {
                            func(c);
                        };
                    };

                    let mult_with_10 = fn(num) { num * 10 };

                    let innerAdder = newAdderWithFn(98, 1);
                    innerAdder(mult_with_10);
                ",
                Object::Integer(990),
            ),
            (
                "
                    let newClosure = fn (a, b) {
                        let one = fn () { a; };
                        let two = fn () { b;  };
                        
                        one() + two();
                    };

                    newClosure(99, 1);
                ",
                Object::Integer(100),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn calling_recursive_closures() {
        let cases = vec![
            (
                "
                    let countDown = fn (x) {
                        if (x == 0) {
                            return 123;
                        } else {
                            countDown(x - 1);
                        };
                    };

                    countDown(11);
                ",
                Object::Integer(123),
            ),
            (
                "
                    let countDown = fn (x) {
                        if (x == 0) {
                            return 123;
                        } else {
                            countDown(x - 1);
                        };
                    };

                    let wrapper = fn() {
                        countDown(11);
                    };

                    wrapper();
                ",
                Object::Integer(123),
            ),
            (
                "
                    let wrapper = fn() {
                        let countDown = fn (x) {
                            if (x == 0) {
                                return 123;
                            } else {
                                countDown(x - 1);
                            };
                        };

                        countDown(11);
                    };

                    wrapper();
                ",
                Object::Integer(123),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn recursive_fib() {
        let cases = vec![
            (
                "
                    let fib = fn (n) {
                        if (n == 1) { return 1; }
                        if (n == 2) { return 1; }

                        fib(n-1) + fib(n-2);
                    };

                    fib(18);
                ",
                Object::Integer(2584),
            ),
            (
                "
                    let fib = fn(x) {
                        if (x == 0) { return 0; }
                        else {
                            if (x == 1) { return 1; }
                            else {
                                fib(x - 1) + fib(x - 2); 
                            } 
                        } 
                    };
                    fib(15);
                ",
                Object::Integer(610),
            ),
        ];

        test_cases(&cases);
    }

    #[test]
    fn calling_builtin_fns() {
        let cases = vec![
            ("let arr = [1, 2, 3]; len(arr);", Object::Integer(3)),
            ("first([3, 4, 5]);", Object::Integer(3)),
            ("len(\"hello world\")", Object::Integer(11)),
            ("puts(\"hello world\")", Object::Null),
            ("first([1, 2, 3])", Object::Integer(1)),
            ("last([1, 2, 3])", Object::Integer(3)),
        ];

        test_cases(&cases);
    }

    #[test]
    fn debug() {
        let input = "-2";
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let mut compiler = Compiler::new();

        let program: Vec<Statement> = (&mut parser).collect();

        let (bytecode, constants, _) = compiler.compile(&program).unwrap();

        dbg!(&bytecode);

        println!("CONSTANTS START");
        constants
            .iter()
            .enumerate()
            .for_each(|(idx, cnst)| println!("CONSTANT_{idx}:\n{}", cnst));
        println!("CONSTANTS END");

        println!("BYTECODE START");
        println!("{}", &bytecode.to_string());
        println!("BYTECODE END");

        let mut vm = VM::new(bytecode, constants);

        let result = vm.run().inspect_err(|err| eprintln!("{err}"));

        dbg!(result);
        dbg!(&vm.stack[..10]);
        dbg!(&vm.sp);
        dbg!(&vm.frame_idx);

        let (bytecode, ..) = vm.cur_frame_inner();
        println!("Cur frame bytecode as string\n: {}", bytecode.to_string());
        dbg!(&vm.constants);
    }
}
