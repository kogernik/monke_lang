use std::{
    borrow::Cow,
    cell::RefCell,
    collections::HashMap,
    mem,
    ops::{Deref, DerefMut, Neg},
    rc::Rc,
};

use serde::{Deserialize, Serialize};

use crate::{
    builtin::BUILTIN_FNS,
    lexer::Lexer,
    monke_error::MonkeError,
    object::Object,
    parser::parser::{Expression, Parser, Statement},
};

pub fn run_eval_on_input<'i>(input: &'i str) -> Result<Rc<Object<'i>>, MonkeError> {
    let lexer = Lexer::new(input);
    let mut parser = Parser::new(lexer);
    let program: Vec<Statement> = (&mut parser).collect();

    assert_eq!(parser.errors, Vec::<String>::new());

    let mut evaluator = Evaluator::new();

    let result = evaluator.evaluate_program(&program);

    result
}

#[derive(Debug, PartialEq, Clone)]
pub struct Environment<'i> {
    inner: HashMap<&'i str, Rc<Object<'i>>>,
    outer: Option<Rc<RefCell<Environment<'i>>>>,
}

pub struct Evaluator<'i> {
    pub env: Rc<RefCell<Environment<'i>>>,
}

impl<'i> Environment<'i> {
    pub fn new() -> Self {
        Environment {
            inner: HashMap::new(),
            outer: None,
        }
    }

    pub fn with_outer(outer_env: Rc<RefCell<Environment<'i>>>) -> Self {
        Environment {
            inner: HashMap::new(),
            outer: Some(outer_env),
        }
    }

    pub fn get_with_outer(&self, key: &'i str) -> Option<Rc<Object<'i>>> {
        match (self.inner.get(key), &self.outer) {
            (Some(from_inner), _) => Some(Rc::clone(from_inner)),

            (None, Some(outer_env)) => outer_env.borrow().get_with_outer(key),

            _ => None,
        }
    }
}

impl<'i> Evaluator<'i> {
    pub fn new() -> Self {
        Self {
            env: Rc::new(RefCell::new(Environment {
                inner: HashMap::new(),
                outer: None,
            })),
        }
    }

    pub fn evaluate_program(
        &mut self,
        stmns: &[Statement<'i>],
    ) -> Result<Rc<Object<'i>>, MonkeError> {
        let mut result = Rc::new(Object::Null);

        for stmn in stmns {
            result = self.evaluate_stmn(stmn)?;

            match result.as_ref() {
                Object::ReturnWrap(return_value) => return Ok(Rc::clone(return_value)),

                _ => (),
            };
        }

        Ok(result)
    }

    pub fn evaluate_stmn(&mut self, stmn: &Statement<'i>) -> Result<Rc<Object<'i>>, MonkeError> {
        match stmn {
            Statement::Let { .. } => self.evaluate_let(stmn),
            Statement::ExprStmn { expr } => self.evaluate_expr(&expr),
            Statement::Return { .. } => self.evaluate_return(stmn),
            Statement::Block { statements } => self.evaluate_block(stmn),
        }
    }

    pub fn evaluate_let(&mut self, stmn: &Statement<'i>) -> Result<Rc<Object<'i>>, MonkeError> {
        let (name, expr) = match stmn {
            Statement::Let { name, expr } => (*name, expr),
            _ => panic!(
                "evaluate_let should be called only for Statement::Let, instead got {stmn:?}"
            ),
        };

        let result = self.evaluate_expr(expr)?;

        self.env.borrow_mut().inner.insert(name, result);

        Ok(Rc::new(Object::Suc))
    }

    pub fn evaluate_return(&mut self, stmn: &Statement<'i>) -> Result<Rc<Object<'i>>, MonkeError> {
        let expr = match stmn {
            Statement::Return { expr } => expr,

            _ => panic!(
                "evaluate_return should be called only for Statement::Return, instead got {stmn:?}"
            ),
        };

        self.evaluate_expr(&expr)
            .map(|expr| Rc::new(Object::ReturnWrap(expr)))
    }

    pub fn evaluate_block(&mut self, stmn: &Statement<'i>) -> Result<Rc<Object<'i>>, MonkeError> {
        let stmns = match stmn {
            Statement::Block { statements } => statements,

            _ => panic!(
                "evaluate_block should be called only for Statement::Block, instead got {stmn:?}"
            ),
        };

        let mut result = Rc::new(Object::Null);

        for stmn in stmns {
            result = self.evaluate_stmn(stmn)?;

            if let Object::ReturnWrap(_) = result.as_ref() {
                return Ok(result);
            };
        }

        Ok(result)
    }

    pub fn evaluate_expr(&mut self, expr: &Expression<'i>) -> Result<Rc<Object<'i>>, MonkeError> {
        match expr {
            Expression::Integer(int) => Ok(Rc::new(Object::Integer(*int))),
            Expression::Float(float) => Ok(Rc::new(Object::Float(*float))),
            Expression::Bool(bool) => Ok(Rc::new(Object::Bool(*bool))),
            Expression::Str(str) => Ok(Rc::new(Object::String(Cow::from(*str)))),

            Expression::Identifier(..) => self.evaluate_identifier(expr),
            Expression::If { .. } => self.evaluate_if(expr),
            Expression::Fn { .. } => self.evaluate_fn(expr),
            Expression::Call { .. } => self.evaluate_call(expr),
            Expression::Indexing { .. } => self.evaluate_indexing(expr),
            Expression::Prefix { .. } => self.evaluate_prefix(expr),
            Expression::Infix { .. } => self.evaluate_infix(expr),
            Expression::Array(..) => self.evaluate_array(expr),
            Expression::Map(..) => self.evaluate_map(expr),
        }
    }

    fn evaluate_identifier(&self, expr: &Expression<'i>) -> Result<Rc<Object<'i>>, MonkeError> {
        let name = match expr {
            Expression::Identifier(name) => *name,
            _ => panic!(
                "evaluate_identifier should be called only for Expression::Identifier, instead got {expr:?}"
            ),
        };

        if let Some(value) = self.env.borrow().get_with_outer(name) {
            return Ok(value);
        }

        if let Some(&builtin_fn) = BUILTIN_FNS.get(name) {
            return Ok(Rc::new(Object::Builtin(builtin_fn)));
        }

        MonkeError::new(format!("identifier with name = {name} not found")).into()
    }

    fn evaluate_if(&mut self, expr: &Expression<'i>) -> Result<Rc<Object<'i>>, MonkeError> {
        let (condition, yes, no) = match expr {
            Expression::If { condition, yes, no } => (condition.deref(), yes.deref(), no),
            _ => panic!("evaluate_if should be called only for Expression::If"),
        };

        let condition_result = {
            let condition_result = self.evaluate_expr(condition)?;
            match *condition_result {
                Object::Bool(condition_result) => condition_result,

                _ => panic!("condition expr should return Object::Bool"),
            }
        };

        match (condition_result, yes, no) {
            (true, yes, _) => self.evaluate_stmn(yes),
            (false, _, Some(no)) => self.evaluate_stmn(no),
            _ => Ok(Rc::new(Object::Null)),
        }
    }

    fn evaluate_fn(&mut self, expr: &Expression<'i>) -> Result<Rc<Object<'i>>, MonkeError> {
        let (parameters, body) = match expr {
            Expression::Fn {
                parameters, body, ..
            } => (parameters, body),
            _ => {
                panic!("evaluate_fn should be called only for Expression::Fn, instead got {expr:?}")
            }
        };

        Ok(Rc::new(Object::Function {
            parameters: parameters.clone(),
            body: body.clone(),
            env: Rc::clone(&self.env),
        }))
    }

    fn evaluate_call(&mut self, expr: &Expression<'i>) -> Result<Rc<Object<'i>>, MonkeError> {
        let (func_expr, arguments) = match expr {
            Expression::Call {
                function,
                arguments,
            } => (function.deref(), arguments),

            _ => panic!(
                "evaluate_call should be called only for Expression::Call, instead got {expr:?}"
            ),
        };

        let function = self.evaluate_expr(&func_expr)?;

        match function.as_ref() {
            Object::Builtin(bfn) => {
                let args = {
                    let args: Result<Vec<Rc<Object<'i>>>, MonkeError> = arguments
                        .iter()
                        .map(|arg| self.evaluate_expr(arg))
                        .collect();

                    args?
                };

                bfn(args)
            }

            Object::Function {
                parameters,
                body,
                env,
            } => {
                if parameters.len() != arguments.len() {
                    return MonkeError::new(format!(
                        "Wrong number of arguments: want={}, got={}",
                        parameters.len(),
                        arguments.len()
                    ))
                    .into();
                }

                let mut fn_env = Environment::with_outer(Rc::clone(env));

                for (param, arg) in parameters.iter().zip(arguments.iter()) {
                    let Expression::Identifier(name) = param else {
                        panic!("params should always be identifiers");
                    };

                    let arg_result = self.evaluate_expr(arg)?;
                    fn_env.inner.insert(name, arg_result);
                }

                let self_env = mem::replace(&mut self.env, Rc::new(RefCell::new(fn_env)));

                let call_result = self.evaluate_block(body.as_ref());

                mem::replace(&mut self.env, self_env);

                call_result.map(|call_result| {
                    if let Object::ReturnWrap(actual_call_result) = call_result.as_ref() {
                        Rc::clone(actual_call_result)
                    } else {
                        call_result
                    }
                })
            }

            _ => panic!("evaluate_fn return Function, somehow got {function:?}"),
        }
    }

    pub fn evaluate_array(&mut self, expr: &Expression<'i>) -> Result<Rc<Object<'i>>, MonkeError> {
        let elements = match expr {
            Expression::Array(elements) => elements,

            _ => panic!(
                "evaluate_array should be called only for Expression::Array, instead got {expr:?}"
            ),
        };

        let obj_elements = {
            let obj_elements: Result<Vec<Rc<Object<'i>>>, MonkeError> = elements
                .iter()
                .map(|el| Ok(self.evaluate_expr(el)?))
                .collect();

            obj_elements?
        };

        Ok(Rc::new(Object::Array(obj_elements)))
    }

    pub fn evaluate_map(&mut self, expr: &Expression<'i>) -> Result<Rc<Object<'i>>, MonkeError> {
        let keys_values = match expr {
            Expression::Map(keys_values) => keys_values,

            _ => panic!(
                "evaluate_map should be called only for Expression::Map, instead got {expr:?}"
            ),
        };

        let obj_map = {
            let obj_map: Result<HashMap<Object, Rc<Object>>, MonkeError> = keys_values
                .iter()
                .map(|(key, value)| {
                    let key_obj = self.evaluate_expr(key)?.as_ref().clone();
                    let value_obj = self.evaluate_expr(value)?;

                    Ok((key_obj, value_obj))
                })
                .collect();

            obj_map?
        };

        Ok(Rc::new(Object::Map(obj_map)))
    }

    pub fn evaluate_indexing(
        &mut self,
        expr: &Expression<'i>,
    ) -> Result<Rc<Object<'i>>, MonkeError> {
        let (left_expr, index_expr) = match expr {
            Expression::Indexing { left, index } => (left.deref(), index.deref()),

            _ => panic!(
                "evaluate_indexing should be called only for Expression::Index, instead got {expr:?}"
            ),
        };

        let mut left = self.evaluate_expr(left_expr)?;
        let index = self.evaluate_expr(index_expr)?;

        let result = match (left.as_ref(), index.as_ref()) {
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

        Ok(result)
    }

    pub fn evaluate_prefix(&mut self, expr: &Expression<'i>) -> Result<Rc<Object<'i>>, MonkeError> {
        let (op, right_expr) = match expr {
            Expression::Prefix { op, right } => (*op, right.as_ref()),
            _ => panic!(
                "evaluate_prefix should be called only for Expression::Prefix, instead got {expr:?}"
            ),
        };

        let right = self.evaluate_expr(right_expr)?;

        let result = match (op, right.as_ref()) {
            ("!", Object::Bool(bool)) => Object::Bool(!bool),

            ("-", Object::Integer(int)) => Object::Integer(int.neg()),
            ("-", Object::Float(float)) => Object::Float(float.neg()),

            _ => {
                return MonkeError::new(format!("op = {op} not implemented for {right:?}")).into();
            }
        };

        Ok(Rc::new(result))
    }

    pub fn evaluate_infix(&mut self, expr: &Expression<'i>) -> Result<Rc<Object<'i>>, MonkeError> {
        use Object::*;

        let (left, op, right) = match expr {
            Expression::Infix { left, op, right } => (left.deref(), *op, right.deref()),
            _ => panic!(
                "evaluate_infix should be called only for Expression::Infix, instead got {expr:?}"
            ),
        };

        let (left_result, right_result) = (self.evaluate_expr(left)?, self.evaluate_expr(right)?);

        #[rustfmt::skip]
        let result = match (op, left_result.as_ref(), right_result.as_ref()) {

            ("!=", Bool(left),    Bool(right))    => Bool(left != right),
            ("==", Bool(left),    Bool(right))    => Bool(left == right),

            ("+",  Integer(left), Integer(right)) => Integer(left + right),
            ("-",  Integer(left), Integer(right)) => Integer(left - right),
            ("*",  Integer(left), Integer(right)) => Integer(left * right),
            ("/",  Integer(left), Integer(right)) => Integer(left / right),
            ("<",  Integer(left), Integer(right)) => Bool(left < right),
            (">",  Integer(left), Integer(right)) => Bool(left > right),
            ("<=", Integer(left), Integer(right)) => Bool(left <= right),
            (">=", Integer(left), Integer(right)) => Bool(left >= right),
            ("!=", Integer(left), Integer(right)) => Bool(left != right),
            ("==", Integer(left), Integer(right)) => Bool(left == right),

            ("+",  Float(left),   Float(right))   => Float(left + right),
            ("-",  Float(left),   Float(right))   => Float(left - right),
            ("*",  Float(left),   Float(right))   => Float(left * right),
            ("/",  Float(left),   Float(right))   => Float(left / right),
            ("<",  Float(left),   Float(right))   => Bool(left < right),
            (">",  Float(left),   Float(right))   => Bool(left > right),
            ("<=", Float(left),   Float(right))   => Bool(left <= right),
            (">=", Float(left),   Float(right))   => Bool(left >= right),
            ("!=", Float(left),   Float(right))   => Bool(left != right),
            ("==", Float(left),   Float(right))   => Bool(left == right),

            ("+",  String(left),  String(right))  => String(Cow::from(left.to_string() + &right)),
            ("<",  String(left),  String(right))  => Bool(left < right),
            (">",  String(left),  String(right))  => Bool(left > right),
            ("<=", String(left),  String(right))  => Bool(left <= right),
            (">=", String(left),  String(right))  => Bool(left >= right),
            ("!=", String(left),  String(right))  => Bool(left != right),
            ("==", String(left),  String(right))  => Bool(left == right),

            (op, left_result, right_result) => {
                return MonkeError::new(format!(
                    "op = {op} not implemented for {left_result:?} and {right_result:?}"
                )).into();
            }

        };

        Ok(Rc::new(result))
    }
}

#[cfg(test)]
mod evaluator_tests {
    use std::time::Instant;

    use crate::{lexer::Lexer, parser::parser::Parser};

    use super::*;

    fn test_cases<'i>(cases: &'i [(&'i str, Object<'i>)]) {
        let tim = Instant::now();

        for case @ (input, exp_res) in cases {
            let input = input.as_ref();
            let lexer = Lexer::new(input);
            let mut parser = Parser::new(lexer);

            let program: Vec<Statement> = (&mut parser).collect();

            assert_eq!(parser.errors, Vec::<String>::new());

            let mut evaluator = Evaluator::new();

            let res = evaluator.evaluate_program(&program).unwrap();

            assert_eq!(
                res.as_ref(),
                exp_res,
                "TEST ERROR at case\n
                    \t ({input},
                    \t {exp_res:?})\n\n
                ",
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

            let program: Vec<Statement> = (&mut parser).collect();

            let mut evaluator = Evaluator::new();

            let err = match evaluator.evaluate_program(&program) {
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
                    let fib = fn(n) { if (n<=1) { return n; } return fib(n-1) + fib(n-2) };
                    fib(3);
                ",
                Object::Integer(2),
            ),
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
    fn test_evaluate() {
        let input = "
let add = fn(a, b, c, d) { return a + b + c + d };
let add_result = add(1, 2, 3, 4);

let addThree = fn(x) { return x + 3 };

let max = fn(x, y) { if (x > y) { x } else { y } };
let max_result = max(5, 10);


let callTwoTimes = fn(x, func) { func(func(x)) };
let call_two_times_result1 = callTwoTimes(3, addThree);
let call_two_times_result2 = callTwoTimes(3, fn(x) { x + 1 });

let factorial = fn(n) { if (n == 0) { 1 } else { n * factorial(n - 1) } };
let factorial_result = factorial(4);
factorial_result

let newAdder = fn(x) { fn(n) { x + n } };
let addTwo = newAdder(2);
let add_two_result = addTwo(70);
add_two_result

let addTwo = newAdder(\"hello \");
let add_two_result = addTwo(\" world\");
add_two_result

let len_test = len(\"hello world\");
len_test

let double = fn(x) { x * 2 };
let ara = [1, 2, 34, double(32), 99, \"hello\"];
let ara_ara = [ara[0] * 0, ara[1] * 1, ara[2] * 2, ara[3] * 3, ara[4] * 4, ara[5] + \" world\"];
ara_ara[2];

let mapa = { 1: double(2), \"hello\": ara };
puts(mapa, ara_ara[2]);
";

        let lexer = Lexer::new(&input);
        let mut parser = Parser::new(lexer);
        let program: Vec<Statement> = (&mut parser).collect();

        let mut evaluator = Evaluator::new();

        let result = evaluator.evaluate_program(&program);

        match result {
            Ok(ok_res) => {
                dbg!(ok_res);
            }

            Err(err_res) => {
                println!("{err_res}");
            }
        };
    }
}
