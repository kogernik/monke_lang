use std::{
    borrow::Cow,
    cell::RefCell,
    cmp::Eq,
    collections::HashMap,
    hash::{Hash, Hasher},
    rc::Rc,
};

use crate::{
    builtin::BuiltinFn,
    evaluator::Environment,
    monke_error::MonkeError,
    parser::parser::{Expression, Statement},
    vm::bytecode::Bytecode,
};

#[derive(Debug, PartialEq, Clone)]
pub enum Object<'i> {
    Null,
    Suc,

    Bool(bool),
    Integer(isize),
    Float(f64),
    ReturnWrap(Rc<Object<'i>>),
    String(Cow<'i, str>),

    // used only for evaluator
    Function {
        parameters: Vec<Expression<'i>>,
        body: Box<Statement<'i>>,
        env: Rc<RefCell<Environment<'i>>>,
    },
    // used only for vm
    CompiledFunction {
        bytecode: Bytecode,
        num_locals: usize,
        num_args: usize,
    },
    // used only for vm
    Closure {
        cfn: Rc<Object<'i>>, // this is always Object::CompiledFunction; NOTE before using sumenum think if you need variants as types
        free_vars: Vec<Rc<Object<'i>>>,
    },

    Array(Vec<Rc<Object<'i>>>),
    Map(HashMap<Object<'i>, Rc<Object<'i>>>),

    Builtin(BuiltinFn),
}

impl<'i> Eq for Object<'i> {}

impl<'i> Hash for Object<'i> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Object::Integer(int) => int.hash(state),
            Object::String(cow) => cow.hash(state),

            obj => panic!("cannot hash object = {obj}"),
        }
    }
}

impl<'i> std::fmt::Display for Object<'i> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Object::Null => write!(f, "NOP"),
            Object::Suc => write!(f, "SUC"),
            Object::Bool(value) => write!(f, "{}", value),
            Object::Integer(value) => write!(f, "{}", value),
            Object::Float(value) => write!(f, "{}", value),
            Object::ReturnWrap(obj) => write!(f, "return {}", obj),
            Object::String(text) => write!(f, "\"{}\"", text),
            Object::Builtin(bfn) => write!(f, "{:?}", bfn),
            Object::Map(hash_map) => {
                write!(
                    f,
                    "{{ {}\n}}",
                    hash_map
                        .iter()
                        .map(|(key, value)| format!("\n\t{key}: {value}"))
                        .collect::<Vec<_>>()
                        .join(",")
                )
            }
            Object::Array(elements) => write!(
                f,
                "[{}]",
                elements
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Object::Function {
                parameters, body, ..
            } => {
                write!(
                    f,
                    "fn(\n{}) {body}",
                    parameters
                        .iter()
                        .map(|p| p.to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                )
            }
            Object::CompiledFunction { bytecode, .. } => {
                write!(f, "{bytecode}")
            }
            Object::Closure { cfn, .. } => {
                write!(f, "Closure[{:p}]", cfn)
            }
        }
    }
}
