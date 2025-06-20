use std::{
    collections::{BTreeMap, HashMap},
    ops::Deref,
    rc::Rc,
    sync::LazyLock,
};

use crate::{monke_error::MonkeError, object::Object};

pub type Bfn = fn(Vec<Rc<Object>>) -> Result<Rc<Object>, MonkeError>;

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct BuiltinFn(pub Bfn);

impl Deref for BuiltinFn {
    type Target = Bfn;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub static BUILTIN_FNS: LazyLock<BTreeMap<&'static str, BuiltinFn>> = LazyLock::new(|| {
    BTreeMap::from([
        ("first", BuiltinFn(b_first)),
        ("last", BuiltinFn(b_last)),
        ("len", BuiltinFn(b_len)),
        ("puts", BuiltinFn(b_puts)),
    ])
});

fn b_len(args: Vec<Rc<Object>>) -> Result<Rc<Object>, MonkeError> {
    if args.len() != 1 {
        return MonkeError::new(format!("Expected 1 arg, got {}", args.len())).into();
    }

    match &args[0].as_ref() {
        Object::String(cow) => Ok(Rc::new(Object::Integer(cow.len() as isize))),
        Object::Array(elements) => Ok(Rc::new(Object::Integer(elements.len() as isize))),

        _ => MonkeError::new(format!("{} not supported by `len`", args[0])).into(),
    }
}

fn b_puts(args: Vec<Rc<Object>>) -> Result<Rc<Object>, MonkeError> {
    for arg in args {
        println!("{}", arg);
    }

    Ok(Rc::new(Object::Null))
}

fn b_first(args: Vec<Rc<Object>>) -> Result<Rc<Object>, MonkeError> {
    if args.len() != 1 {
        return MonkeError::new(format!("Expected 1 arg, got {}", args.len())).into();
    }

    match &args[0].as_ref() {
        Object::Array(elements) => {
            if elements.len() > 0 {
                Ok(Rc::clone(&elements[0]))
            } else {
                Ok(Rc::new(Object::Null))
            }
        }

        _ => MonkeError::new(format!("{} not supported by `first`", args[0])).into(),
    }
}

fn b_last(args: Vec<Rc<Object>>) -> Result<Rc<Object>, MonkeError> {
    if args.len() != 1 {
        return MonkeError::new(format!("Expected 1 arg, got {}", args.len())).into();
    }

    match &args[0].as_ref() {
        Object::Array(elements) => {
            if elements.len() > 0 {
                Ok(Rc::clone(&elements[elements.len() - 1]))
            } else {
                Ok(Rc::new(Object::Null))
            }
        }

        _ => MonkeError::new(format!("{} not supported by `first`", args[0])).into(),
    }
}

fn b_push(args: Vec<Rc<Object>>) -> Result<Object, MonkeError> {
    todo!()
}
