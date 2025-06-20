use std::{cell::Cell, rc::Rc};

use crate::object::Object;

use super::bytecode::Bytecode;

#[derive(Debug, Clone, PartialEq)]
pub struct Frame<'i> {
    pub closure: Rc<Object<'i>>,
    pub ip: Cell<usize>,
    pub base_pointer: Cell<usize>,
}

impl<'i> Frame<'i> {
    pub fn new(closure: Rc<Object<'i>>, base_pointer: usize) -> Self {
        assert!(matches!(closure.as_ref(), Object::Closure { .. }));

        Self {
            closure,
            ip: Cell::new(0),
            base_pointer: Cell::new(base_pointer),
        }
    }

    pub fn get_inner(&self) -> (&Bytecode, &Vec<Rc<Object<'i>>>, &Cell<usize>, &Cell<usize>) {
        let Object::Closure { cfn, free_vars } = self.closure.as_ref() else {
            panic!("Frame.cfn should contain only Object::Closure, instead got {self:?}")
        };

        let Object::CompiledFunction { bytecode, .. } = cfn.as_ref() else {
            panic!("Object::Closure should contain Object::CompiledFunction, instead got {cfn:?}");
        };

        let ip = &self.ip;
        let base_pointer = &self.base_pointer;

        (bytecode, free_vars, ip, base_pointer)
    }
}
