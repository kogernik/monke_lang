use super::parser::{Expression, Statement};

pub trait Visitor<'i> {
    fn visit_expression(&mut self, expr: &Expression<'i>);
    fn visit_statement(&mut self, stmt: &Statement<'i>);
}

impl<'i> Expression<'i> {
    pub fn visit(&self, visitor: &mut dyn Visitor<'i>) {
        visitor.visit_expression(self);
    }
}

impl<'i> Statement<'i> {
    pub fn visit(&self, visitor: &mut dyn Visitor<'i>) {
        visitor.visit_statement(self);
    }
}
