use super::{
    parser::{Expression, Statement},
    visitor::Visitor,
};

use std::io::Write as _;
use std::{fmt::Write as _, ops::Deref};

struct DisplayVisitor {
    output: String,
    indent_count: isize,
}

const MAX_INDENT: &str = "                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        ";

impl DisplayVisitor {
    pub fn new() -> Self {
        Self {
            output: String::new(),
            indent_count: 0,
        }
    }

    fn indent(&mut self) {
        self.indent_count += 4;
    }

    fn dedent(&mut self) {
        self.indent_count -= 4;
    }

    fn write_indent(&mut self) {
        if self.indent_count > 0 {
            self.output
                .push_str(&MAX_INDENT[0..self.indent_count as usize]);
        }
    }
}

impl<'i> Visitor<'i> for DisplayVisitor {
    fn visit_expression(&mut self, expr: &Expression<'i>) {
        match expr {
            Expression::Identifier(name) => {
                write!(self.output, "{}", name);
            }

            Expression::Integer(value) => {
                write!(self.output, "{}", value);
            }

            Expression::Float(value) => {
                write!(self.output, "{}", value);
            }

            Expression::Str(value) => {
                write!(self.output, "\"{}\"", value);
            }

            Expression::Bool(value) => {
                write!(self.output, "{}", value);
            }

            Expression::Prefix { op, right } => {
                write!(self.output, "({}", op);
                self.visit_expression(right);
                write!(self.output, ")");
            }

            Expression::Infix { left, op, right } => {
                write!(self.output, "(");
                self.visit_expression(left);
                write!(self.output, " {} ", op);
                self.visit_expression(right);
                write!(self.output, ")");
            }

            Expression::If { condition, yes, no } => {
                write!(self.output, "if ");
                self.visit_expression(condition);
                write!(self.output, " ");

                self.visit_statement(yes);

                if let Some(else_block) = no {
                    self.output.truncate(self.output.len() - 1); // to remove \n from self.visit_statement(yes);
                    write!(self.output, " else ");
                    self.visit_statement(else_block);
                }
            }

            Expression::Fn {
                parameters, body, ..
            } => {
                write!(self.output, "fn(");
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(self.output, ", ");
                    }
                    self.visit_expression(param);
                }
                write!(self.output, ") ");
                self.visit_statement(body);
            }

            Expression::Call {
                function,
                arguments,
            } => {
                self.visit_expression(function);
                write!(self.output, "(");
                for (i, arg) in arguments.iter().enumerate() {
                    if i > 0 {
                        write!(self.output, ", ");
                    }
                    self.visit_expression(arg);
                }
                write!(self.output, ")");
            }

            Expression::Indexing { left, index } => {
                self.visit_expression(left);
                write!(self.output, "[");
                self.visit_expression(index);
                write!(self.output, "]");
            }

            Expression::Array(elements) => {
                write!(self.output, "[");
                for (i, element) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(self.output, ", ");
                    }
                    self.visit_expression(element);
                }
                write!(self.output, "] ");
            }

            Expression::Map(map) => {
                write!(self.output, "{{");
                for (i, (key, value)) in map.iter().enumerate() {
                    write!(self.output, "\n\t");

                    if i > 0 {
                        write!(self.output, ",");
                    }

                    self.visit_expression(key);
                    write!(self.output, ": ");
                    self.visit_expression(value);
                }
                write!(self.output, "}} ");
            }
        }
    }

    fn visit_statement(&mut self, stmt: &Statement<'i>) {
        match stmt {
            Statement::Let { name, expr } => {
                self.write_indent();
                write!(self.output, "let {} = ", name);

                self.indent();
                self.visit_expression(expr);

                self.dedent();
                writeln!(self.output, ";");
            }

            Statement::ExprStmn { expr } => {
                self.write_indent();
                self.visit_expression(expr);

                match expr {
                    Expression::If { condition, yes, no } => Ok(()),
                    Expression::Fn {
                        parameters, body, ..
                    } => Ok(()),

                    _ => writeln!(self.output, ";"),
                };
            }

            Statement::Return { expr } => {
                self.write_indent();
                write!(self.output, "return ");

                self.visit_expression(expr);

                writeln!(self.output, ";");
            }

            Statement::Block { statements } => {
                writeln!(self.output, "{{");

                self.indent();
                for stmt in statements {
                    self.visit_statement(stmt);
                }
                self.dedent();

                self.write_indent();
                writeln!(self.output, "}}");
            }
        }
    }
}

impl<'i> std::fmt::Display for Expression<'i> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut vis = DisplayVisitor::new();

        self.visit(&mut vis);

        writeln!(f, "{}", vis.output)
    }
}

impl<'i> std::fmt::Display for Statement<'i> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut vis = DisplayVisitor::new();

        self.visit(&mut vis);

        writeln!(f, "{}", vis.output)
    }
}
