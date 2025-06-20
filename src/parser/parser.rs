use std::{
    borrow::Cow,
    collections::HashMap,
    hash::{Hash, Hasher},
    iter::Peekable,
    mem,
};

use serde::{Deserialize, Serialize};

use crate::lexer::{self, Lexer};

const DUMMY_STR: &str = "";
const DUMMY_NUM: isize = 0;
const DUMMY_FLOAT: f64 = 0.0;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Precedence {
    Lowest,
    Equals,      // ==, !=
    LessGreater, // >, <, <=, >=
    Sum,         // +, -
    Product,     // *, /
    Prefix,      // -X, !X
    Call,        // my_function(X)
    Indexing,    // a[i]
}

impl Precedence {
    pub fn by_token_kind(token_kind: &lexer::TokenKind) -> Precedence {
        use lexer::TokenKind::*;

        match token_kind {
            Equal | NotEqual => Precedence::Equals,
            Less | LessEqual | Greater | GreaterEqual => Precedence::LessGreater,
            Plus | Minus => Precedence::Sum,
            Slash | Asterisk => Precedence::Product,
            LeftParen => Precedence::Call,
            LeftBracket => Precedence::Indexing,
            _ => Precedence::Lowest,
        }
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
#[serde(bound(deserialize = "'de: 'i"))]
pub enum Expression<'i> {
    Identifier(&'i str),
    Integer(isize),
    Float(f64),
    Str(&'i str),
    Bool(bool),

    Prefix {
        op: &'i str,
        right: Box<Expression<'i>>,
    },

    Infix {
        left: Box<Expression<'i>>,
        op: &'i str,
        right: Box<Expression<'i>>,
    },

    If {
        condition: Box<Expression<'i>>,
        yes: Box<Statement<'i>>,
        no: Option<Box<Statement<'i>>>,
    },

    Fn {
        name: Option<&'i str>,
        parameters: Vec<Expression<'i>>,
        body: Box<Statement<'i>>,
    },

    Call {
        function: Box<Expression<'i>>,
        arguments: Vec<Expression<'i>>,
    },

    Indexing {
        left: Box<Expression<'i>>,
        index: Box<Expression<'i>>,
    },

    Array(Vec<Expression<'i>>),
    Map(Vec<(Expression<'i>, Expression<'i>)>),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
#[serde(bound(deserialize = "'de: 'i"))]
pub enum Statement<'i> {
    Let { name: &'i str, expr: Expression<'i> },

    ExprStmn { expr: Expression<'i> },

    Return { expr: Expression<'i> },

    Block { statements: Vec<Statement<'i>> },
}

#[derive(Debug)]
pub struct Parser<'i> {
    pub lexer: Peekable<Lexer<'i>>,
    pub errors: Vec<String>,
}

impl<'i> Parser<'i> {
    pub fn new(lexer: Lexer<'i>) -> Self {
        Self {
            lexer: lexer.peekable(),
            errors: Vec::new(),
        }
    }

    fn next_expect(&mut self, exp_tk: &lexer::TokenKind<'i>) -> Option<lexer::Token<'i>> {
        let Some(token) = self.lexer.next() else {
            self.errors.push(format!(
                "Expected next token to be {:?}, got None instead",
                exp_tk,
            ));

            return None;
        };

        let exp_disc = mem::discriminant(exp_tk);
        let got_disc = mem::discriminant(&token.kind);

        if exp_disc != got_disc {
            self.errors.push(format!(
                "Expected next token to be {:?}, got {:?} instead",
                exp_tk, &token.kind,
            ));

            None
        } else {
            Some(token)
        }
    }

    fn skip_expect(&mut self, exp_tk: &lexer::TokenKind<'i>) -> bool {
        let Some(peek_token) = self.lexer.peek() else {
            return false;
        };

        let exp_disc = mem::discriminant(exp_tk);
        let got_disc = mem::discriminant(&peek_token.kind);

        if exp_disc == got_disc {
            self.lexer.next();
            true
        } else {
            false
        }
    }

    pub fn parse_next(&mut self) -> Option<Statement<'i>> {
        self.parse_statement()
    }

    pub fn parse_statement(&mut self) -> Option<Statement<'i>> {
        use crate::lexer::TokenKind;

        let token = self.lexer.peek()?;

        match token.kind {
            TokenKind::Let => self.parse_let(),
            TokenKind::Return => self.parse_return(),
            TokenKind::LeftBrace => self.parse_block(),
            _ => self.parse_expr_stmn(),
        }
    }

    fn parse_let(&mut self) -> Option<Statement<'i>> {
        self.next_expect(&lexer::TokenKind::Let)?;

        let name = match self.next_expect(&lexer::TokenKind::Ident(DUMMY_STR))? {
            lexer::Token {
                kind: lexer::TokenKind::Ident(name),
                ..
            } => name,

            _ => unreachable!("checked in next_expect"),
        };

        self.next_expect(&lexer::TokenKind::Assign)?;

        let mut expr = self.parse_expression(&Precedence::Lowest)?;

        if let Expression::Fn {
            name: ref mut fn_name,
            ..
        } = expr
        {
            *fn_name = Some(name);
        }

        self.skip_expect(&lexer::TokenKind::Semicolon);

        Some(Statement::Let { name, expr })
    }

    fn parse_return(&mut self) -> Option<Statement<'i>> {
        self.next_expect(&lexer::TokenKind::Return)?;

        let expr = self.parse_expression(&Precedence::Lowest)?;

        self.skip_expect(&lexer::TokenKind::Semicolon);

        Some(Statement::Return { expr })
    }

    fn parse_block(&mut self) -> Option<Statement<'i>> {
        self.next_expect(&lexer::TokenKind::LeftBrace)?;

        let mut statements = vec![];
        loop {
            let Some(peek_token) = self.lexer.peek() else {
                break;
            };

            if peek_token.kind == lexer::TokenKind::RightBrace {
                break;
            }

            let stmn = self.parse_next()?;

            statements.push(stmn);
        }

        self.next_expect(&lexer::TokenKind::RightBrace)?;

        Some(Statement::Block { statements })
    }

    fn parse_expr_stmn(&mut self) -> Option<Statement<'i>> {
        let expr = self.parse_expression(&Precedence::Lowest)?;

        self.skip_expect(&lexer::TokenKind::Semicolon);

        Some(Statement::ExprStmn { expr })
    }

    fn parse_expression(&mut self, prev_op_precedence: &Precedence) -> Option<Expression<'i>> {
        let expr = {
            let mut left_expr = self.parse_expression_left()?;

            loop {
                let Some(peek_token) = self.lexer.peek() else {
                    break left_expr;
                };

                if peek_token.kind == lexer::TokenKind::Semicolon {
                    break left_expr;
                }

                let peek_op_precedence = &Precedence::by_token_kind(&peek_token.kind);

                if prev_op_precedence >= peek_op_precedence {
                    // This implies that prev_op will close the parenthesis with left_expr, such as `(... <prev_op> left_expr)`.
                    // Since prev_op possesses higher binding power,
                    //
                    break left_expr;
                }

                // We are aware that the next operator has higher precedence, so we construct the next infix expression.
                // This is equivalent to opening a new parentheses like `<prev_op> (left_expr <peek_op> right_expr)`
                // Because left_expr will be inside the returned expression, one level deeper than if left_expr were returned from this loop
                //
                let within_expr = self.parse_expression_within(left_expr)?;

                left_expr = within_expr;
            }
        };

        Some(expr)
    }

    fn parse_expression_left(&mut self) -> Option<Expression<'i>> {
        use crate::lexer::TokenKind::*;

        match &self.lexer.peek()?.kind {
            Minus | Bang => self.parse_prefix(),
            Ident(_) => self.parse_identifier(),
            Integer(_) => self.parse_integer(),
            Float(_) => self.parse_float(),
            Str(_) => self.parse_str(),
            True | False => self.parse_boolean(),
            LeftParen => self.parse_grouped(),
            LeftBracket => self.parse_array(),
            LeftBrace => self.parse_map(),
            If => self.parse_if(),
            Fn => self.parse_fn(),
            kind => panic!("no parse_expression_left was found for {kind:?}"),
        }
    }

    fn parse_expression_within(&mut self, left: Expression<'i>) -> Option<Expression<'i>> {
        use crate::lexer::TokenKind::*;

        match &self.lexer.peek()?.kind {
            Equal | NotEqual | Minus | Plus | Asterisk | Slash | Less | Greater | LessEqual
            | GreaterEqual => self.parse_infix_within(left),

            LeftParen => self.parse_call_within(left),

            LeftBracket => self.parse_indexing_within(left),

            kind => panic!("no parse_infix for token_kind = {kind:?} was found"),
        }
    }

    fn parse_prefix(&mut self) -> Option<Expression<'i>> {
        let op = match self.lexer.next()? {
            lexer::Token {
                kind: lexer::TokenKind::Minus | lexer::TokenKind::Bang,
                input_slice,
            } => input_slice,

            token => panic!("parse_prefix do not implemented for {:?}", token),
        };

        let right_expr = self.parse_expression(&Precedence::Prefix)?;

        Some(Expression::Prefix {
            op,
            right: Box::new(right_expr),
        })
    }

    fn parse_infix_within(&mut self, left: Expression<'i>) -> Option<Expression<'i>> {
        let left = left;

        let op = self.lexer.next()?;

        let op_precedence = Precedence::by_token_kind(&op.kind);

        let right = self.parse_expression(&op_precedence)?;

        Some(Expression::Infix {
            left: Box::new(left),
            op: op.input_slice,
            right: Box::new(right),
        })
    }

    fn parse_identifier(&mut self) -> Option<Expression<'i>> {
        let name = match self.next_expect(&lexer::TokenKind::Ident(DUMMY_STR))? {
            lexer::Token {
                kind: lexer::TokenKind::Ident(name),
                ..
            } => name,

            _ => unreachable!("checked in next_expect"),
        };

        Some(Expression::Identifier(name))
    }

    fn parse_integer(&mut self) -> Option<Expression<'i>> {
        let num = match self.next_expect(&lexer::TokenKind::Integer(DUMMY_NUM))? {
            lexer::Token {
                kind: lexer::TokenKind::Integer(num),
                ..
            } => num,

            _ => unreachable!("checked in next_expect"),
        };

        Some(Expression::Integer(num))
    }

    fn parse_float(&mut self) -> Option<Expression<'i>> {
        let float = match self.next_expect(&lexer::TokenKind::Float(DUMMY_FLOAT))? {
            lexer::Token {
                kind: lexer::TokenKind::Float(float),
                ..
            } => float,

            _ => unreachable!("checked in next_expect"),
        };

        Some(Expression::Float(float))
    }

    fn parse_str(&mut self) -> Option<Expression<'i>> {
        let str = match self.next_expect(&lexer::TokenKind::Str(DUMMY_STR))? {
            lexer::Token {
                kind: lexer::TokenKind::Str(str),
                ..
            } => str,

            _ => unreachable!("checked in next_expect"),
        };

        Some(Expression::Str(str))
    }

    fn parse_boolean(&mut self) -> Option<Expression<'i>> {
        let value = match self.lexer.next()? {
            lexer::Token {
                kind: lexer::TokenKind::True,
                ..
            } => true,

            lexer::Token {
                kind: lexer::TokenKind::False,
                ..
            } => false,

            token => unreachable!(
                "parse_boolean should not be called for non boolean tokens, instead called for {:?}",
                token
            ),
        };

        Some(Expression::Bool(value))
    }

    fn parse_grouped(&mut self) -> Option<Expression<'i>> {
        self.next_expect(&lexer::TokenKind::LeftParen)?;

        let expr = self.parse_expression(&Precedence::Lowest)?;

        self.next_expect(&lexer::TokenKind::RightParen)?;

        Some(expr)
    }

    fn parse_array(&mut self) -> Option<Expression<'i>> {
        let mut elements = vec![];

        self.next_expect(&lexer::TokenKind::LeftBracket)?;

        if self.skip_expect(&lexer::TokenKind::RightBracket) {
            return Some(Expression::Array(elements));
        }

        loop {
            let expr = self.parse_expression(&Precedence::Lowest)?;
            elements.push(expr);

            if !self.skip_expect(&lexer::TokenKind::Comma) {
                break;
            }
        }

        self.next_expect(&lexer::TokenKind::RightBracket)?;

        Some(Expression::Array(elements))
    }

    fn parse_map(&mut self) -> Option<Expression<'i>> {
        let mut keys_values = vec![];

        self.next_expect(&lexer::TokenKind::LeftBrace)?;

        if self.skip_expect(&lexer::TokenKind::RightBrace) {
            return Some(Expression::Map(keys_values));
        }

        loop {
            let key = self.parse_expression(&Precedence::Lowest)?;
            self.next_expect(&lexer::TokenKind::Colon)?;
            let value = self.parse_expression(&Precedence::Lowest)?;

            keys_values.push((key, value));

            if !self.skip_expect(&lexer::TokenKind::Comma) {
                break;
            }
        }

        self.next_expect(&lexer::TokenKind::RightBrace)?;

        Some(Expression::Map(keys_values))
    }

    fn parse_if(&mut self) -> Option<Expression<'i>> {
        self.next_expect(&lexer::TokenKind::If)?;

        let condition = Box::new(self.parse_grouped()?);

        let yes = Box::new(self.parse_block()?);
        let no = {
            match self.lexer.peek() {
                Some(token) if token.kind == lexer::TokenKind::Else => {
                    self.next_expect(&lexer::TokenKind::Else)
                        .expect("checked in match arm");

                    Some(Box::new(self.parse_block()?))
                }

                _ => None,
            }
        };

        Some(Expression::If { condition, yes, no })
    }

    fn parse_fn(&mut self) -> Option<Expression<'i>> {
        self.next_expect(&lexer::TokenKind::Fn)?;

        let parameters = self.parse_fn_params()?;

        let body = Box::new(self.parse_block()?);

        Some(Expression::Fn {
            parameters,
            body,
            name: None,
        })
    }

    fn parse_fn_params(&mut self) -> Option<Vec<Expression<'i>>> {
        let mut params = vec![];

        self.next_expect(&lexer::TokenKind::LeftParen)?;

        if self.skip_expect(&lexer::TokenKind::RightParen) {
            return Some(params);
        }

        loop {
            let ident = self.parse_identifier()?;
            params.push(ident);

            if !self.skip_expect(&lexer::TokenKind::Comma) {
                break;
            }
        }

        self.next_expect(&lexer::TokenKind::RightParen)?;

        Some(params)
    }

    fn parse_call_within(&mut self, function: Expression<'i>) -> Option<Expression<'i>> {
        let arguments = self.parse_call_args()?;

        Some(Expression::Call {
            function: Box::new(function),
            arguments,
        })
    }

    fn parse_indexing_within(&mut self, left: Expression<'i>) -> Option<Expression<'i>> {
        self.next_expect(&lexer::TokenKind::LeftBracket)?;

        let index = self.parse_expression(&Precedence::Lowest)?;

        self.next_expect(&lexer::TokenKind::RightBracket)?;

        Some(Expression::Indexing {
            left: Box::new(left),
            index: Box::new(index),
        })
    }

    fn parse_call_args(&mut self) -> Option<Vec<Expression<'i>>> {
        let mut params = vec![];

        self.next_expect(&lexer::TokenKind::LeftParen)?;

        if self.skip_expect(&lexer::TokenKind::RightParen) {
            return Some(params);
        }

        loop {
            let expr = self.parse_expression(&Precedence::Lowest)?;
            params.push(expr);

            if !self.skip_expect(&lexer::TokenKind::Comma) {
                break;
            }
        }

        self.next_expect(&lexer::TokenKind::RightParen)?;

        Some(params)
    }
}

impl<'i> Iterator for Parser<'i> {
    type Item = Statement<'i>;

    fn next(&mut self) -> Option<Self::Item> {
        self.parse_next()
    }
}

#[cfg(test)]
mod parser_tests {
    use super::{Expression::*, Statement::*, *};

    fn test_structure<'i>(cases: Vec<(impl AsRef<str>, Vec<Statement<'i>>)>) {
        for (input, exp_program) in cases {
            let input = input.as_ref();
            let lexer = Lexer::new(&input);
            let mut parser = Parser::new(lexer);

            let program: Vec<Statement> = (&mut parser).collect();

            assert_eq!(
                parser.errors.len(),
                0,
                "Parser has {} errors: {:?}",
                parser.errors.len(),
                parser.errors
            );

            assert_eq!(program, exp_program);

            assert_eq!(parser.parse_next(), None);
        }
    }

    fn test_display(cases: Vec<(impl AsRef<str>, impl AsRef<str>)>) {
        for (input, exp_program_display) in cases {
            let input = input.as_ref();
            let lexer = Lexer::new(&input);
            let mut parser = Parser::new(lexer);

            let program: Vec<Statement> = (&mut parser).collect();

            assert_eq!(
                parser.errors.len(),
                0,
                "Parser has {} errors: {:?}",
                parser.errors.len(),
                parser.errors
            );

            let program_display = program.iter().fold("".to_string(), |mut res, stmn| {
                res.push_str(&stmn.to_string());
                res
            });

            assert_eq!(program_display.trim(), exp_program_display.as_ref());

            assert_eq!(parser.parse_next(), None);
        }
    }

    #[test]
    fn let_expr() {
        let cases = vec![(
            "let LET_NAME = LET_EXPR_RIGHT;",
            vec![Let {
                name: "LET_NAME",
                expr: Identifier("LET_EXPR_RIGHT"),
            }],
        )];

        test_structure(cases);
    }

    #[test]
    fn return_expr() {
        let cases = vec![(
            "return EXPR;",
            vec![Return {
                expr: Identifier("EXPR"),
            }],
        )];

        test_structure(cases);
    }

    #[test]
    fn identifier_expr() {
        let cases = vec![(
            "JUST_IDENT;",
            vec![ExprStmn {
                expr: Identifier("JUST_IDENT"),
            }],
        )];

        test_structure(cases);
    }

    #[test]
    fn integer_expr() {
        let cases = vec![
            ("5;", vec![ExprStmn { expr: Integer(5) }]),
            ("98;", vec![ExprStmn { expr: Integer(98) }]),
        ];

        test_structure(cases);
    }

    #[test]
    fn bool_expr() {
        let cases = vec![
            ("true;", vec![ExprStmn { expr: Bool(true) }]),
            ("false;", vec![ExprStmn { expr: Bool(false) }]),
        ];

        test_structure(cases);
    }

    #[test]
    fn prefix_expr() {
        let cases = vec![
            (
                "-5;",
                vec![ExprStmn {
                    expr: Prefix {
                        op: "-",
                        right: Box::new(Integer(5)),
                    },
                }],
            ),
            (
                "!5;",
                vec![ExprStmn {
                    expr: Prefix {
                        op: "!",
                        right: Box::new(Integer(5)),
                    },
                }],
            ),
        ];

        test_structure(cases);
    }

    #[test]
    fn if_else_expr() {
        let cases = vec![
            (
                "if (x > y) { x; } else { y; }",
                vec![ExprStmn {
                    expr: If {
                        condition: Box::new(Infix {
                            left: Box::new(Identifier("x")),
                            op: ">",
                            right: Box::new(Identifier("y")),
                        }),
                        yes: Box::new(Block {
                            statements: vec![ExprStmn {
                                expr: Identifier("x"),
                            }],
                        }),
                        no: Some(Box::new(Block {
                            statements: vec![ExprStmn {
                                expr: Identifier("y"),
                            }],
                        })),
                    },
                }],
            ),
            (
                "if (x > y) { x; }",
                vec![ExprStmn {
                    expr: If {
                        condition: Box::new(Infix {
                            left: Box::new(Identifier("x")),
                            op: ">",
                            right: Box::new(Identifier("y")),
                        }),
                        yes: Box::new(Block {
                            statements: vec![ExprStmn {
                                expr: Identifier("x"),
                            }],
                        }),
                        no: None,
                    },
                }],
            ),
        ];

        test_structure(cases);
    }

    #[test]
    fn function_expr() {
        let cases = vec![
            (
                "fn(x, y) { x + y; }",
                vec![ExprStmn {
                    expr: Fn {
                        name: None,
                        parameters: vec![Identifier("x"), Identifier("y")],
                        body: Box::new(Block {
                            statements: vec![ExprStmn {
                                expr: Infix {
                                    left: Box::new(Identifier("x")),
                                    op: "+",
                                    right: Box::new(Identifier("y")),
                                },
                            }],
                        }),
                    },
                }],
            ),
            (
                "fn() { x + y; }",
                vec![ExprStmn {
                    expr: Fn {
                        name: None,
                        parameters: vec![],
                        body: Box::new(Block {
                            statements: vec![ExprStmn {
                                expr: Infix {
                                    left: Box::new(Identifier("x")),
                                    op: "+",
                                    right: Box::new(Identifier("y")),
                                },
                            }],
                        }),
                    },
                }],
            ),
            (
                "fn(x, y) {}",
                vec![ExprStmn {
                    expr: Fn {
                        name: None,
                        parameters: vec![Identifier("x"), Identifier("y")],
                        body: Box::new(Block { statements: vec![] }),
                    },
                }],
            ),
        ];

        test_structure(cases);
    }

    #[test]
    fn call_expr() {
        let cases = vec![
            (
                "fn(x, y) { x + y; }(a, b);",
                vec![ExprStmn {
                    expr: Call {
                        function: Box::new(Fn {
                            name: None,
                            parameters: vec![Identifier("x"), Identifier("y")],
                            body: Box::new(Block {
                                statements: vec![ExprStmn {
                                    expr: Infix {
                                        left: Box::new(Identifier("x")),
                                        op: "+",
                                        right: Box::new(Identifier("y")),
                                    },
                                }],
                            }),
                        }),
                        arguments: vec![Identifier("a"), Identifier("b")],
                    },
                }],
            ),
            (
                "add(a, b);",
                vec![ExprStmn {
                    expr: Call {
                        function: Box::new(Identifier("add")),
                        arguments: vec![Identifier("a"), Identifier("b")],
                    },
                }],
            ),
            (
                "add(3 * 4, 9 + 0 * 9);",
                vec![ExprStmn {
                    expr: Call {
                        function: Box::new(Identifier("add")),
                        arguments: vec![
                            Infix {
                                left: Box::new(Integer(3)),
                                op: "*",
                                right: Box::new(Integer(4)),
                            },
                            Infix {
                                left: Box::new(Integer(9)),
                                op: "+",
                                right: Box::new(Infix {
                                    left: Box::new(Integer(0)),
                                    op: "*",
                                    right: Box::new(Integer(9)),
                                }),
                            },
                        ],
                    },
                }],
            ),
        ];

        test_structure(cases);
    }

    #[test]
    fn infix_expr_simple() {
        let cases = vec!["+", "-", "*", "/", ">", "<", "==", "!="]
            .into_iter()
            .map(|op| {
                (
                    format!("5 {op} 5;"),
                    vec![ExprStmn {
                        expr: Infix {
                            left: Box::new(Integer(5)),
                            op,
                            right: Box::new(Integer(5)),
                        },
                    }],
                )
            })
            .collect();

        test_structure(cases);
    }

    #[test]
    fn infix_expr_hard() {
        let cases = vec![
            ("-a * b;", "((-a) * b);"),
            ("-a + b * c;", "((-a) + (b * c));"),
            ("-a * b + c;", "(((-a) * b) + c);"),
            ("a + b + c;", "((a + b) + c);"),
            ("a * b * c;", "((a * b) * c);"),
            ("a * b / c;", "((a * b) / c);"),
            ("5 > 4 == 3 < 4;", "((5 > 4) == (3 < 4));"),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5;",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)));",
            ),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5;",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)));",
            ),
        ];

        test_display(cases);
    }

    #[test]
    fn operator_precedence_power() {
        let cases = vec![
            ("true;", "true;"),
            ("false;", "false;"),
            ("3 > 5 == false;", "((3 > 5) == false);"),
            ("3 < 5 == true;", "((3 < 5) == true);"),
            ("1 + (2 + 3) + 4;", "((1 + (2 + 3)) + 4);"),
            ("(5 + 5) * 2;", "((5 + 5) * 2);"),
            ("2 / (5 + 5);", "(2 / (5 + 5));"),
            ("-(5 + 5);", "(-(5 + 5));"),
            ("!(true == true);", "(!(true == true));"),
        ];

        test_display(cases);
    }

    #[test]
    fn array() {
        let cases = vec![
            (
                "[1, 2, 3, \"hello\", 3 + 3];",
                vec![ExprStmn {
                    expr: Array(vec![
                        Integer(1),
                        Integer(2),
                        Integer(3),
                        Str("hello"),
                        Infix {
                            left: Box::new(Integer(3)),
                            op: "+",
                            right: Box::new(Integer(3)),
                        },
                    ]),
                }],
            ),
            (
                "[1, 2, 3, \"hello\", 3 + 3][2];",
                vec![ExprStmn {
                    expr: Indexing {
                        left: Box::new(Array(vec![
                            Integer(1),
                            Integer(2),
                            Integer(3),
                            Str("hello"),
                            Infix {
                                left: Box::new(Integer(3)),
                                op: "+",
                                right: Box::new(Integer(3)),
                            },
                        ])),
                        index: Box::new(Integer(2)),
                    },
                }],
            ),
        ];

        test_structure(cases);
    }

    #[test]
    fn map() {
        let cases = vec![
            (
                "let r = {};",
                vec![Let {
                    name: "r",
                    expr: Map(vec![]),
                }],
            ),
            (
                "let m = {1: 2, 3: \"hello\", \"sld\": 4};",
                vec![Let {
                    name: "m",
                    expr: Map(vec![
                        (Integer(1), Integer(2)),
                        (Integer(3), Str("hello")),
                        (Str("sld"), Integer(4)),
                    ]),
                }],
            ),
        ];

        test_structure(cases);
    }

    #[test]
    fn dbg() {
        let input = "
--1 * 2[i](abc);

add(3 * 4, 9 + 0 * 9);

let fn_name = fn(x, y) {
    x + y; 
    arr[i] + 25;
    true;

    if (9 < 8) {
        identi;
    } else {
        g[9];
    }
};

-5;

[1, 2, 3][5 - 1];
";
        let lexer = lexer::Lexer::new(input);
        let mut parser = Parser::new(lexer);

        let program: Vec<Statement> = (&mut parser).collect();

        dbg!(parser.errors);
        let program_string = program.iter().fold("".to_string(), |mut res, cur| {
            res.push_str(&cur.to_string());
            res
        });
        //
        //dbg!(&program);

        println!("\nRecovered after parsing:\n");
        println!("{program_string}");
    }
}
