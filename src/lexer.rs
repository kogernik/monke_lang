use std::{
    iter::Peekable,
    ops::{Deref, Not},
    str::Chars,
};

use serde::{Deserialize, Serialize};

use crate::monke_error::MonkeError;

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
pub enum TokenKind<'i> {
    // Meta
    Illegal,
    Eof,
    Comment,

    // Keywords
    Fn,
    Let,
    True,
    False,
    If,
    Else,
    Return,

    // Delimiters
    Comma,
    Semicolon,
    Colon,
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
    Whitespace,

    // Operators
    Assign,
    Dot,
    Plus,
    Minus,
    Bang,
    Asterisk,
    Slash,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
    NotEqual,

    // Compound
    Integer(isize),
    Float(f64),
    Str(&'i str),

    // Identifiers
    Ident(&'i str),
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct Token<'i> {
    pub kind: TokenKind<'i>,
    pub input_slice: &'i str,
}

impl<'i> Token<'i> {
    pub fn new(kind: TokenKind<'i>, input_slice: &'i str) -> Self {
        Self { kind, input_slice }
    }
}

#[derive(Debug)]
pub struct Lexer<'i> {
    input: &'i str,
    to_process: &'i str,
    chars_iter: Peekable<Chars<'i>>,
}

impl<'i> Lexer<'i> {
    pub fn new(input: &'i str) -> Self {
        Self {
            input,
            to_process: input,
            chars_iter: input.chars().peekable(),
        }
    }

    fn next_on(&mut self, cur_to_process: &'i str) -> Option<Token<'i>> {
        let (kind, input_slice) = match self.chars_iter.peek()? {
            peek_ch if peek_ch.is_whitespace() => self.next_whitespace(&cur_to_process),

            '"' => self.next_string(&cur_to_process),

            'A'..='Z' | 'a'..='z' | '_' => self.next_identifier(&cur_to_process),

            '0'..='9' => self.next_number(&cur_to_process),

            '=' => self
                .next_if_ch('=', TokenKind::Equal, &cur_to_process)
                .unwrap_or((TokenKind::Assign, &cur_to_process[..1])),
            '=' => self
                .next_if_ch('=', TokenKind::Equal, &cur_to_process)
                .unwrap_or((TokenKind::Assign, &cur_to_process[..1])),
            '!' => self
                .next_if_ch('=', TokenKind::NotEqual, &cur_to_process)
                .unwrap_or((TokenKind::Bang, &cur_to_process[..1])),
            '<' => self
                .next_if_ch('=', TokenKind::LessEqual, &cur_to_process)
                .unwrap_or((TokenKind::Less, &cur_to_process[..1])),
            '>' => self
                .next_if_ch('=', TokenKind::GreaterEqual, &cur_to_process)
                .unwrap_or((TokenKind::Greater, &cur_to_process[..1])),

            '/' => self
                .next_try_comment(&cur_to_process)
                .unwrap_or((TokenKind::Slash, &cur_to_process[..1])),

            _ => match self.chars_iter.next().expect("checked in peek above") {
                '+' => (TokenKind::Plus, &cur_to_process[..1]),
                '-' => (TokenKind::Minus, &cur_to_process[..1]),
                '.' => (TokenKind::Dot, &cur_to_process[..1]),
                '{' => (TokenKind::LeftBrace, &cur_to_process[..1]),
                '}' => (TokenKind::RightBrace, &cur_to_process[..1]),
                '(' => (TokenKind::LeftParen, &cur_to_process[..1]),
                ')' => (TokenKind::RightParen, &cur_to_process[..1]),
                '[' => (TokenKind::LeftBracket, &cur_to_process[..1]),
                ']' => (TokenKind::RightBracket, &cur_to_process[..1]),
                ',' => (TokenKind::Comma, &cur_to_process[..1]),
                ';' => (TokenKind::Semicolon, &cur_to_process[..1]),
                ':' => (TokenKind::Colon, &cur_to_process[..1]),
                '*' => (TokenKind::Asterisk, &cur_to_process[..1]),

                _ => panic!("Got unexpected char:\n {}", &cur_to_process[..10]),
            },
        };

        let token = Token { kind, input_slice };
        self.to_process = &cur_to_process[token.input_slice.len()..];

        Some(token)
    }

    fn next_if_ch(
        &mut self,
        check_ch: char,
        kind: TokenKind<'i>,
        cur_to_process: &'i str,
    ) -> Option<(TokenKind<'i>, &'i str)> {
        self.chars_iter.next().expect("should not be called on EOF");

        if self.chars_iter.peek()? == &check_ch {
            assert!(cur_to_process.len() >= 2,);

            self.chars_iter.next();
            Some((kind, &cur_to_process[..2]))
        } else {
            None
        }
    }

    fn next_try_comment(&mut self, cur_to_process: &'i str) -> Option<(TokenKind<'i>, &'i str)> {
        self.chars_iter
            .next_if_eq(&'/')
            .expect("should be called only for comments that start with '/'");

        match self.chars_iter.peek() {
            Some('/') => {
                self.chars_iter
                    .next_if_eq(&'/')
                    .expect("checked in match arm");

                let comment_len = self
                    .chars_iter
                    .by_ref()
                    .take_while(|ch| *ch != '\n')
                    .count()
                    + 2;

                Some((TokenKind::Comment, &cur_to_process[..comment_len]))
            }
            _ => None,
        }
    }

    fn next_string(&mut self, cur_to_process: &'i str) -> (TokenKind<'i>, &'i str) {
        self.chars_iter
            .next_if_eq(&'"')
            .expect("next_string should be called only for strings that start with '\"'");

        // using cur_to_process[1..].find('"') will not move iter
        match self
            .chars_iter
            .by_ref()
            .enumerate()
            .find(|(_, ch)| '"'.eq(ch))
        {
            Some((str_len, _)) => {
                // take &str without ""
                let kind = TokenKind::Str(&cur_to_process[1..str_len + 1]);
                // take &str with ""
                let input_slice = &cur_to_process[0..=str_len + 1];

                (kind, input_slice)
            }

            None => (TokenKind::Illegal, &cur_to_process[..]),
        }
    }

    fn next_number(&mut self, cur_to_process: &'i str) -> (TokenKind<'i>, &'i str) {
        assert!(
            matches!(self.chars_iter.peek(), Some('0'..='9')),
            "next_number should be called only for numeric chars"
        );

        // `find` consume element that return false in predicate
        // so instead from_fn with next_if
        let int_len =
            std::iter::from_fn(|| self.chars_iter.by_ref().next_if(|ch| ch.is_ascii_digit()))
                .count();

        assert!(int_len > 0, "expecting int_len > 0 because of prev assert!");

        let frac_len = match (self.chars_iter.next(), self.chars_iter.peek()) {
            (Some('.'), Some('0'..='9')) => {
                std::iter::from_fn(|| self.chars_iter.by_ref().next_if(|ch| ch.is_ascii_digit()))
                    .count()
            }

            _ => {
                // cannot construct frac part, revert chars_iter as it was before match block
                self.chars_iter = cur_to_process[int_len..].chars().peekable();

                0
            }
        };

        if frac_len > 0 {
            let float_len = int_len + 1 + frac_len;

            let num = cur_to_process[..float_len]
                .parse()
                .expect("int_len > 0 and frac_len > 0");

            let kind = TokenKind::Float(num);

            let input_slice = &cur_to_process[..float_len];

            (kind, input_slice)
        } else {
            let num = cur_to_process[..int_len].parse().expect("int_len > 0");

            let kind = TokenKind::Integer(num);

            let input_slice = &cur_to_process[..int_len];

            (kind, input_slice)
        }
    }

    fn next_identifier(&mut self, cur_to_process: &'i str) -> (TokenKind<'i>, &'i str) {
        let ident_len = std::iter::from_fn(|| {
            self.chars_iter
                .by_ref()
                .next_if(|ch| matches!(ch, 'a'..='z' | 'A'..='Z' | '0'..='9' | '_'))
        })
        .count();

        let ident_literal = &cur_to_process[..ident_len];

        let token_kind = match ident_literal {
            "let" => TokenKind::Let,
            "fn" => TokenKind::Fn,
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            "if" => TokenKind::If,
            "else" => TokenKind::Else,
            "return" => TokenKind::Return,

            _ => TokenKind::Ident(ident_literal),
        };

        (token_kind, ident_literal)
    }

    fn next_whitespace(&mut self, cur_to_process: &'i str) -> (TokenKind<'i>, &'i str) {
        let whitespace_len =
            std::iter::from_fn(|| self.chars_iter.by_ref().next_if(|ch| ch.is_whitespace()))
                .count();

        let kind = TokenKind::Whitespace;
        let input_slice = &cur_to_process[..whitespace_len];

        (kind, input_slice)
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let token = self.next_on(&self.to_process)?;

            if matches!(token.kind, TokenKind::Whitespace | TokenKind::Comment).not() {
                break Some(token);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::TokenKind::*;
    use crate::lexer::*;

    fn fold_to_tokens_and_string<'a>(lexer: &'a mut Lexer) -> (Vec<TokenKind<'a>>, String) {
        lexer.fold(
            (Vec::new(), String::new()),
            |(mut tokens, mut chs), next_token| {
                if next_token.kind != TokenKind::Whitespace {
                    tokens.push(next_token.kind);
                }

                chs.push_str(next_token.input_slice);

                (tokens, chs)
            },
        )
    }

    #[test]
    fn one_char() {
        let input = "-=+(){},;.";
        dbg!(input);

        let mut lexer = Lexer::new(input);

        let (tokens, string_from_tokens) = fold_to_tokens_and_string(&mut lexer);

        assert_eq!(input, string_from_tokens);
        assert_eq!(
            tokens,
            vec![
                Minus, Assign, Plus, LeftParen, RightParen, LeftBrace, RightBrace, Comma,
                Semicolon, Dot
            ]
        );
    }

    #[test]
    fn one_char_with_numbers() {
        let input = "143+=3-4+98-{-10000},;";
        dbg!(input);

        let mut lexer = Lexer::new(input);

        let (tokens, string_from_tokens) = fold_to_tokens_and_string(&mut lexer);

        assert_eq!(input, string_from_tokens);
        assert_eq!(
            tokens,
            vec![
                Integer(143),
                Plus,
                Assign,
                Integer(3),
                Minus,
                Integer(4),
                Plus,
                Integer(98),
                Minus,
                LeftBrace,
                Minus,
                Integer(10000),
                RightBrace,
                Comma,
                Semicolon
            ]
        )
    }

    mod float_number {
        use super::*;

        #[test]
        fn float_numbers() {
            let input = "143.546,0.00100+=3.14-{-10000.98145},;";
            dbg!(input);

            let mut lexer = Lexer::new(input);
            let (tokens, string_from_tokens) = fold_to_tokens_and_string(&mut lexer);

            assert_eq!(input, string_from_tokens);
            assert_eq!(
                tokens,
                vec![
                    Float(143.546),
                    Comma,
                    Float(0.001),
                    Plus,
                    Assign,
                    Float(3.14),
                    Minus,
                    LeftBrace,
                    Minus,
                    Float(10000.98145),
                    RightBrace,
                    Comma,
                    Semicolon
                ]
            )
        }

        #[test]
        fn sequence_of_dots() {
            let input = "143..546.1.34...89.43";
            dbg!(input);

            let mut lexer = Lexer::new(input);

            let (tokens, string_from_tokens) = fold_to_tokens_and_string(&mut lexer);

            assert_eq!(input, string_from_tokens);
            assert_eq!(
                tokens,
                vec![
                    Integer(143),
                    Dot,
                    Dot,
                    Float(546.1),
                    Dot,
                    Integer(34),
                    Dot,
                    Dot,
                    Dot,
                    Float(89.43)
                ]
            );
        }
    }

    #[test]
    fn one_char_with_string() {
        let input = "{(\"qqq\")\"Hello, world\";}+=";
        dbg!(input);

        let mut lexer = Lexer::new(input);

        let (tokens, string_from_tokens) = fold_to_tokens_and_string(&mut lexer);

        assert_eq!(input, string_from_tokens);
        assert_eq!(
            tokens,
            vec![
                LeftBrace,
                LeftParen,
                Str("qqq"),
                RightParen,
                Str("Hello, world"),
                Semicolon,
                RightBrace,
                Plus,
                Assign
            ]
        )
    }

    #[test]
    fn broken_string() {
        let input = "(\"qqq123";
        dbg!(input);

        let mut lexer = Lexer::new(input);

        assert_eq!(
            lexer.next().unwrap(),
            Token {
                kind: LeftParen,
                input_slice: "("
            }
        );

        assert_eq!(
            lexer.next().unwrap(),
            Token {
                kind: Illegal,
                input_slice: "\"qqq123"
            }
        );
    }

    #[test]
    fn actual_monkey_lang() {
        let input = "\
            let five = 5;
            let ten = 10;
               let add = fn(x, y) {
                 x + y;
            };
            let result = add(five, ten);
            !-/*5;
            5 < 10 > 5;

            [1, 2, 3];

            { 1: 2, 3: 4 };


            if (5 < 10) {
               return true;
            } else {
               return false;
            }

            10 == 10; 10 != 9;
";

        let mut lexer = Lexer::new(input);
        let (tokens, string_from_tokens) = fold_to_tokens_and_string(&mut lexer);

        #[rustfmt::skip]
        let expected = vec![
            Let, Ident("five"), Assign, Integer(5), Semicolon,

            Let, Ident("ten"), Assign, Integer(10), Semicolon,

            Let, Ident("add"), Assign, Fn, LeftParen, Ident("x"), Comma, Ident("y"), RightParen, LeftBrace,
                Ident("x"), Plus, Ident("y"), Semicolon,
            RightBrace, Semicolon,

            Let, Ident("result"), Assign, Ident("add"), LeftParen, Ident("five"), Comma, Ident("ten"), RightParen, Semicolon,

            Bang, Minus, Slash, Asterisk, Integer(5), Semicolon,

            Integer(5), Less, Integer(10), Greater, Integer(5), Semicolon,

            LeftBracket, Integer(1), Comma, Integer(2), Comma, Integer(3), RightBracket, Semicolon,

            LeftBrace, Integer(1), Colon, Integer(2), Comma, Integer(3), Colon, Integer(4), RightBrace, Semicolon,

            If, LeftParen, Integer(5), Less, Integer(10), RightParen, LeftBrace,
                Return, True, Semicolon,
            RightBrace, Else, LeftBrace,
                Return, False, Semicolon,
            RightBrace,

            Integer(10), Equal, Integer(10), Semicolon,
            Integer(10), NotEqual, Integer(9), Semicolon,
        ];

        for (expected_tk, lexer_tk) in expected.chunks(15).zip(tokens.chunks(15)) {
            assert_eq!(expected_tk, lexer_tk);
        }
    }
}
