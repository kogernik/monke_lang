use std::collections::HashMap;
use std::sync::LazyLock;

use super::op_code::{OP_CODE_LEN, OpCode};

#[derive(Debug, Clone)]
pub struct Meta {
    pub name: String,
    pub operand_widths: Vec<OperandWidth>,
    pub op_bytes_width: usize,
}

impl From<(&str, Vec<OperandWidth>, usize)> for Meta {
    fn from(value: (&str, Vec<OperandWidth>, usize)) -> Self {
        let (name, operand_widths, op_bytes_width) = value;

        Meta {
            name: name.to_string(),
            operand_widths,
            op_bytes_width,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum OperandWidth {
    OneByte = 1,
    TwoBytes = 2,
}

#[rustfmt::skip]
pub static OP_CODE_META: LazyLock<HashMap<OpCode, Meta>> = LazyLock::new(|| {
    [
        (OpCode::Null, ("Null", vec![])),
        (OpCode::Pop, ("Pop", vec![])),
        (OpCode::Constant, ("Constant", vec![OperandWidth::TwoBytes /* idx in Compiler.constants and VM.constants */])),

        (OpCode::GetGlobal, ("GetGlobal", vec![OperandWidth::TwoBytes /* idx in VM.globals */])),
        (OpCode::SetGlobal, ("SetGlobal", vec![OperandWidth::TwoBytes /* idx in VM.globals */])),

        (OpCode::GetLocal, ("GetLocal", vec![OperandWidth::OneByte /* idx from Frame.base_pointer */])),
        (OpCode::SetLocal, ("SetLocal", vec![OperandWidth::OneByte /* idx from Frame.base_pointer */])),

        (OpCode::GetBuiltin, ("GetBuiltin", vec![OperandWidth::OneByte /* idx of BUILTIN_FNS */])),

        (OpCode::GetFree, ("GetFree", vec![OperandWidth::OneByte /* idx of free in Object::Closure.free_vars */])),

        (OpCode::Add, ("Add", vec![])),
        (OpCode::Sub, ("Sub", vec![])),
        (OpCode::Mul, ("Mul", vec![])),
        (OpCode::Div, ("Div", vec![])),

        (OpCode::True, ("True", vec![])),
        (OpCode::False, ("False", vec![])),

        (OpCode::Equal, ("Equal", vec![])),
        (OpCode::NotEqual, ("NotEqual", vec![])),
        (OpCode::Greater, ("Greater", vec![])),
        (OpCode::GreaterEqual, ("GreaterEqual", vec![])),

        (OpCode::Bang, ("Bang", vec![])),
        (OpCode::Minus, ("Minus", vec![])),

        (OpCode::JumpNotTrue, ("JumpNotTrue", vec![OperandWidth::TwoBytes, /* idx in Bytecode */])),
        (OpCode::Jump, ("Jump", vec![OperandWidth::TwoBytes /* idx in Bytecode */])),
        
        (OpCode::Array, ("Array", vec![OperandWidth::TwoBytes /* len of args */])),
        (OpCode::Map, ("Map", vec![OperandWidth::TwoBytes /* num of keys + values */])), 
        (OpCode::Indexing, ("Index", vec![])),

        (OpCode::CurrentClosure, ("CurrentClosure", vec![])),
        (OpCode::Closure, ("Closure", vec![OperandWidth::TwoBytes /* constant index */, OperandWidth::OneByte /* num of free vars */])),
        (OpCode::Call, ("Call", vec![OperandWidth::OneByte /* num of args */])),
        (OpCode::ReturnValue, ("ReturnValue", vec![])),
        (OpCode::ReturnNull, ("ReturnNull", vec![])),
    ]
    .into_iter()
    .map(|(op_code, (name, operand_widths))| {
        let op_bytes_width = OP_CODE_LEN + operand_widths.iter().map(|width| *width as usize).sum::<usize>();
        (op_code, Meta::from((name, operand_widths, op_bytes_width)))
    })
    .collect()
});
