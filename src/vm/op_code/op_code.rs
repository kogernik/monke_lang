use std::backtrace::Backtrace;

use crate::{monke_error::MonkeError, vm::op_code::meta::OperandWidth};

use super::meta::{Meta, OP_CODE_META};

#[derive(Debug, Clone, PartialEq)]
pub enum Operands {
    Placeholder,
    InstrOffset(isize),
    Raw(Vec<isize>),
}

pub const OP_CODE_LEN: usize = 1;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum OpCode {
    Constant,
    Pop,

    SetGlobal,
    GetGlobal,
    SetLocal,
    GetLocal,
    GetBuiltin,
    GetFree,

    Add,
    Sub,
    Mul,
    Div,

    True,
    False,

    Equal,
    NotEqual,
    Greater,
    GreaterEqual,

    Minus,
    Bang,

    JumpNotTrue,
    Jump,

    Array,
    Map,
    Indexing,

    Closure,
    CurrentClosure,
    Call,
    ReturnValue,
    ReturnNull,

    Null,
}

impl TryFrom<u8> for OpCode {
    type Error = ();

    #[inline]
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            value if value == OpCode::Constant as u8 => Ok(OpCode::Constant),
            value if value == OpCode::Pop as u8 => Ok(OpCode::Pop),
            value if value == OpCode::GetGlobal as u8 => Ok(OpCode::GetGlobal),
            value if value == OpCode::SetGlobal as u8 => Ok(OpCode::SetGlobal),
            value if value == OpCode::GetLocal as u8 => Ok(OpCode::GetLocal),
            value if value == OpCode::SetLocal as u8 => Ok(OpCode::SetLocal),
            value if value == OpCode::GetBuiltin as u8 => Ok(OpCode::GetBuiltin),
            value if value == OpCode::GetFree as u8 => Ok(OpCode::GetFree),
            value if value == OpCode::Add as u8 => Ok(OpCode::Add),
            value if value == OpCode::Sub as u8 => Ok(OpCode::Sub),
            value if value == OpCode::Mul as u8 => Ok(OpCode::Mul),
            value if value == OpCode::Div as u8 => Ok(OpCode::Div),
            value if value == OpCode::True as u8 => Ok(OpCode::True),
            value if value == OpCode::False as u8 => Ok(OpCode::False),
            value if value == OpCode::Equal as u8 => Ok(OpCode::Equal),
            value if value == OpCode::NotEqual as u8 => Ok(OpCode::NotEqual),
            value if value == OpCode::Greater as u8 => Ok(OpCode::Greater),
            value if value == OpCode::GreaterEqual as u8 => Ok(OpCode::GreaterEqual),
            value if value == OpCode::Minus as u8 => Ok(OpCode::Minus),
            value if value == OpCode::Bang as u8 => Ok(OpCode::Bang),
            value if value == OpCode::JumpNotTrue as u8 => Ok(OpCode::JumpNotTrue),
            value if value == OpCode::Jump as u8 => Ok(OpCode::Jump),
            value if value == OpCode::Null as u8 => Ok(OpCode::Null),
            value if value == OpCode::Array as u8 => Ok(OpCode::Array),
            value if value == OpCode::Map as u8 => Ok(OpCode::Map),
            value if value == OpCode::Indexing as u8 => Ok(OpCode::Indexing),
            value if value == OpCode::Closure as u8 => Ok(OpCode::Closure),
            value if value == OpCode::CurrentClosure as u8 => Ok(OpCode::CurrentClosure),
            value if value == OpCode::Call as u8 => Ok(OpCode::Call),
            value if value == OpCode::ReturnValue as u8 => Ok(OpCode::ReturnValue),
            value if value == OpCode::ReturnNull as u8 => Ok(OpCode::ReturnNull),

            _ => Err(()),
        }
    }
}

impl TryFrom<&u8> for OpCode {
    type Error = ();

    #[inline]
    fn try_from(value: &u8) -> Result<Self, Self::Error> {
        match value {
            value if *value == OpCode::Pop as u8 => Ok(OpCode::Pop),
            value if *value == OpCode::GetGlobal as u8 => Ok(OpCode::GetGlobal),
            value if *value == OpCode::SetGlobal as u8 => Ok(OpCode::SetGlobal),
            value if *value == OpCode::GetLocal as u8 => Ok(OpCode::GetLocal),
            value if *value == OpCode::SetLocal as u8 => Ok(OpCode::SetLocal),
            value if *value == OpCode::Constant as u8 => Ok(OpCode::Constant),
            value if *value == OpCode::GetBuiltin as u8 => Ok(OpCode::GetBuiltin),
            value if *value == OpCode::GetFree as u8 => Ok(OpCode::GetFree),
            value if *value == OpCode::Add as u8 => Ok(OpCode::Add),
            value if *value == OpCode::Sub as u8 => Ok(OpCode::Sub),
            value if *value == OpCode::Mul as u8 => Ok(OpCode::Mul),
            value if *value == OpCode::Div as u8 => Ok(OpCode::Div),
            value if *value == OpCode::True as u8 => Ok(OpCode::True),
            value if *value == OpCode::False as u8 => Ok(OpCode::False),
            value if *value == OpCode::Equal as u8 => Ok(OpCode::Equal),
            value if *value == OpCode::NotEqual as u8 => Ok(OpCode::NotEqual),
            value if *value == OpCode::Greater as u8 => Ok(OpCode::Greater),
            value if *value == OpCode::GreaterEqual as u8 => Ok(OpCode::GreaterEqual),
            value if *value == OpCode::Minus as u8 => Ok(OpCode::Minus),
            value if *value == OpCode::Bang as u8 => Ok(OpCode::Bang),
            value if *value == OpCode::JumpNotTrue as u8 => Ok(OpCode::JumpNotTrue),
            value if *value == OpCode::Jump as u8 => Ok(OpCode::Jump),
            value if *value == OpCode::Null as u8 => Ok(OpCode::Null),
            value if *value == OpCode::Array as u8 => Ok(OpCode::Array),
            value if *value == OpCode::Map as u8 => Ok(OpCode::Map),
            value if *value == OpCode::Indexing as u8 => Ok(OpCode::Indexing),
            value if *value == OpCode::Closure as u8 => Ok(OpCode::Closure),
            value if *value == OpCode::CurrentClosure as u8 => Ok(OpCode::CurrentClosure),
            value if *value == OpCode::Call as u8 => Ok(OpCode::Call),
            value if *value == OpCode::ReturnValue as u8 => Ok(OpCode::ReturnValue),

            _ => Err(()),
        }
    }
}

impl OpCode {
    pub fn meta(&self) -> &Meta {
        OP_CODE_META.get(self).expect("for all op_codes exist meta")
    }

    pub fn compute_bytes_width(instrs: &[(OpCode, Operands)]) -> usize {
        instrs
            .iter()
            .map(|(op_code, _)| op_code.meta().op_bytes_width)
            .sum()
    }

    pub fn make(op_code: &OpCode, operands: &[isize]) -> Vec<u8> {
        use OperandWidth::*;

        let mut instruction = Vec::with_capacity(op_code.meta().op_bytes_width);

        instruction.push(*op_code as u8);

        for (operand, width) in operands.iter().zip(op_code.meta().operand_widths.iter()) {
            let operand_be_bytes = match *width {
                OneByte => {
                    let operand = u8::try_from(*operand)
                        .expect(&format!("can't make {op_code:?} with operand = {operand:#X}, operand does't fit into {OneByte:?}"));

                    Vec::from(operand.to_be_bytes())
                }

                TwoBytes => {
                    let operand = u16::try_from(*operand)
                        .expect(&format!("can't make {op_code:?} with operand = {operand:#X}, operand does't fit into {TwoBytes:?}"));

                    Vec::from(operand.to_be_bytes())
                }
            };

            instruction.extend_from_slice(&operand_be_bytes);
        }

        instruction
    }
}

#[cfg(test)]
mod op_code_tests {
    use super::OpCode;

    #[test]
    fn make() {
        let cases = vec![
            (
                (OpCode::Constant, vec![0xFFFE]),
                vec![OpCode::Constant as u8, 0xFF, 0xFE],
            ),
            (
                (
                    OpCode::Closure,
                    vec![(u16::MAX - 1) as isize, u8::MAX as isize],
                ),
                vec![OpCode::Closure as u8, 255, 254, 255],
            ),
        ];

        for case @ ((op_code, operands), exp_instruction) in &cases {
            let instruction = OpCode::make(op_code, operands);

            assert_eq!(&instruction, exp_instruction, "TEST ERROR for: {case:X?}");
        }
    }
}
