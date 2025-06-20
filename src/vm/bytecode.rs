use crate::vm::op_code::meta::OperandWidth;
use crate::vm::op_code::op_code::OpCode;
use std::ops::Deref;
use std::ops::DerefMut;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Bytecode(pub Vec<u8>);

impl From<Vec<(OpCode, Vec<isize>)>> for Bytecode {
    fn from(value: Vec<(OpCode, Vec<isize>)>) -> Self {
        Bytecode(
            value
                .into_iter()
                .map(|(op_code, operands)| OpCode::make(&op_code, &operands))
                .flatten()
                .collect(),
        )
    }
}

impl Deref for Bytecode {
    type Target = Vec<u8>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Bytecode {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl std::fmt::Display for Bytecode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut rest_instr = self.as_slice();
        let mut i = 0;

        loop {
            let op_code = match rest_instr {
                [] => break,

                [op_code_byte, rest @ ..] => {
                    rest_instr = rest;

                    OpCode::try_from(op_code_byte).expect(&format!(
                        "no candidate for OpCode exists for byte={op_code_byte} at position {i} in {:?}", self.deref()
                    ))
                }
            };

            let meta = op_code.meta();

            let mut operands = Vec::with_capacity(meta.operand_widths.len());

            for width in &op_code.meta().operand_widths {
                let width = *width;

                let operand_bytes = match rest_instr.split_at_checked(width as usize) {
                    Some((operand_slice, rest)) => {
                        rest_instr = rest;

                        operand_slice
                    }

                    _ => panic!(
                        "Not enough instruction bytes to construct operand, rest_instr = {rest_instr:?}"
                    ),
                };

                assert_eq!(width as usize, operand_bytes.len());

                let operand = match width {
                    OperandWidth::OneByte => {
                        u8::from_be_bytes(operand_bytes.try_into().expect("can't convert into arr"))
                            as i64
                    }

                    OperandWidth::TwoBytes => u16::from_be_bytes(
                        operand_bytes.try_into().expect("can't convert into arr"),
                    ) as i64,
                };

                operands.push(operand);
            }

            let operands_string = operands
                .into_iter()
                .map(|operand| operand.to_string())
                .collect::<Vec<_>>()
                .join(", ");

            writeln!(f, "{i:04} {} {}", meta.name, operands_string)?;

            i = self.len() - rest_instr.len();
        }

        Ok(())
    }
}

#[cfg(test)]
mod instruction_tests {
    use super::*;

    #[test]
    fn instructions_display() {
        let bytecode = Bytecode(
            vec![
                OpCode::make(&OpCode::Constant, &vec![3]),
                OpCode::make(&OpCode::Constant, &vec![65534]),
                OpCode::make(&OpCode::Constant, &vec![309]),
                OpCode::make(&OpCode::Constant, &vec![65]),
                OpCode::make(
                    &OpCode::Closure,
                    &vec![(u16::MAX - 1) as isize, u8::MAX as isize],
                ),
            ]
            .into_iter()
            .flatten()
            .collect(),
        );

        let exp_output = "\
0000 Constant 3
0003 Constant 65534
0006 Constant 309
0009 Constant 65
0012 Closure 65534, 255
";

        assert_eq!(bytecode.to_string(), exp_output);
    }
}
