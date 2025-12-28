use std::{collections::HashMap, fmt::{self, write}};

use crate::asm::{parser::{AddAndKind, Imm9Kind, MemRelativeKind, Origin, StatementKind, parse}, types::{Address, Either, NBitInt}};
use crate::lc3_constants;


pub fn assemble(source: &str) -> Result<Vec<MachineCode>, ()> {
    let origins = parse(source).unwrap();
    let table = get_symbol_table(&origins).unwrap();
    let codes = assemble_origins(&origins, &table).unwrap();
    Ok(codes)
}

pub fn assemble_origins(origins: &[Origin], symbol_table: &SymbolTable) -> Result<Vec<MachineCode>, Vec<AssemblyError>> {
    let mut machine_codes = Vec::new();
    let mut errors = Vec::new();

    for origin in origins {
        match assemble_origin(origin, symbol_table) {
            Err(e) => errors.extend(e),
            Ok(machine_code) if errors.len() == 0 => machine_codes.push(machine_code),
            _ => {} // Do not write machine code if there has been an error
        }
    }
    Ok(machine_codes)
}

pub fn assemble_origin(origin: &Origin, symbol_table: &SymbolTable) -> Result<MachineCode, Vec<AssemblyError>> {
    let mut machine_code: Vec<u16> = Vec::new();
    let mut errors = Vec::new();

    let mut pc = origin.start_address.get_truncated_u16();
    for statement in &origin.statements {
        pc += get_statement_size(&statement.kind);

        match assemble_statement(&statement.kind, pc, symbol_table) {
            Err(e) => errors.push(e),
            Ok(assembled_statement) if errors.len() == 0 => machine_code.extend(assembled_statement),
            _ => {} // Stop writing machine code if there has been an error
        }
    }


    Ok(MachineCode {
        start_address: origin.start_address,
        code: machine_code,
    })
}

pub fn assemble_statement(statement_kind: &StatementKind, pc: u16, symbol_table: &SymbolTable) -> Result<Vec<u16>, AssemblyError> {
    let words = match statement_kind {
        StatementKind::AddAnd(kind, r0, r1, immediate_or_r2) => {
            let instruction = match kind {
                AddAndKind::Add => lc3_constants::ADD,
                AddAndKind::And => lc3_constants::AND
            };
            let termination = match immediate_or_r2 {
                Either::A(im) => 1 << 5 | im.get_truncated_u16(),
                Either::B(r2) => r2.get_truncated_u16()
            };
            vec![instruction | (r0.get_truncated_u16() << 9) | r1.get_truncated_u16() << 6 | termination]
        },
        StatementKind::Br(n, z, p, offset_or_symbol) => {
            let offset = symbol_table.get_or_give_offset(pc, offset_or_symbol)?;
            vec![lc3_constants::BR | (*n as u16) << 11 | (*z as u16) << 10 | (*p as u16) << 9 | offset]
        }
        StatementKind::Jmp(r0) => vec![lc3_constants::JMP | r0.get_truncated_u16() << 6],
        StatementKind::Jsr(offset) => {
            vec![lc3_constants::JSR | 1 << 11 | symbol_table.get_or_give_offset::<11>(pc, offset)?]
        },
        StatementKind::Jsrr(r0) => vec![lc3_constants::JSR | r0.get_truncated_u16() << 6],
        StatementKind::Imm9MemInstruction(kind, r0, offset) => {
            let instruction= match kind {
                Imm9Kind::Ld => lc3_constants::LD,
                Imm9Kind::Ldi => lc3_constants::LDI,
                Imm9Kind::Lea => lc3_constants::LEA,
                Imm9Kind::St => lc3_constants::ST,
                Imm9Kind::Sti => lc3_constants::STI,
            };

            vec![instruction | r0.get_truncated_u16() << 9 | symbol_table.get_or_give_offset::<9>(pc, offset)?]
        }
        StatementKind::MemRelative(kind, dr, base, offset) => {
            let instruction = match kind {
                MemRelativeKind::Load => lc3_constants::LDR,
                MemRelativeKind::Store => lc3_constants::STR
            };

            vec![instruction | dr.get_truncated_u16() << 9 | base.get_truncated_u16() << 6  | offset.get_truncated_u16()]
        }
        StatementKind::Not(r0,r1 ) => vec![lc3_constants::NOT | r0.get_truncated_u16() << 9 | r1.get_truncated_u16() << 6 | (1 << 6) - 1],
        StatementKind::Rti => vec![lc3_constants::RTI],
        StatementKind::Trap(trap_vec) => vec![lc3_constants::TRAP | trap_vec.get_truncated_u16()]
    };

    Ok(words)
}

fn get_statement_size(statement_kind: &StatementKind) -> u16 {
    match statement_kind {
        _ => 1
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MachineCode {
    pub start_address: Address,
    pub code: Vec<u16>,
}

impl MachineCode {
    pub fn new(start_address: Address) -> Self {
        Self {
            start_address,
            code: Vec::new()
        }
    }
}


fn get_symbol_table(origins: &[Origin]) -> Result<SymbolTable, (SymbolTable, Vec<AssemblyError>)> {
    let mut table = SymbolTable::new();
    let mut errors = Vec::new();
    for origin in origins {
        if let Some(label) = &origin.label {
            if let Err(ae) = table.add(&label, origin.start_address.get_truncated_u16()) {
                errors.push(ae);
            }
        }

        let mut pc = origin.start_address;
        let mut last_instuction_size = 0;
        for statement in &origin.statements {
            if let Err(ae) = pc.increment(last_instuction_size).map_err(|_| AssemblyError::LabelOutOfRange(pc.get() + last_instuction_size)) {
                errors.push(ae);
            }
            if let Some(label) = &statement.label {
                if let Err(ae) = table.add(label, pc.get_truncated_u16()) {
                    errors.push(ae);
                }
            }
            last_instuction_size = get_statement_size(&statement.kind) as i32
        }
    }

    if errors.len() == 0 {
        Ok(table)
    } else {
        Err((table, errors))
    }
}


#[derive(Debug)]
pub struct SymbolTable {
    lookup: HashMap<String, u16>
}

impl<'a> SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable { lookup: HashMap::new() }
    }
    pub fn add(&mut self, symbol: &str, address: u16) -> Result<(), AssemblyError> {
        if self.lookup.contains_key(symbol) {
            Err(AssemblyError::DoubleDefinedSymbol(symbol.to_string()))
        } else {
            self.lookup.insert(symbol.to_string(), address);
            Ok(())
        }
    }
    pub fn get(&self, symbol: &str) -> Result<u16, AssemblyError> {
        if let Some(address) = self.lookup.get(symbol) {
            Ok(*address)
        } else {
            Err(AssemblyError::UndefinedSymbol(symbol.to_string()))
        }
    }

    pub fn labels(&'a self) -> Vec<&'a str> {
        self.lookup.keys().map(|x| x.as_str()).collect()
    }

    pub fn get_offset<const BITS: u32>(&self, pc: u16, symbol: &str) -> Result<u16, AssemblyError> {
        let signed_offset = self.get(symbol)? as i32 - pc as i32;
        let n_bit_number = NBitInt::<BITS, true>::new(signed_offset).map_err(|e| AssemblyError::OffsetOutOfRange(symbol.to_string(), e.attempted_num, e.bits as u8))?;
        Ok(n_bit_number.get_truncated_u16())
    }

    pub fn get_or_give_offset<const BITS: u32>(&self, pc: u16, offset_or_symbol: &Either<NBitInt<BITS, true>, String>) -> Result<u16, AssemblyError> {
       let n_bit_offset = match offset_or_symbol {
            Either::A(offset) => *offset,
            Either::B(symbol) => {
                let signed_offset = self.get(symbol)? as i32 - pc as i32;
                NBitInt::<BITS, true>::new(signed_offset).map_err(|e| AssemblyError::OffsetOutOfRange(symbol.to_string(), e.attempted_num, e.bits as u8))?
            }
        };
        
        Ok(n_bit_offset.get_truncated_u16())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssemblyError {
    DoubleDefinedSymbol(String),
    UndefinedSymbol(String),
    LabelOutOfRange(i32),
    OffsetOutOfRange(String, i32, u8),
}

impl fmt::Display for AssemblyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DoubleDefinedSymbol(sym) => write!(f, "the label \"{}\" has been defined more than once", sym),
            Self::UndefinedSymbol(sym) => write!(f, "the label \"{}\" has no definition", sym),
            Self::LabelOutOfRange(address) => write!(f, "the label stands in for address \"{:x}\", which is out of range for the LC-3", address),
            Self::OffsetOutOfRange(label, offset, bits) => write!(f, "\"{label}\" stands for an address that is at an offset of {offset:x}, which is too high in magnitude for a {bits}-bit number.")
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::asm::{lexer::lex, parse_lexemes, types::Address};
    use super::*;

    #[test]
    fn get_empty_symbol_table() {
        let lexemes = lex(".orig #300 \n add r0 r1 r2 \n add r4 r3 r2 \n add r1 r3 r2 \n .end").unwrap();
        let origins = parse_lexemes(&lexemes).unwrap();
        let table = get_symbol_table(&origins).unwrap();

        assert_eq!(table.labels().len(), 0);
    }

    #[test]
    fn symbol_table_one_origin_and_all_statements_have_label() {
        let lexemes = lex("l1 .orig #300 \n l2 add r0 r1 r2 \n l3 add r4 r3 r2 \n l4 add r1 r3 r2 \n .end").unwrap();
        let origins = parse_lexemes(&lexemes).unwrap();
        let table = get_symbol_table(&origins).unwrap();
        let mut labels_and_addresses: Vec<_> = table.labels().iter().map(|&l| (l, table.get(l).unwrap())).collect();
        labels_and_addresses.sort_by(|a, b| a.0.cmp(b.0));
        assert_eq!(
            labels_and_addresses,
            vec![
                ("l1", 300),
                ("l2", 300),
                ("l3", 301),
                ("l4", 302),
                ]
        );
    }

    #[test]
    fn assembles_add_and_and() {
        assert_eq!(
            assemble(".orig #12288 \n add r0 r1 r2 \n and r3 r4 #0\n.end").unwrap(),
            vec![
                MachineCode {
                    start_address: Address::new(12288).unwrap(),
                    code: vec![
                        0x1042, 0x5720
                    ]
                }
            ]
        )
    }

    #[test]
    fn assembles_two_origins() {
        assert_eq!(
            assemble(".orig x3000 \n add r0 r1 r2 \n and r3 r4 #0\n.end\n.orig x3002 \n add r0 r1 r2 \n and r3 r4 #8\n.end").unwrap(),
            vec![
                MachineCode {
                    start_address: Address::new(0x3000).unwrap(),
                    code: vec![
                        0x1042, 0x5720
                    ]
                },
                MachineCode {
                    start_address: Address::new(0x3002).unwrap(),
                    code: vec![
                        0x1042, 0x5728
                    ]
                }
            ]
        )
    }

    #[test]
    fn assembles_immediate_offsets() {
        assert_eq!(
            assemble("
            .orig x3000
            jsr xFF
            ld r2 x01
            ldi r3 x02
            lea r4 x03
            st r5 x04
            sti r5 x05
            .end
            ").unwrap(),
            vec![MachineCode {
                start_address: Address::new(0x3000).unwrap(),
                code: vec![
                    0x48FF, // jsr
                    0x2401, // ld
                    0xA602, // ldi
                    0xE803, // lea
                    0x3A04, // sti
                    0xBA05, // sti
                ]
            }]
        )
    }

    #[test]
    fn assembles_all_branch_instruction_possibilities() {
        assert_eq!(
            assemble("
            .orig x3000
            br #-1
            brn #-1
            brz #-1
            brnz #-1
            brp #-1
            brnp #-1
            brzp #-1
            brnzp #-1
            .end").unwrap(),
            vec![
                MachineCode {
                    start_address: Address::new(0x3000).unwrap(),
                    code: vec![
                        0x0FFF,
                        0x09FF,
                        0x05FF,
                        0x0DFF,
                        0x03FF,
                        0x0BFF,
                        0x07FF,
                        0x0FFF,
                    ]
                }
            ]
        )
    }

    #[test]
    fn assembles_all_instructions() {
        assert_eq!(
            assemble("
            .orig x3000
            add r0 r1 r2
            add r3 r4 #0
            and r1 r2 r3
            label and r1 r2 #15
            brnp label
            brz x87
            jmp r6
            jsr label
            jsrr r5
            ld r2 label
            ldi r3 label
            ldr r1 r2 x8
            lea r4 label
            not r1 r2
            ret
            rti
            st r5 label
            sti r5 label
            str r7 r0 #-32
            trap x18
            .end").unwrap(),
            vec![
                MachineCode {
                    start_address: Address::new(0x3000).unwrap(),
                    code: vec![
                        0x1042, // add
                        0x1720, // add
                        0x5283, // and
                        0x52AF, // and
                        0x0BFE, // brnp
                        0x0487, // brz
                        0xC180, // jmp
                        0x4FFB, // jsr
                        0x4140, // jsrr
                        0x25F9, // ld
                        0xA7F8, // ldi
                        0x6288, // ldr
                        0xE9F6, // lea
                        0x92BF, // not
                        0xC1C0, // ret
                        0x8000, // rti
                        0x3BF2, // st
                        0xBBF1, // sti
                        0x7E20, // str
                        0xF018, // trap
                    ]
                }
            ]
        )
    }
}

