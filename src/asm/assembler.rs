use std::{collections::HashMap, fmt::{self, write}};

use crate::asm::{parser::{Imm9Kind, Origin, StatementKind, parse}, types::{Address, NBitInt}};
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

    let mut pc = origin.start_address.get_u16();
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
        StatementKind::Add(r0,r1 ,r2 ) => vec![lc3_constants::ADD | (r0.get_u16() << 9) | r1.get_u16() << 6 | r2.get_u16()],
        StatementKind::AddI(r0,r1 ,im ) => vec![lc3_constants::ADD | (r0.get_u16() << 9) | r1.get_u16() << 6 | 1 << 5 | im.get_u16()],
        StatementKind::And(r0,r1 ,r2 ) => vec![lc3_constants::AND | (r0.get_u16() << 9) | r1.get_u16() << 6 | r2.get_u16()],
        StatementKind::AndI(r0,r1 ,im ) => vec![lc3_constants::AND | (r0.get_u16() << 9) | r1.get_u16() << 6 | 1 << 5 | im.get_u16()],
        StatementKind::Jmp(r0) => vec![lc3_constants::JMP | r0.get_u16() << 6],
        StatementKind::Jsrr(r0) => vec![lc3_constants::JSR | r0.get_u16() << 6],
        StatementKind::Imm9MemInstruction(kind, r0, label) => {
            let instruction= match kind {
                Imm9Kind::Ld => lc3_constants::LD,
            };
            let signed_offset = symbol_table.get(label)? as i32 - pc as i32;
            let _ = NBitInt::<9, true>::new(signed_offset).map_err(|e| AssemblyError::OffsetOutOfRange(label.clone(), signed_offset, 9))?;
            vec![instruction | r0.get_u16() << 9 | signed_offset as u16 & 0x1FF]
        }
        StatementKind::Not(r0,r1 ) => vec![lc3_constants::NOT | r0.get_u16() << 9 | r1.get_u16() << 6 | (1 << 6) - 1],
        StatementKind::Rti => vec![lc3_constants::RTI],
        StatementKind::Trap(trap_vec) => vec![lc3_constants::TRAP | trap_vec.get_u16()]
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
            if let Err(ae) = table.add(&label, origin.start_address.get_u16()) {
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
                if let Err(ae) = table.add(label, pc.get_u16()) {
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
    fn assembles_all_instructions() {
        assert_eq!(
            assemble("
            .orig x3000
            add r0 r1 r2
            add r3 r4 #0
            and r1 r2 r3
            and r1 r2 #15
            jmp r6
            jsrr r5
            ld r2 label
            not r1 r2
            ret
            rti
            label trap x18
            .end").unwrap(),
            vec![
                MachineCode {
                    start_address: Address::new(0x3000).unwrap(),
                    code: vec![
                        0x1042, // add
                        0x1720, // add
                        0x5283, // and
                        0x52AF, // and
                        0xC180, // jmp
                        0x4140, // jsrr
                        0x2403, // ld
                        0x92BF, // not
                        0xC1C0, // ret
                        0x8000, // rti
                        0xF018, // trap
                    ]
                }
            ]
        )
    }
}

