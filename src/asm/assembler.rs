use std::{collections::HashMap, fmt};

use crate::asm::{parser::{Origin, StatementKind}, types::Address};
use crate::lc3_constants;



fn assemble(origins: &[Origin], _: &SymbolTable) -> Result<Vec<u16>, Vec<AssemblyError>> {
    let mut machine_code = Vec::new();
    // let mut errors = Vec::new();
    for origin in origins {
        let mut pc = origin.address;

        for statement in &origin.statements {
            if let Err(_) = pc.increment(get_statement_size(&statement.kind) as i32) {
                todo!();
            };
            let words = match statement.kind {
                StatementKind::Add(r0,r1 ,r2 ) => vec![lc3_constants::ADD | (r0.get_u16() << 9) | r1.get_u16() << 6 | r2.get_u16()],
                StatementKind::AddI(r0,r1 ,im ) => vec![lc3_constants::ADD | (r0.get_u16() << 9) | r1.get_u16() << 6 | 1 << 5 | im.get_u16()],
                StatementKind::And(r0,r1 ,r2 ) => vec![lc3_constants::AND | (r0.get_u16() << 9) | r1.get_u16() << 6 | r2.get_u16()],
                StatementKind::AndI(r0,r1 ,im ) => vec![lc3_constants::AND | (r0.get_u16() << 9) | r1.get_u16() << 6 | 1 << 5 | im.get_u16()],
            };

            machine_code.extend(words);
            
        }
    }

    Ok(machine_code)
}

fn assemple_statement(statement_kind: &StatementKind, mut pc: Address) -> Result<Vec<u16>, AssemblyError> {
    if let Err(_) = pc.increment(get_statement_size(statement_kind) as i32) {
        todo!()
    };
    let words = match statement_kind {
        StatementKind::Add(r0,r1 ,r2 ) => vec![lc3_constants::ADD | (r0.get_u16() << 9) | r1.get_u16() << 6 | r2.get_u16()],
        StatementKind::AddI(r0,r1 ,im ) => vec![lc3_constants::ADD | (r0.get_u16() << 9) | r1.get_u16() << 6 | 1 << 5 | im.get_u16()],
        StatementKind::And(r0,r1 ,r2 ) => vec![lc3_constants::AND | (r0.get_u16() << 9) | r1.get_u16() << 6 | r2.get_u16()],
        StatementKind::AndI(r0,r1 ,im ) => vec![lc3_constants::AND | (r0.get_u16() << 9) | r1.get_u16() << 6 | 1 << 5 | im.get_u16()],
    };

    Ok(words)
}

#[derive(Debug)]
pub struct MachineCode {
    pub start_address: Address,
    pub machine_code: Vec<u16>,
}

impl MachineCode {
    
}


fn get_symbol_table(origins: &[Origin]) -> Result<SymbolTable, (SymbolTable, Vec<AssemblyError>)> {
    let mut table = SymbolTable::new();
    let mut errors = Vec::new();
    for origin in origins {
        if let Some(label) = origin.label {
            if let Err(ae) = table.add(label, origin.address) {
                errors.push(ae);
            }
        }

        let mut pc = origin.address;
        let mut last_instuction_size = 0;
        for statement in &origin.statements {
            if let Err(ae) = pc.increment(last_instuction_size).map_err(|e| AssemblyError::LabelOutOfRange(pc.get() + last_instuction_size)) {
                errors.push(ae);
            }
            if let Some(label) = statement.label {
                if let Err(ae) = table.add(label, pc) {
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

fn get_statement_size(statement_kind: &StatementKind) -> u16 {
    match statement_kind {
        _ => 1
    }
}

#[derive(Debug)]
pub struct SymbolTable {
    lookup: HashMap<Vec<u8>, Address>
}

impl<'a> SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable { lookup: HashMap::new() }
    }
    pub fn add(&mut self, symbol: &[u8], address: Address) -> Result<(), AssemblyError> {
        if self.lookup.contains_key(symbol) {
            Err(AssemblyError::DoubleDefinedSymbol(symbol.to_vec()))
        } else {
            self.lookup.insert(symbol.to_vec(), address);
            Ok(())
        }
    }
    pub fn get(&self, symbol: &[u8]) -> Result<Address, AssemblyError> {
        if let Some(address) = self.lookup.get(symbol) {
            Ok(*address)
        } else {
            Err(AssemblyError::UndefinedSymbol(symbol.to_vec()))
        }
    }

    pub fn labels(&'a self) -> Vec<&'a [u8]> {
        self.lookup.keys().map(|x| x.as_slice()).collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssemblyError {
    DoubleDefinedSymbol(Vec<u8>),
    UndefinedSymbol(Vec<u8>),
    LabelOutOfRange(i32),
}

impl fmt::Display for AssemblyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DoubleDefinedSymbol(sym) => write!(f, "the label \"{}\" has been defined more than once", unsafe { String::from_utf8_unchecked(sym.clone()) }),
            Self::UndefinedSymbol(sym) => write!(f, "the label \"{}\" has no definition", unsafe { String::from_utf8_unchecked(sym.clone())}),
            Self::LabelOutOfRange(address) => write!(f, "the label stands in for address \"{:x}\", which is out of range for the LC-3", address)
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::asm::{lexer::lex, parse, types::Address};
    use super::*;

    #[test]
    fn get_empty_symbol_table() {
        let lexemes = lex(b".orig #300 \n add r0 r1 r2 \n add r4 r3 r2 \n add r1 r3 r2 \n .end").unwrap();
        let origins = parse(&lexemes).unwrap();
        let table = get_symbol_table(&origins).unwrap();

        assert_eq!(table.labels().len(), 0);
    }

    #[test]
    fn symbol_table_one_origin_and_all_statements_have_label() {
        let lexemes = lex(b"l1 .orig #300 \n l2 add r0 r1 r2 \n l3 add r4 r3 r2 \n l4 add r1 r3 r2 \n .end").unwrap();
        let origins = parse(&lexemes).unwrap();
        let table = get_symbol_table(&origins).unwrap();
        let mut labels_and_addresses: Vec<_> = table.labels().iter().map(|&l| (l, table.get(l).unwrap())).collect();
        labels_and_addresses.sort_by(|a, b| a.0.cmp(b.0));
        assert_eq!(
            labels_and_addresses,
            vec![
                (&b"l1"[..], Address::new(300).unwrap()),
                (&b"l2"[..], Address::new(300).unwrap()),
                (&b"l3"[..], Address::new(301).unwrap()),
                (&b"l4"[..], Address::new(302).unwrap()),
                ]
        );
    }
}
