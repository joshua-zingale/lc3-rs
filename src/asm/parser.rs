use std::vec;

use crate::asm::{
    lexer::{DirectiveSymbol, InstructionSymbol, Lexeme, LexemeKind, lex},
    types::{
        Address, Either, Imm5, Imm6, Imm9, Imm11, Location, NBitInt, ParsingError,
        ParsingErrorKind, RegisterNum, TrapVec,
    },
};

pub fn parse(source: &str) -> Result<Vec<Origin>, Vec<ParsingError>> {
    let lexemes = lex(source);
    match lexemes {
        Err(mixed) => {
            let mut errors = Vec::new();
            for e in mixed {
                if let Err(pe) = e {
                    errors.push(pe)
                }
            }
            Err(errors)
        }
        Ok(lexemes) => parse_lexemes(&lexemes),
    }
}

pub fn parse_lexemes(lexemes: &[Lexeme]) -> Result<Vec<Origin>, Vec<ParsingError>> {
    let mut errors = Vec::new();
    let mut parser = Parser { pos: 0, lexemes };

    let mut origins = Vec::new();
    parser.skip(LexemeKind::LineBreak);
    while parser.pos < lexemes.len() {
        match parser.parse_origin() {
            Ok(origin) => {
                origins.push(origin);
                parser.skip(LexemeKind::LineBreak);
            }
            Err(errors_in_origin) => {
                errors.extend(errors_in_origin);
            }
        }
    }

    if errors.len() > 0 {
        Err(errors)
    } else {
        Ok(origins)
    }
}

struct Parser<'a> {
    pos: usize,
    lexemes: &'a [Lexeme],
}

impl<'a> Parser<'a> {
    fn parse_origin(&mut self) -> Result<Origin, Vec<ParsingError>> {
        let maybe_label = self.try_consume_label().map(|t| t.1);
        self.skip(LexemeKind::LineBreak);

        let orig_lexeme = self
            .consume(LexemeKind::Directive(DirectiveSymbol::Orig))
            .map_err(|e| vec![e])?;
        let (immediate_lexeme, address) =
            self.consume_immediate::<16, false>().map_err(|e| vec![e])?;

        let mut errors = Vec::new();

        if let Err(e) = self.consume(LexemeKind::LineBreak) {
            errors.push(e);
        }

        let mut statements = vec![];

        while let Some(lex) = self.curr_lexeme()
            && lex.kind != LexemeKind::Directive(DirectiveSymbol::End)
        {
            match self.consume_statement() {
                Ok(statement) => statements.push(statement),
                Err(e) => {
                    while let Some(lexeme) = self.curr_lexeme()
                        && lexeme.kind != LexemeKind::LineBreak
                    {
                        let _ = self.advance();
                    }
                    errors.push(e)
                }
            }
            if let Err(e) = self.consume(LexemeKind::LineBreak) {
                errors.push(e);
            }
        }

        let end_lexeme = self
            .consume(LexemeKind::Directive(DirectiveSymbol::End))
            .map_err(|e| vec![e])?;

        if errors.len() > 0 {
            Err(errors)
        } else {
            Ok(Origin {
                start_address: address,
                statements,
                orig_lexeme: orig_lexeme.clone(),
                immediate_lexeme: immediate_lexeme.clone(),
                end_lexeme: end_lexeme.clone(),
                label: maybe_label.map(String::from),
            })
        }
    }

    fn consume_statement(&mut self) -> Result<Statement, ParsingError> {
        let maybe_label = self.try_consume_label().map(|t| t.1).map(String::from);
        self.skip(LexemeKind::LineBreak);
        let instruction_lexeme = self.consume_any("instruction")?;
        match &instruction_lexeme.kind {
            LexemeKind::Directive(symbol) => match symbol {
                DirectiveSymbol::Orig => Err(self.make_error(ParsingErrorKind::ExpectedButFound(
                    "instruction".to_string(),
                    "ORIG directive".to_string(),
                ))),
                DirectiveSymbol::End => Err(self.make_error(ParsingErrorKind::ExpectedButFound(
                    "instruction".to_string(),
                    "END directive".to_string(),
                ))),
                DirectiveSymbol::Fill => {
                    let value = match &self.curr_lexeme_or_error("immediate or label")?.kind {
                        LexemeKind::Immediate(value) => {
                            if *value > u16::MAX.into() {
                                Err(self.make_error(ParsingErrorKind::ImmediateOutOfRange(
                                    16, *value, false,
                                )))?
                            } else if *value < i16::MIN.into() {
                                Err(self.make_error(ParsingErrorKind::ImmediateOutOfRange(
                                    16, *value, true,
                                )))?
                            }
                            Either::A(*value as u16)
                        }
                        LexemeKind::Label(label) => Either::B(label.to_owned()),
                        other => Err(self.make_error(ParsingErrorKind::ExpectedButFound(
                            "immediate or label".to_string(),
                            other.string_name(),
                        )))?,
                    };
                    self.advance();
                    Ok(Statement {
                        kind: StatementKind::Fill(value),
                        lexemes: self.lexemes[self.pos - 2..self.pos].to_vec(),
                        label: maybe_label,
                    })
                }
                DirectiveSymbol::Blkw => {
                    let (_, size) = self.consume_immediate::<16, false>()?;
                    Ok(Statement {
                        kind: StatementKind::Blkw(size.get_truncated_u16()),
                        lexemes: self.lexemes[self.pos - 2..self.pos].to_vec(),
                        label: maybe_label,
                    })
                }
                DirectiveSymbol::Stringz => {
                    let s = self.consume_string_literal()?;
                    Ok(Statement {
                        kind: StatementKind::Stringz(s),
                        lexemes: self.lexemes[self.pos - 2..self.pos].to_vec(),
                        label: maybe_label,
                    })
                }
            },
            LexemeKind::Instruction(symbol) => match symbol {
                s @ (InstructionSymbol::Add | InstructionSymbol::And) => {
                    let r1 = self.consume_register()?;
                    let r2 = self.consume_register()?;
                    let r3_or_immediate = self.consume_immediate_or_register()?;

                    let kind = match s {
                        InstructionSymbol::Add => AddAndKind::Add,
                        InstructionSymbol::And => AddAndKind::And,
                        _ => unreachable!(),
                    };
                    Ok(Statement {
                        kind: StatementKind::AddAnd(kind, r1, r2, r3_or_immediate),
                        lexemes: self.lexemes[self.pos - 4..self.pos].to_vec(),
                        label: maybe_label,
                    })
                }
                InstructionSymbol::Br(n, z, p) => {
                    let (n2, z2, p2) = if *n || *z || *p {
                        (*n, *z, *p)
                    } else {
                        (true, true, true)
                    };
                    let offset = self.consume_immediate_or_label()?;
                    Ok(Statement {
                        kind: StatementKind::Br(n2, z2, p2, offset),
                        lexemes: self.lexemes[self.pos - 2..self.pos].to_vec(),
                        label: maybe_label,
                    })
                }
                InstructionSymbol::Jmp => {
                    let r1 = self.consume_register()?;
                    Ok(Statement {
                        kind: StatementKind::Jmp(r1),
                        lexemes: self.lexemes[self.pos - 2..self.pos].to_vec(),
                        label: maybe_label,
                    })
                }
                InstructionSymbol::Jsr => {
                    let offset = self.consume_immediate_or_label::<11, true>()?;
                    Ok(Statement {
                        kind: StatementKind::Jsr(offset),
                        lexemes: self.lexemes[self.pos - 2..self.pos].to_vec(),
                        label: maybe_label,
                    })
                }
                InstructionSymbol::Jsrr => {
                    let r1 = self.consume_register()?;
                    Ok(Statement {
                        kind: StatementKind::Jsrr(r1),
                        lexemes: self.lexemes[self.pos - 2..self.pos].to_vec(),
                        label: maybe_label,
                    })
                }
                symbol @ (InstructionSymbol::Ld
                | InstructionSymbol::Ldi
                | InstructionSymbol::Lea
                | InstructionSymbol::St
                | InstructionSymbol::Sti) => {
                    let r0 = self.consume_register()?;
                    let offset = self.consume_immediate_or_label()?;
                    let imm9_kind = match symbol {
                        InstructionSymbol::Ld => Imm9Kind::Ld,
                        InstructionSymbol::Ldi => Imm9Kind::Ldi,
                        InstructionSymbol::Lea => Imm9Kind::Lea,
                        InstructionSymbol::St => Imm9Kind::St,
                        InstructionSymbol::Sti => Imm9Kind::Sti,
                        _ => unreachable!(),
                    };

                    Ok(Statement {
                        kind: StatementKind::Imm9MemInstruction(imm9_kind, r0, offset),
                        lexemes: self.lexemes[self.pos - 3..self.pos].to_vec(),
                        label: maybe_label,
                    })
                }
                symbol @ (InstructionSymbol::Ldr | InstructionSymbol::Str) => {
                    let kind = match symbol {
                        InstructionSymbol::Ldr => MemRelativeKind::Load,
                        InstructionSymbol::Str => MemRelativeKind::Store,
                        _ => unreachable!(),
                    };
                    let dr = self.consume_register()?;
                    let base = self.consume_register()?;
                    let (_, offset) = self.consume_immediate()?;
                    Ok(Statement {
                        kind: StatementKind::MemRelative(kind, dr, base, offset),
                        lexemes: self.lexemes[self.pos - 4..self.pos].to_vec(),
                        label: maybe_label,
                    })
                }
                InstructionSymbol::Not => {
                    let r1 = self.consume_register()?;
                    let r2 = self.consume_register()?;
                    Ok(Statement {
                        kind: StatementKind::Not(r1, r2),
                        lexemes: self.lexemes[self.pos - 3..self.pos].to_vec(),
                        label: maybe_label,
                    })
                }
                InstructionSymbol::Ret => Ok(Statement {
                    kind: StatementKind::Jmp(NBitInt::new(7).unwrap()),
                    lexemes: self.lexemes[self.pos - 1..self.pos].to_vec(),
                    label: maybe_label,
                }),
                InstructionSymbol::Rti => Ok(Statement {
                    kind: StatementKind::Rti,
                    lexemes: self.lexemes[self.pos - 1..self.pos].to_vec(),
                    label: maybe_label,
                }),
                InstructionSymbol::Trap => {
                    let (_, trap_vec) = self.consume_immediate()?;
                    Ok(Statement {
                        kind: StatementKind::Trap(trap_vec),
                        lexemes: self.lexemes[self.pos - 2..self.pos].to_vec(),
                        label: maybe_label,
                    })
                }
                s @ (InstructionSymbol::Getc
                | InstructionSymbol::Out
                | InstructionSymbol::Puts
                | InstructionSymbol::In
                | InstructionSymbol::Putsp
                | InstructionSymbol::Halt) => {
                    let trap_vec = TrapVec::new(match s {
                        InstructionSymbol::Getc => 0x20,
                        InstructionSymbol::Out => 0x21,
                        InstructionSymbol::Puts => 0x22,
                        InstructionSymbol::In => 0x23,
                        InstructionSymbol::Putsp => 0x24,
                        InstructionSymbol::Halt => 0x25,
                        _ => unreachable!(),
                    })
                    .expect("all TRAP aliases map to valid trap vectors");

                    Ok(Statement {
                        kind: StatementKind::Trap(trap_vec),
                        lexemes: self.lexemes[self.pos - 2..self.pos].to_vec(),
                        label: maybe_label,
                    })
                }
            },
            a => todo!("{:?}", a),
        }
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn consume_immediate<const BITS: u32, const SIGNED: bool>(
        &mut self,
    ) -> Result<(&'a Lexeme, NBitInt<BITS, SIGNED>), ParsingError> {
        let immediate_lexeme = self.curr_lexeme_or_error("immediate value")?;
        if let LexemeKind::Immediate(value) = immediate_lexeme.kind {
            self.advance();
            let n_bit_int = NBitInt::<BITS, SIGNED>::new(value).map_err(|noore| {
                self.make_error(ParsingErrorKind::ImmediateOutOfRange(
                    noore.bits,
                    noore.attempted_num,
                    noore.signed,
                ))
            })?;
            Ok((immediate_lexeme, n_bit_int))
        } else {
            Err(self.make_error(ParsingErrorKind::ExpectedButFound(
                "immediate value".to_string(),
                immediate_lexeme.kind.string_name(),
            )))
        }
    }

    fn consume_any_immediate(&mut self) -> Result<(&'a Lexeme, i32), ParsingError> {
        let immediate_lexeme = self.curr_lexeme_or_error("immediate value")?;
        if let LexemeKind::Immediate(value) = immediate_lexeme.kind {
            self.advance();
            Ok((immediate_lexeme, value))
        } else {
            Err(self.make_error(ParsingErrorKind::ExpectedButFound(
                "immediate value".to_string(),
                immediate_lexeme.kind.string_name(),
            )))
        }
    }

    fn consume_register(&mut self) -> Result<RegisterNum, ParsingError> {
        let register_lexeme = self.curr_lexeme_or_error("register")?;
        if let LexemeKind::Register(value) = register_lexeme.kind {
            self.advance();
            Ok(value)
        } else {
            Err(self.make_error(ParsingErrorKind::ExpectedButFound(
                "immediate value".to_string(),
                register_lexeme.kind.string_name(),
            )))
        }
    }

    fn consume_label(&mut self) -> Result<String, ParsingError> {
        let register_lexeme = self.curr_lexeme_or_error("label")?;
        if let LexemeKind::Label(label) = &register_lexeme.kind {
            self.advance();
            Ok(label.clone())
        } else {
            Err(self.make_error(ParsingErrorKind::ExpectedButFound(
                "label".to_string(),
                register_lexeme.kind.string_name(),
            )))
        }
    }

    fn consume_string_literal(&mut self) -> Result<String, ParsingError> {
        let lexeme = self.curr_lexeme_or_error("string literal")?;
        if let LexemeKind::String(s) = &lexeme.kind {
            self.advance();
            Ok(s.clone())
        } else {
            Err(self.make_error(ParsingErrorKind::ExpectedButFound(
                "string literal".to_string(),
                lexeme.kind.string_name(),
            )))
        }
    }

    fn consume_immediate_or_register<const BITS: u32, const SIGNED: bool>(
        &mut self,
    ) -> Result<Either<NBitInt<BITS, SIGNED>, RegisterNum>, ParsingError> {
        let lexeme = self.curr_lexeme_or_error("immediate value or register")?;
        if let LexemeKind::Immediate(value) = lexeme.kind {
            self.advance();
            let n_bit_int = NBitInt::<BITS, SIGNED>::new(value).map_err(|noore| {
                self.make_error(ParsingErrorKind::ImmediateOutOfRange(
                    noore.bits,
                    noore.attempted_num,
                    noore.signed,
                ))
            })?;
            Ok(Either::A(n_bit_int))
        } else if let LexemeKind::Register(value) = lexeme.kind {
            self.advance();
            Ok(Either::B(value))
        } else {
            Err(self.make_error(ParsingErrorKind::ExpectedButFound(
                "immediate value or register".to_string(),
                lexeme.kind.string_name(),
            )))
        }
    }

    fn consume_immediate_or_label<const BITS: u32, const SIGNED: bool>(
        &mut self,
    ) -> Result<Either<NBitInt<BITS, SIGNED>, String>, ParsingError> {
        let lexeme = self.curr_lexeme_or_error("immediate value or label")?;
        if let LexemeKind::Immediate(value) = lexeme.kind {
            self.advance();
            let n_bit_int = NBitInt::<BITS, SIGNED>::new(value).map_err(|noore| {
                self.make_error(ParsingErrorKind::ImmediateOutOfRange(
                    noore.bits,
                    noore.attempted_num,
                    noore.signed,
                ))
            })?;
            Ok(Either::A(n_bit_int))
        } else if let LexemeKind::Label(value) = &lexeme.kind {
            self.advance();
            Ok(Either::B(value.clone()))
        } else {
            Err(self.make_error(ParsingErrorKind::ExpectedButFound(
                "immediate value or label".to_string(),
                lexeme.kind.string_name(),
            )))
        }
    }

    fn make_error(&self, kind: ParsingErrorKind) -> ParsingError {
        let (start, end) = self.curr_lexeme_location();
        ParsingError { kind, start, end }
    }

    fn curr_lexeme(&self) -> Option<&'a Lexeme> {
        self.lexemes.get(self.pos)
    }

    fn curr_lexeme_or_error(&self, name: &str) -> Result<&'a Lexeme, ParsingError> {
        let res = self.curr_lexeme().ok_or_else(|| {
            self.make_error(ParsingErrorKind::ExpectedButFound(
                name.to_string(),
                "end of file".to_string(),
            ))
        });

        res
    }

    fn consume_any(&mut self, name: &str) -> Result<&'a Lexeme, ParsingError> {
        let res = self.curr_lexeme().ok_or_else(|| {
            self.make_error(ParsingErrorKind::ExpectedButFound(
                name.to_string(),
                "end of file".to_string(),
            ))
        });

        if res.is_ok() {
            self.pos += 1;
        }

        res
    }

    fn try_consume_label(&mut self) -> Option<(&'a Lexeme, &'a str)> {
        if let Some(lexeme) = self.curr_lexeme()
            && let LexemeKind::Label(label) = &lexeme.kind
        {
            let _ = self.consume_any("label");
            Some((lexeme, label))
        } else {
            None
        }
    }

    fn consume(&mut self, lexeme_kind: LexemeKind) -> Result<&'a Lexeme, ParsingError> {
        match self.lexemes.get(self.pos) {
            None => Err(ParsingError {
                kind: ParsingErrorKind::ExpectedButFound(
                    lexeme_kind.string_name(),
                    "end of file".to_string(),
                ),
                start: self.curr_lexeme_location().0,
                end: self.curr_lexeme_location().1,
            }),
            Some(lexeme) if lexeme.kind == lexeme_kind => {
                self.pos += 1;
                Ok(lexeme)
            }
            Some(lexeme) => Err(ParsingError {
                kind: ParsingErrorKind::ExpectedButFound(
                    lexeme_kind.string_name(),
                    lexeme.kind.string_name(),
                ),
                start: self.curr_lexeme_location().0,
                end: self.curr_lexeme_location().1,
            }),
        }
    }

    fn skip(&mut self, lexeme_kind: LexemeKind) {
        if self.pos < self.lexemes.len() && self.lexemes[self.pos].kind == lexeme_kind {
            self.pos += 1;
        }
    }

    fn curr_lexeme_location(&self) -> (Location, Location) {
        match self.lexemes.get(self.pos) {
            None if self.pos == 0 => (Location::default(), Location::default()),
            None => (
                self.lexemes.last().unwrap().end,
                self.lexemes.last().unwrap().end,
            ),
            Some(lexeme) => (lexeme.start, lexeme.end),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Origin {
    pub start_address: Address,
    pub statements: Vec<Statement>,
    pub orig_lexeme: Lexeme,
    pub immediate_lexeme: Lexeme,
    pub end_lexeme: Lexeme,
    pub label: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Statement {
    pub kind: StatementKind,
    pub lexemes: Vec<Lexeme>,
    pub label: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StatementKind {
    AddAnd(
        AddAndKind,
        RegisterNum,
        RegisterNum,
        Either<Imm5, RegisterNum>,
    ),
    Br(bool, bool, bool, Either<Imm9, String>),
    MemRelative(MemRelativeKind, RegisterNum, RegisterNum, Imm6),
    Jmp(RegisterNum),
    Jsr(Either<Imm11, String>),
    Jsrr(RegisterNum),
    Imm9MemInstruction(Imm9Kind, RegisterNum, Either<Imm9, String>),
    Not(RegisterNum, RegisterNum),
    Rti,
    Trap(TrapVec),
    Fill(Either<u16, String>),
    Blkw(u16),
    Stringz(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MemRelativeKind {
    Load,
    Store,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AddAndKind {
    Add,
    And,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Imm9Kind {
    Ld,
    Ldi,
    Lea,
    St,
    Sti,
}

trait StatementArgument {
    fn string_name(&self) -> String;
}

#[cfg(test)]
mod tests {
    use super::super::lexer::lex;
    use super::super::types::RegisterNum;
    use super::*;

    #[test]
    fn empty_origin() {
        let lexemes = lex(".orig #100\n.end").unwrap();
        assert_eq!(
            *parse_lexemes(&lexemes).unwrap().first().unwrap(),
            Origin {
                start_address: Address::new(100).unwrap(),
                statements: vec![],
                orig_lexeme: lexemes[0].clone(),
                immediate_lexeme: lexemes[1].clone(),
                end_lexeme: lexemes[3].clone(),
                label: None,
            },
        )
    }

    #[test]
    fn origin_with_one_statement() {
        let lexemes = lex(" .orig #3000\nadd r0 r1 r2 \n.end").unwrap();
        let origin = parse_lexemes(&lexemes).unwrap().first().unwrap().to_owned();

        assert_eq!(
            origin.statements,
            vec![Statement {
                kind: StatementKind::AddAnd(
                    AddAndKind::Add,
                    RegisterNum::new(0).unwrap(),
                    RegisterNum::new(1).unwrap(),
                    Either::B(RegisterNum::new(2).unwrap())
                ),
                lexemes: lexemes[3..7].to_vec(),
                label: None,
            }]
        )
    }

    #[test]
    fn requires_newline_before_dot_end() {
        let lexemes = lex(" .orig #3000\nadd r0 r1 r2 .end").unwrap();
        assert!(parse_lexemes(&lexemes).is_err())
    }

    #[test]
    fn origin_with_two_statements() {
        let lexemes = lex(" .orig #3000\nadd r0 r1 #12\n  and r7 r2 r5 \n.end").unwrap();
        let origin = parse_lexemes(&lexemes).unwrap().first().unwrap().to_owned();

        assert_eq!(
            origin.statements,
            vec![
                Statement {
                    kind: StatementKind::AddAnd(
                        AddAndKind::Add,
                        RegisterNum::new(0).unwrap(),
                        RegisterNum::new(1).unwrap(),
                        Either::A(Imm5::new(12).unwrap())
                    ),
                    lexemes: lexemes[3..7].to_vec(),
                    label: None,
                },
                Statement {
                    kind: StatementKind::AddAnd(
                        AddAndKind::And,
                        RegisterNum::new(7).unwrap(),
                        RegisterNum::new(2).unwrap(),
                        Either::B(RegisterNum::new(5).unwrap())
                    ),
                    lexemes: lexemes[8..12].to_vec(),
                    label: None,
                }
            ]
        )
    }

    #[test]
    fn two_origins() {
        let lexemes = lex(" \n .ORIG #300 \n.end \n .orig #4002 \n\n\n .end");
        assert_eq!(parse_lexemes(&lexemes.unwrap()).unwrap().len(), 2)
    }

    #[test]
    fn statement_with_label() {
        let lexemes = lex(" .orig #3000\n someLabel add r0 r1 r2 \n.end").unwrap();
        assert_eq!(
            parse_lexemes(&lexemes).unwrap()[0].statements[0]
                .clone()
                .label
                .unwrap(),
            "somelabel"
        );
    }

    #[test]
    fn statement_with_label_before_linebreak() {
        let lexemes = lex(" .orig #3000\n someLabel\n add r0 r1 r2 \n.end").unwrap();
        assert_eq!(
            parse_lexemes(&lexemes).unwrap()[0].statements[0]
                .clone()
                .label
                .unwrap(),
            "somelabel"
        );
    }

    #[test]
    fn origin_with_label() {
        let lexemes = lex(" goodOrigin .orig #3000\n add r0 r1 r2 \n.end").unwrap();
        assert_eq!(
            parse_lexemes(&lexemes).unwrap()[0].clone().label.unwrap(),
            "goodorigin"
        );
    }

    #[test]
    fn origin_with_label_before_linebreak() {
        let lexemes = lex(" goodOrigin \n.orig #3000\n add r0 r1 r2 \n.end").unwrap();
        assert_eq!(
            parse_lexemes(&lexemes).unwrap()[0].clone().label.unwrap(),
            "goodorigin"
        );
    }

    #[test]
    fn three_errors_identified_in_origin() {
        let lexemes =
            lex(".orig #3000\nadd r0 r2 hello \n and r1 r2\n and r1 bob r2\n .end").unwrap();
        assert_eq!(parse_lexemes(&lexemes).unwrap_err().len(), 3);
    }
}
