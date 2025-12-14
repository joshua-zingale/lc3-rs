use crate::asm::{lexer::{DirectiveSymbol, InstructionSymbol, Lexeme, LexemeKind}, types::{Address, Either, Imm5, Location, NBitInt, ParsingError, ParsingErrorKind, RegisterNum}};

pub fn parse<'a>(lexemes: &'a [Lexeme]) -> Result<Vec<Origin<'a>>, ParsingError> {
    
    let mut parser = Parser{pos: 0, lexemes};

    let mut origins = Vec::new();
    parser.skip(LexemeKind::LineBreak);
    while parser.pos < lexemes.len(){
        let origin = parser.parse_origin()?;
        origins.push(origin);
        parser.skip(LexemeKind::LineBreak);
    }

    return Ok(origins)
}

struct Parser<'a> {
    pos: usize,
    lexemes: &'a [Lexeme]
}


impl<'a> Parser<'a> {

    fn parse_origin(&mut self) -> Result<Origin<'a>, ParsingError> {
        let orig_lexeme = self.consume(LexemeKind::Directive(DirectiveSymbol::Orig))?;
        let (immediate_lexeme, address)=  self.consume_immediate::<16, false>()?;
        
        let mut statements = vec![];
        self.consume(LexemeKind::LineBreak)?;

        while let Some(lex) = self.curr_lexeme() && lex.kind != LexemeKind::Directive(DirectiveSymbol::End) {
            statements.push(self.consume_statement()?);
            self.consume(LexemeKind::LineBreak)?;
        }


        let end_lexeme = self.consume(LexemeKind::Directive(DirectiveSymbol::End))?;
        
        Ok(Origin{address, statements, orig_lexeme, immediate_lexeme, end_lexeme})
    }

    fn consume_immediate<const BITS: u32, const SIGNED: bool>(&mut self) -> Result<(&'a Lexeme, NBitInt<BITS, SIGNED>), ParsingError> {
        let immediate_lexeme=  self.consume_any("immediate value")?;
        if let LexemeKind::Immediate(value)  = immediate_lexeme.kind {
            let n_bit_int = NBitInt::<BITS, SIGNED>::new(value).map_err(|kind| self.make_error(kind))?;
            Ok((immediate_lexeme, n_bit_int))
        } else {
            Err(self.make_error(ParsingErrorKind::ExpectedButFound("immediate value".to_string(), immediate_lexeme.kind.string_name())))
        }
    }

    fn consume_register(&mut self) -> Result<RegisterNum, ParsingError> {
        let register_lexeme=  self.consume_any("register")?;
        if let LexemeKind::Register(value)  = register_lexeme.kind {
            Ok(value)
        } else {
            Err(self.make_error(ParsingErrorKind::ExpectedButFound("immediate value".to_string(), register_lexeme.kind.string_name())))
        }
    }

    fn consume_immediate_or_register<const BITS: u32, const SIGNED: bool>(&mut self) -> Result<Either<NBitInt<BITS, SIGNED>, RegisterNum>, ParsingError> {
        let lexeme=  self.consume_any("immediate value")?;
        if let LexemeKind::Immediate(value)  = lexeme.kind {
            let n_bit_int = NBitInt::<BITS, SIGNED>::new(value).map_err(|kind| self.make_error(kind))?;
            Ok(Either::A( n_bit_int))
        } else if let LexemeKind::Register(value)  = lexeme.kind {
            Ok(Either::B(value))
        } else {
            Err(self.make_error(ParsingErrorKind::ExpectedButFound("immediate value or register".to_string(), lexeme.kind.string_name())))
        }
    }

    fn consume_statement(&mut self) -> Result<Statement<'a>, ParsingError> {
        let instruction_lexeme = self.consume_any("instruction")?;
        match &instruction_lexeme.kind {
            LexemeKind::Directive(DirectiveSymbol::Orig) => Err(self.make_error(ParsingErrorKind::ExpectedButFound("instruction".to_string(), "ORIG directive".to_string()))),
            LexemeKind::Directive(DirectiveSymbol::End) => Err(self.make_error(ParsingErrorKind::ExpectedButFound("instruction".to_string(), "END directive".to_string()))),
            LexemeKind::Instruction(symbol) => match symbol {
                InstructionSymbol::Add => {
                    let r1 = self.consume_register()?;
                    let r2= self.consume_register()?;
                    let kind =  match self.consume_immediate_or_register::<5, true>()? {
                        Either::A(im) => StatementKind::AddI(r1, r2, im),
                        Either::B(reg) => StatementKind::Add(r1, r2, reg)
                    };
                    Ok(Statement {kind, lexemes: &self.lexemes[self.pos-4..self.pos]})
                },
                InstructionSymbol::And => {
                    let r1 = self.consume_register()?;
                    let r2= self.consume_register()?;
                    let kind =  match self.consume_immediate_or_register::<5, true>()? {
                        Either::A(im) => StatementKind::AndI(r1, r2, im),
                        Either::B(reg) => StatementKind::And(r1, r2, reg)
                    };
                    Ok(Statement {kind, lexemes: &self.lexemes[self.pos-4..self.pos]})
                },
            },
            _ => todo!()
        }
    }

    fn make_error(&self, kind: ParsingErrorKind) -> ParsingError {
        let (start, end) = self.curr_lexeme_location();
        ParsingError { kind, start, end }
    }

    fn curr_lexeme(&self) -> Option<&'a Lexeme> {
        self.lexemes.get(self.pos)
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

    fn next_lexeme(&mut self) -> Option<&'a Lexeme> {
        if self.pos < self.lexemes.len() {
            self.pos += 1;
            Some(&self.lexemes[self.pos - 1])
        } else {
            None
        }
    }

    fn consume_descriminant(&mut self, lexeme_kind: LexemeKind) -> Result<&'a Lexeme, ParsingError> {
        match self.lexemes.get(self.pos) {
            None => Err(ParsingError { kind: ParsingErrorKind::ExpectedButFound(lexeme_kind.string_name(), "end of file".to_string()), start: self.curr_lexeme_location().0, end: self.curr_lexeme_location().1 }),
            Some(lexeme) if std::mem::discriminant(&lexeme.kind) == std::mem::discriminant(&lexeme_kind) => {
                self.pos += 1;
                Ok(lexeme)
            },
            Some(lexeme) => Err(ParsingError { kind: ParsingErrorKind::ExpectedButFound(lexeme_kind.string_name(), lexeme.kind.string_name()), start: self.curr_lexeme_location().0, end: self.curr_lexeme_location().1 })
        }
    }

    fn consume(&mut self, lexeme_kind: LexemeKind) -> Result<&'a Lexeme, ParsingError> {
        match self.lexemes.get(self.pos) {
            None => Err(ParsingError { kind: ParsingErrorKind::ExpectedButFound(lexeme_kind.string_name(), "end of file".to_string()), start: self.curr_lexeme_location().0, end: self.curr_lexeme_location().1 }),
            Some(lexeme) if lexeme.kind == lexeme_kind => {
                self.pos += 1;
                Ok(lexeme)
            },
            Some(lexeme) => Err(ParsingError { kind: ParsingErrorKind::ExpectedButFound(lexeme_kind.string_name(), lexeme.kind.string_name()), start: self.curr_lexeme_location().0, end: self.curr_lexeme_location().1 })
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
            None => (self.lexemes.last().unwrap().end, self.lexemes.last().unwrap().end),
            Some(lexeme) => (lexeme.start, lexeme.end)
        }
    }
}



#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Origin<'a> {
    pub address: Address,
    pub statements: Vec<Statement<'a>>,
    pub orig_lexeme: &'a Lexeme,
    pub immediate_lexeme: &'a Lexeme,
    pub end_lexeme: &'a Lexeme,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Statement<'a> {
    kind: StatementKind,
    lexemes: &'a[Lexeme]
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StatementKind {
    Add(RegisterNum, RegisterNum, RegisterNum),
    AddI(RegisterNum, RegisterNum, Imm5),
    And(RegisterNum, RegisterNum, RegisterNum),
    AndI(RegisterNum, RegisterNum, Imm5),

}

trait StatementArgument {
    fn string_name(&self) -> String;
}


#[cfg(test)]
mod tests {
    use super::*;
    use super::super::lexer::lex;
    use super::super::types::RegisterNum;

    #[test]
    fn empty_origin() {
        let lexemes = lex(b".orig #100\n.end").unwrap();
        assert_eq!(
            *parse(&lexemes).unwrap().first().unwrap(),
            Origin {
                address: Address::new(100).unwrap(),
                statements: vec![],
                orig_lexeme: &lexemes[0],
                immediate_lexeme: &lexemes[1],
                end_lexeme: &lexemes[3],
            },
        )
    }

    #[test]
    fn origin_with_one_statement() {
        let lexemes = lex(b" .orig #3000\nadd r0 r1 r2 \n.end").unwrap();
        let origin = parse(&lexemes).unwrap().first().unwrap().to_owned();

        assert_eq!(
            origin.statements,
            vec![
                Statement{
                    kind: StatementKind::Add(RegisterNum::new(0).unwrap(), RegisterNum::new(1).unwrap(), RegisterNum::new(2).unwrap()),
                    lexemes: &lexemes[3..7]
                }
            ]
        )

    }

    #[test]
    fn requires_newline_before_end() {
        let lexemes = lex(b" .orig #3000\nadd r0 r1 r2 .end").unwrap();
        assert!(
            parse(&lexemes).is_err()
        )

    }

    #[test]
    fn origin_with_two_statements() {
        let lexemes = lex(b" .orig #3000\nadd r0 r1 #12\n  and r7 r2 r5 \n.end").unwrap();
        let origin = parse(&lexemes).unwrap().first().unwrap().to_owned();

        assert_eq!(
            origin.statements,
            vec![
                Statement{
                    kind: StatementKind::AddI(RegisterNum::new(0).unwrap(), RegisterNum::new(1).unwrap(), Imm5::new(12).unwrap()),
                    lexemes: &lexemes[3..7]
                },
                Statement{
                    kind: StatementKind::And(RegisterNum::new(7).unwrap(), RegisterNum::new(2).unwrap(), RegisterNum::new(5).unwrap()),
                    lexemes: &lexemes[8..12]
                }
            ]
        )

    }

    #[test]
    fn two_origins() {
        let lexemes = lex(b" \n .ORIG #300 \n.end \n .orig #4002 \n\n\n .end");
        assert_eq!(parse(&lexemes.unwrap()).unwrap().len(), 2)
    }

}