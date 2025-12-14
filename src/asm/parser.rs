use crate::asm::{lexer::{DirectiveSymbol, Lexeme, LexemeKind}, types::{Location, ParsingError, ParsingErrorKind, RegisterNum}};

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
        let immediate_lexeme: &Lexeme=  self.consume_any("immediate value")?;

        let address: u16 = if let LexemeKind::Immediate(value)  = immediate_lexeme.kind {
             u16::try_from(value).map_err(|_| self.make_error(ParsingErrorKind::UnsignedNumberOutOfRange(16, value)))?
        } else {
            return Err(self.make_error(ParsingErrorKind::ExpectedButFound("immediate value".to_string(), immediate_lexeme.kind.string_name())))
        };

        self.consume(LexemeKind::LineBreak)?;

        let end_lexeme = self.consume(LexemeKind::Directive(DirectiveSymbol::End))?;
        
        Ok(Origin{address, statements: vec![], orig_lexeme, immediate_lexeme, end_lexeme})
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
    pub address: u16,
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


type Imm5 = NBitInt<5, true>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NBitInt<const BITS: u32, const SIGNED: bool>(i32);

impl<const BITS: u32, const SIGNED: bool> NBitInt<BITS, SIGNED> {
    pub fn new(v: i32) -> Result<Self, ()> {
        {
            let min = if SIGNED { -(1 << (BITS - 1)) } else { 0 };
            let max = if SIGNED {
                (1 << (BITS - 1)) - 1
            } else {
                (1 << BITS) - 1
            };

            if v < min || v > max {
                return Err(());
            }
        }

        let masked = if SIGNED {
            let shift = 32 - BITS;
            v << shift >> shift
        } else {
            v & ((1 << BITS) - 1)
        };

        Ok(Self(masked))
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use super::super::lexer::lex;

    #[test]
    fn empty_origin() {
        let lexemes = lex(b".orig #100\n.end").unwrap();
        assert_eq!(
            *parse(&lexemes).unwrap().first().unwrap(),
            Origin{
                address: 100,
                statements: vec![],
                orig_lexeme: &lexemes[0],
                immediate_lexeme: &lexemes[1],
                end_lexeme: &lexemes[3],
            },
        )
    }

}