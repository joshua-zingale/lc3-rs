use crate::asm::{lexer::{DirectiveSymbol, Lexeme, LexemeKind, lex}, types::{Location, ParsingError, ParsingErrorKind, RegisterNum}};

pub fn parse(source: &[u8]) -> Result<Vec<Origin>, ParsingError> {
    parse_from_lexemes(&lex(source).unwrap())
}

pub fn parse_from_lexemes(lexemes: &[Lexeme]) -> Result<Vec<Origin>, ParsingError> {
    
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
    lexemes: &'a [Lexeme<'a>]
}


impl<'a> Parser<'a> {

    fn parse_origin(&mut self) -> Result<Origin, ParsingError> {
        self.consume(LexemeKind::Directive(DirectiveSymbol::Orig))?;
        let address: u16 = match &self.curr_lexeme().kind {
            LexemeKind::Immediate(value) => {
                u16::try_from(*value).map_err(|_| self.make_error(ParsingErrorKind::UnsignedNumberOutOfRange(16, *value)))?
            }
            kind => return Err(self.make_error(ParsingErrorKind::ExpectedButFound("immediate value".to_string(), kind.string_name())))
        };
        self.next_lexeme();

        self.consume(LexemeKind::LineBreak)?;

        self.consume(LexemeKind::Directive(DirectiveSymbol::End))?;
        
        Ok(Origin{address, statements: vec![]})
    }

    fn make_error(&self, kind: ParsingErrorKind) -> ParsingError {
        let (start, end) = self.curr_lexeme_location();
        ParsingError { kind, start, end }
    }

    fn curr_lexeme(&self) -> &'a Lexeme<'a> {
        &self.lexemes[self.pos]
    }

    fn next_lexeme(&mut self) -> Option<&'a Lexeme<'a>> {
        if self.pos < self.lexemes.len() {
            self.pos += 1;
            Some(&self.lexemes[self.pos - 1])
        } else {
            None
        }
    }

    fn consume_descriminant(&mut self, lexeme_kind: LexemeKind<'a>) -> Result<&Lexeme<'a>, ParsingError> {
        match self.lexemes.get(self.pos) {
            None => Err(ParsingError { kind: ParsingErrorKind::ExpectedButFound(lexeme_kind.string_name(), "end of file".to_string()), start: self.curr_lexeme_location().0, end: self.curr_lexeme_location().1 }),
            Some(lexeme) if std::mem::discriminant(&lexeme.kind) == std::mem::discriminant(&lexeme_kind) => {
                self.pos += 1;
                Ok(lexeme)
            },
            Some(lexeme) => Err(ParsingError { kind: ParsingErrorKind::ExpectedButFound(lexeme_kind.string_name(), lexeme.kind.string_name()), start: self.curr_lexeme_location().0, end: self.curr_lexeme_location().1 })
        }
    }

    fn consume(&mut self, lexeme_kind: LexemeKind<'a>) -> Result<&Lexeme<'a>, ParsingError> {
        match self.lexemes.get(self.pos) {
            None => Err(ParsingError { kind: ParsingErrorKind::ExpectedButFound(lexeme_kind.string_name(), "end of file".to_string()), start: self.curr_lexeme_location().0, end: self.curr_lexeme_location().1 }),
            Some(lexeme) if lexeme.kind == lexeme_kind => {
                self.pos += 1;
                Ok(lexeme)
            },
            Some(lexeme) => Err(ParsingError { kind: ParsingErrorKind::ExpectedButFound(lexeme_kind.string_name(), lexeme.kind.string_name()), start: self.curr_lexeme_location().0, end: self.curr_lexeme_location().1 })
        }
    }

    fn skip(&mut self, lexeme_kind: LexemeKind<'a>) {
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
pub struct Origin{
    pub address: u16,
    pub statements: Vec<Statement>
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
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

    #[test]
    fn empty_origin() {
        assert_eq!(
            *parse(b".orig #100\n.end").unwrap().first().unwrap(),
            Origin{
                address: 100,
                statements: vec![]
            },
        )
    }

}