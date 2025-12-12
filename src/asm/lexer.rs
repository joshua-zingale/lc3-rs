
use crate::asm::types::{Location, ParsingError, ParsingErrorKind, RegisterNum};
pub struct Lexer<'a>{
    source: &'a [u8],
    pos: Location,
    start_of_curr_lexeme: Location,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a [u8]) -> Lexer<'a> {
        Lexer { source: source, pos: Location::default(), start_of_curr_lexeme: Location::default() }
    }
}

impl<'a> Lexer<'a> {
     fn peek_char(&self) -> Option<u8> {
        if self.pos.offset < self.source.len() {
            Some(self.source[self.pos.offset])
        } else {
            None
        }
    }

    fn next_char(&mut self) -> Option<u8> {
        match self.peek_char() {
            Some(c) => {
                self.pos.advance(c);
                Some(c)
            }
            None => None
        }
    }

    unsafe fn advance_char(&mut self) {
        let char = self.source[self.pos.offset];
        self.pos.advance(char);
    }

    fn start_lexeme(&mut self) {
        self.start_of_curr_lexeme = self.pos;
    }

    unsafe fn lexeme_slice_unchecked(&self) -> &'a [u8] {
        &self.source[self.start_of_curr_lexeme.offset..self.pos.offset]
    }
    
    fn make_error(&self, kind: ParsingErrorKind) -> ParsingError {
        ParsingError{kind: kind, start: self.start_of_curr_lexeme, end: self.pos}
    }
    fn make_lexeme(&self, kind: LexemeKind<'a>) -> Lexeme<'a> {
        Lexeme{kind: kind, start: self.start_of_curr_lexeme, end: self.pos}
    }
}

fn skippable(char: u8) -> bool {
    return char == b' ' || char == b'\t' || char == b'\r' || char == b','
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Lexeme<'a>, ParsingError>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(c) = self.peek_char() {
            if !skippable(c) {
                break
            }
            unsafe {
                self.advance_char();
            }
        }

        self.start_lexeme();

        let first_char = self.next_char()?;

        return Some(match first_char {
            b'\n' => {
                while let Some(c) = self.peek_char() && (skippable(c) || c == b'\n') {
                    unsafe { self.advance_char() };
                }
                Ok(self.make_lexeme(LexemeKind::LineBreak))
            },
            _ => {
                while let Some(c) = self.peek_char() && !skippable(c) && c != b'\n' {
                    self.pos.advance_char();
                }
                let lexeme_slice= unsafe {self.lexeme_slice_unchecked()};
                if lexeme_slice.len() == 2 && lexeme_slice[0] == b'r'  && (b'0'..=b'7').contains(&lexeme_slice[1]) {
                    return Some(Ok(self.make_lexeme(LexemeKind::Register(RegisterNum(lexeme_slice[1] - b'0')))))
                }
                if lexeme_slice.len() >= 2 && lexeme_slice[0] == b'#' && lexeme_slice[1..].iter().all(|x| (b'0'..=b'9').contains(x)) {
                    // return Some(Ok(self.make_lexeme(LexemeKind::Immediate(lexeme_slice as i32))))
                }
                match lexeme_slice {
                    b"add" => Ok(self.make_lexeme(LexemeKind::Instruction(InstructionSymbol::Add))),
                    b"and" => Ok(self.make_lexeme(LexemeKind::Instruction(InstructionSymbol::And))),
                    _ if lexeme_slice.len() > 20 => Err(self.make_error(ParsingErrorKind::LabelTooLong(lexeme_slice.len()))),
                    _ => Ok(self.make_lexeme(LexemeKind::Label(lexeme_slice)))
                }
            }
        })
    }
}


#[derive(Debug, PartialEq, Eq)]
pub struct Lexeme<'a> {
    pub kind: LexemeKind<'a>,
    pub start: Location,
    pub end: Location,
}

#[derive(Debug, PartialEq, Eq)]
pub enum LexemeKind<'a> {
    Directive(DirectiveSymbol),
    Immediate(i32),
    Instruction(InstructionSymbol),
    Label(&'a [u8]),
    Register(RegisterNum),
    String(Vec<u8>),
    LineBreak,
}

#[derive(Debug, PartialEq, Eq)]
pub enum DirectiveSymbol {
    Orig,
    End,
}

#[derive(Debug, PartialEq, Eq)]
pub enum InstructionSymbol {
    Add,
    And,
    // Br,
    // Jmp,
    // Jsr,
    // Jsrr,
    // Ld,
    // Ldi,
    // Ldr,
    // Lea,
    // Not,
    // Ret,
    // Rti,
    // Sti,
    // Str,
    // Trap,
    // Out,
    // Puts,
}


#[cfg(test)]
mod tests {
    use super::*;

    fn lex_unwrap(source: &[u8]) -> Vec<Lexeme> {
        Lexer::new(source).map(|x| x.unwrap()).collect()
    }

    fn lex_unwrap_kind(source: &[u8]) -> Vec<LexemeKind> {
        Lexer::new(source).map(|x| x.unwrap().kind).collect()
    }

    fn lex_errors(source: &[u8]) -> Vec<ParsingError> {
        Lexer::new(source).filter_map(|x| match x {
            Ok(_) => None,
            Err(e) => Some(e)
        }).collect()
    }
     

    #[test]
    fn lexes_instruction_symbols() {
        use InstructionSymbol::*;
        assert_eq!(
            lex_unwrap_kind(b"add and and add"),
            vec![
                LexemeKind::Instruction(Add),
                LexemeKind::Instruction(And),
                LexemeKind::Instruction(And),
                LexemeKind::Instruction(Add),]
        )
    }
    #[test]
    fn lexes_registers() {
        assert_eq!(
            lex_unwrap_kind(b"r0 r1 r2 r3 r4 r5 r6 r7"),
            vec![
                LexemeKind::Register(RegisterNum(0)),
                LexemeKind::Register(RegisterNum(1)),
                LexemeKind::Register(RegisterNum(2)),
                LexemeKind::Register(RegisterNum(3)),
                LexemeKind::Register(RegisterNum(4)),
                LexemeKind::Register(RegisterNum(5)),
                LexemeKind::Register(RegisterNum(6)),
                LexemeKind::Register(RegisterNum(7))
                ]
        )
    }

     #[test]
    fn lexes_line_break() {
        assert_eq!(
            lex_unwrap_kind(b"  \n \n \n\n \n"),
            vec![
                LexemeKind::LineBreak
                ]
        )
    }

    #[test]
    fn lexes_labels() {
        assert_eq!(
            lex_unwrap_kind(b"this is a whole lot of labels"),
            vec![
                LexemeKind::Label(b"this"),
                LexemeKind::Label(b"is"),
                LexemeKind::Label(b"a"),
                LexemeKind::Label(b"whole"),
                LexemeKind::Label(b"lot"),
                LexemeKind::Label(b"of"),
                LexemeKind::Label(b"labels")
                ]
        )
    }

    #[test]
    fn lexer_gets_positions() {
        use crate::asm::types::Location;

        let lexer = Lexer::new(b"add\n and");

        let locs: Vec<_> = lexer.map(|x: Result<Lexeme<'_>, ParsingError>| {
            let l = x.unwrap();
            (l.start, l.end)}).collect();
        
        assert_eq!(
            locs,
            vec![
                (Location{line: 1, column: 1, offset: 0}, Location{line: 1, column: 4, offset: 3}),
                (Location{line: 1, column: 4, offset: 3}, Location{line: 2, column: 2, offset: 5}),
                (Location{line: 2, column: 2, offset: 5}, Location{line: 2, column: 5, offset: 8})
                ]
        )
    }

    #[test]
    fn long_label_errors() {
        assert_eq!(
            lex_errors(b"o12345678901234567890"),
            vec![
                ParsingError{
                    kind: ParsingErrorKind::LabelTooLong(21),
                    start: Location{line:1,column:1, offset: 0},
                    end: Location{line: 1, column: 22, offset:21}}]
        )
    }
}