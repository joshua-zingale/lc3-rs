
use std::ops::{BitOr};

use crate::asm::types::{Location, ParsingError, ParsingErrorKind, RegisterNum};

pub fn lex<'a>(source: &'a [u8]) -> Result<Vec<Lexeme<'a>>, Vec<Result<Lexeme<'a>, ParsingError>>> {
    let lexemes: Vec<_> = Lexer::new(source).collect();

    if lexemes.iter().all(Result::is_ok) {
        Ok(lexemes.into_iter().map(Result::unwrap).collect())
    } else {
        Err(lexemes)
    }
}

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

    fn advance_to_end_of_word(&mut self) {
        while let Some(c) = self.peek_char() && !skippable(c) && c != b'\n' {
            self.pos.advance_char();
        }
    }
}

fn skippable(char: u8) -> bool {
    return char == b' ' || char == b'\t' || char == b'\r' || char == b','
}

fn lowercase(chars: &[u8]) -> Vec<u8> {
    chars.iter().map(|c| c.bitor(0x20)).collect()
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
            b'.' => {
                self.advance_to_end_of_word();
                let directive = &unsafe {self.lexeme_slice_unchecked()}[1..];
                match &lowercase(directive)[..] {
                    b"orig" => Ok(self.make_lexeme(LexemeKind::Directive(DirectiveSymbol::Orig))),
                    b"end" => Ok(self.make_lexeme(LexemeKind::Directive(DirectiveSymbol::End))),
                    _ => {
                        let directive_string = str::from_utf8(directive).expect("should be valid uft8");
                        Err(self.make_error(ParsingErrorKind::InvalidDirective(directive_string.to_string())))
                    }
                }
            }
            b'#' => {
                self.advance_to_end_of_word();
                let lexeme_slice = unsafe {self.lexeme_slice_unchecked()};
                let str_number =  str::from_utf8(&lexeme_slice[1..]).expect("should be valid utf8");
                if lexeme_slice.len() >= 2 && lexeme_slice[0] == b'#' && lexeme_slice[1..].iter().all(|x| (b'0'..=b'9').contains(x) || *x == b'-') {
                    let Ok(value) = str_number.parse() else {
                        return Some(Err(self.make_error(ParsingErrorKind::InvalidDecimalNumber(str_number.to_string()))))
                    };
                    Ok(self.make_lexeme(LexemeKind::Immediate(value)))
                } else {
                    Err(self.make_error(ParsingErrorKind::InvalidDecimalNumber(str_number.to_string())))
                }
            }
            _ => {
                self.advance_to_end_of_word();
                let lexeme_slice= &unsafe {self.lexeme_slice_unchecked()}[..];
                if lexeme_slice.len() == 2 && (lexeme_slice[0] == b'r' || lexeme_slice[0] == b'R') && (b'0'..=b'7').contains(&lexeme_slice[1]) {
                    return Some(Ok(self.make_lexeme(LexemeKind::Register(RegisterNum(lexeme_slice[1] - b'0')))))
                }
                match &lowercase(lexeme_slice)[..] {
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

impl<'a> LexemeKind<'a> {
    pub fn string_name(&self) -> String {
        use LexemeKind::*;
        match self {
            Directive(sym) => {
                format!("{} directive", match sym {
                    DirectiveSymbol::Orig => "ORIG",
                    DirectiveSymbol::End => "END"
                })
            },
            Immediate(_) => "immediate".to_string(),
            Instruction(_) => "instruction".to_string(),
            Label(_) => "label".to_string(),
            Register(_) => "register".to_string(),
            String(_) => "string literal".to_string(),
            LineBreak => "line break".to_string()
        }
    }
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
    fn directives() {
        assert_eq!(
            lex_unwrap_kind(b".orig .end .oRig .END"),
            vec![
                LexemeKind::Directive(DirectiveSymbol::Orig),
                LexemeKind::Directive(DirectiveSymbol::End),
                LexemeKind::Directive(DirectiveSymbol::Orig),
                LexemeKind::Directive(DirectiveSymbol::End)
            ]
        )
    }

    #[test]
    fn instruction_symbols() {
        use InstructionSymbol::*;
        assert_eq!(
            lex_unwrap_kind(b"add AND and ADD"),
            vec![
                LexemeKind::Instruction(Add),
                LexemeKind::Instruction(And),
                LexemeKind::Instruction(And),
                LexemeKind::Instruction(Add),]
        )
    }
    #[test]
    fn registers() {
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
    fn line_break() {
        assert_eq!(
            lex_unwrap_kind(b"  \n \n \n\n \n"),
            vec![
                LexemeKind::LineBreak
                ]
        )
    }

    #[test]
    fn labels() {
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
    fn decimal_immediates() {
        assert_eq!(
            lex_unwrap_kind(b"#103 #3123 #-32"),
            vec![
                LexemeKind::Immediate(103), LexemeKind::Immediate(3123), LexemeKind::Immediate(-32)
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

    #[test]
    fn invalid_decimal_number_error() {
        assert_eq!(
            lex_errors(b"#104 #3-3 #b5 #-3-").iter().map(|x| x.kind.clone()).collect::<Vec<_>>(),
            vec![
                ParsingErrorKind::InvalidDecimalNumber("3-3".to_string()),
                ParsingErrorKind::InvalidDecimalNumber("b5".to_string()),
                ParsingErrorKind::InvalidDecimalNumber("-3-".to_string()),
            ]
        )
    }
}