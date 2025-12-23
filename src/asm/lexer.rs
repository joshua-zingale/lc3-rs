
use std::ops::{BitOr};

use crate::asm::types::{Location, ParsingError, ParsingErrorKind, RegisterNum};

pub fn lex(source: &str) -> Result<Vec<Lexeme>, Vec<Result<Lexeme, ParsingError>>> {
    let lexemes: Vec<_> = Lexer::new(source).collect();

    if lexemes.iter().all(Result::is_ok) {
        Ok(lexemes.into_iter().map(Result::unwrap).collect())
    } else {
        Err(lexemes)
    }
}

#[derive(Clone)]
pub struct Lexer<'a>{
    source: &'a str,
    pos: Location,
    start_of_curr_lexeme: Location,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str) -> Lexer<'a> {
        Lexer { source: source, pos: Location::default(), start_of_curr_lexeme: Location::default() }
    }
}

impl<'a> Lexer<'a> {
     fn peek_char(&self) -> Option<char> {
        self.source[self.pos.offset..].chars().next()
    }

    fn next_char(&mut self) -> Option<char> {
        match self.peek_char() {
            Some(c) => {
                self.pos.advance(c);
                Some(c)
            }
            None => None
        }
    }

    unsafe fn advance_char(&mut self) {
        let char = self.peek_char().unwrap();
        self.pos.advance(char);
    }

    fn start_lexeme(&mut self) {
        self.start_of_curr_lexeme = self.pos;
    }

    unsafe fn lexeme_slice_unchecked(&self) -> &'a str {
        &self.source[self.start_of_curr_lexeme.offset..self.pos.offset]
    }

    fn peek_lexeme_cdr(&self) -> String {
        let mut lexer = self.clone();
        lexer.advance_to_end_of_word();
        let mut lexeme = unsafe { lexer.lexeme_slice_unchecked() }.chars();
        lexeme.next();
        lexeme.collect()
    }
    
    fn make_error(&self, kind: ParsingErrorKind) -> ParsingError {
        ParsingError{kind: kind, start: self.start_of_curr_lexeme, end: self.pos}
    }
    fn make_lexeme(&self, kind: LexemeKind ) -> Lexeme {
        Lexeme{kind: kind, start: self.start_of_curr_lexeme, end: self.pos}
    }

    fn advance_to_end_of_word(&mut self) {
        while let Some(c) = self.peek_char() && !skippable(c) && c != '\n' {
            self.pos.advance(c);
        }
    }

}

fn skippable(char: char) -> bool {
    return char == ' ' || char == '\t' || char == '\r' || char == ','
}

fn lowercase(chars: &[u8]) -> Vec<u8> {
    chars.iter().map(|c| c.bitor(0x20)).collect()
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Lexeme, ParsingError>;

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
            '\n' => {
                while let Some(c) = self.peek_char() && (skippable(c) || c == '\n') {
                    unsafe { self.advance_char() };
                }
                Ok(self.make_lexeme(LexemeKind::LineBreak))
            },
            '.' => {
                self.advance_to_end_of_word();
                let directive = &unsafe {self.lexeme_slice_unchecked()}[1..];
                match directive.to_lowercase().as_str() {
                    "orig" => Ok(self.make_lexeme(LexemeKind::Directive(DirectiveSymbol::Orig))),
                    "end" => Ok(self.make_lexeme(LexemeKind::Directive(DirectiveSymbol::End))),
                    _ => {
                        Err(self.make_error(ParsingErrorKind::InvalidDirective(directive.to_string())))
                    }
                }
            }
            '#' => {
                self.advance_to_end_of_word();
                let lexeme_slice = unsafe {self.lexeme_slice_unchecked()};
                let str_number =  lexeme_slice['#'.len_utf8()..].chars();
                if lexeme_slice.len() >= 2 {
                    let Ok(value) = str_number.as_str().parse() else {
                        return Some(Err(self.make_error(ParsingErrorKind::InvalidDecimalNumber(str_number.collect()))))
                    };
                    Ok(self.make_lexeme(LexemeKind::Immediate(value)))
                } else {
                    Err(self.make_error(ParsingErrorKind::InvalidDecimalNumber(str_number.collect())))
                }
            },
            'x' | 'X' if i32::from_str_radix(&self.peek_lexeme_cdr(), 16).is_ok() => {
                self.advance_to_end_of_word();
                Ok(self.make_lexeme(LexemeKind::Immediate(i32::from_str_radix(&self.peek_lexeme_cdr(), 16).unwrap())))
            },
            _ => {
                self.advance_to_end_of_word();
                let lexeme_slice= unsafe {self.lexeme_slice_unchecked()};
                let lexeme_slice_bytes = lexeme_slice.as_bytes();
                if lexeme_slice_bytes.len() == 2 && (lexeme_slice_bytes[0] == b'r' || lexeme_slice_bytes[0] == b'R') && (b'0'..=b'7').contains(&lexeme_slice_bytes[1]) {
                    return Some(Ok(self.make_lexeme(LexemeKind::Register(RegisterNum::new(i32::try_from(lexeme_slice_bytes[1] - b'0').unwrap()).unwrap()))))
                }
                match lexeme_slice.to_lowercase().as_str() {
                    "add" => Ok(self.make_lexeme(LexemeKind::Instruction(InstructionSymbol::Add))),
                    "and" => Ok(self.make_lexeme(LexemeKind::Instruction(InstructionSymbol::And))),
                    "not" => Ok(self.make_lexeme(LexemeKind::Instruction(InstructionSymbol::Not))),
                    _ if lexeme_slice.len() > 20 => Err(self.make_error(ParsingErrorKind::LabelTooLong(lexeme_slice.len()))),
                    slice if !(
                        slice.chars().all(|c|
                            ('a'..='z').contains(&c)
                            || ('A'..='Z').contains(&c)
                            || ('0'..='9').contains(&c))
                        && (
                            ('a'..='z').contains(&first_char)
                            || ('A'..='Z').contains(&first_char))) => Err(self.make_error(ParsingErrorKind::InvalidCharacterInLabel)),
                    lowercase_slice => Ok(self.make_lexeme(LexemeKind::Label(lowercase_slice.to_string())))
                }
            }
        })
    }
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lexeme {
    pub kind: LexemeKind,
    pub start: Location,
    pub end: Location,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LexemeKind {
    Directive(DirectiveSymbol),
    Immediate(i32),
    Instruction(InstructionSymbol),
    Label(String),
    Register(RegisterNum),
    String(String),
    LineBreak,
}

impl LexemeKind {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DirectiveSymbol {
    Orig,
    End,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
    Not,
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
    use super::super::types::RegisterNum;

    fn lex_unwrap_kind(source: &str) -> Vec<LexemeKind> {
        Lexer::new(source).map(|x| x.unwrap().kind).collect()
    }

    fn lex_errors(source: &str) -> Vec<ParsingError> {
        Lexer::new(source).filter_map(|x| match x {
            Ok(_) => None,
            Err(e) => Some(e)
        }).collect()
    }
    #[test]
    fn directives() {
        assert_eq!(
            lex_unwrap_kind(".orig .end .oRig .END"),
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
            lex_unwrap_kind("add AdD and aND not Not"),
            vec![
                LexemeKind::Instruction(Add),
                LexemeKind::Instruction(Add),
                LexemeKind::Instruction(And),
                LexemeKind::Instruction(And),
                LexemeKind::Instruction(Not),
                LexemeKind::Instruction(Not)]
        )
    }
    #[test]
    fn registers() {
        assert_eq!(
            lex_unwrap_kind("r0 r1 r2 r3 r4 r5 r6 r7"),
            vec![
                LexemeKind::Register(RegisterNum::new(0).unwrap()),
                LexemeKind::Register(RegisterNum::new(1).unwrap()),
                LexemeKind::Register(RegisterNum::new(2).unwrap()),
                LexemeKind::Register(RegisterNum::new(3).unwrap()),
                LexemeKind::Register(RegisterNum::new(4).unwrap()),
                LexemeKind::Register(RegisterNum::new(5).unwrap()),
                LexemeKind::Register(RegisterNum::new(6).unwrap()),
                LexemeKind::Register(RegisterNum::new(7).unwrap())
                ]
        )
    }

     #[test]
    fn line_break() {
        assert_eq!(
            lex_unwrap_kind("  \n \n \n\n \n"),
            vec![
                LexemeKind::LineBreak
                ]
        )
    }

    #[test]
    fn labels() {
        assert_eq!(
            lex_unwrap_kind("this is a whole lot of labels xray"),
            vec![
                LexemeKind::Label("this".to_string()),
                LexemeKind::Label("is".to_string()),
                LexemeKind::Label("a".to_string()),
                LexemeKind::Label("whole".to_string()),
                LexemeKind::Label("lot".to_string()),
                LexemeKind::Label("of".to_string()),
                LexemeKind::Label("labels".to_string()),
                LexemeKind::Label("xray".to_string())
                ]
        )
    }

    #[test]
    fn lexer_gets_positions() {
        use crate::asm::types::Location;

        let lexer = Lexer::new("add\n and");

        let locs: Vec<_> = lexer.map(|x: Result<Lexeme, ParsingError>| {
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
            lex_unwrap_kind("#103 #3123 #-32"),
            vec![
                LexemeKind::Immediate(103), LexemeKind::Immediate(3123), LexemeKind::Immediate(-32)
            ]
        )
    }

    #[test]
    fn hex_immediates() {
        assert_eq!(
            lex_unwrap_kind("x103 X3123 x-32"),
            vec![
                LexemeKind::Immediate(0x103), LexemeKind::Immediate(0x3123), LexemeKind::Immediate(-0x32)
            ]
        )
    }

    #[test]
    fn long_label_errors() {
        assert_eq!(
            lex_errors("o12345678901234567890"),
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
            lex_errors("#104 #3-3 #b5 #-3-").iter().map(|x| x.kind.clone()).collect::<Vec<_>>(),
            vec![
                ParsingErrorKind::InvalidDecimalNumber("3-3".to_string()),
                ParsingErrorKind::InvalidDecimalNumber("b5".to_string()),
                ParsingErrorKind::InvalidDecimalNumber("-3-".to_string()),
            ]
        )
    }
}