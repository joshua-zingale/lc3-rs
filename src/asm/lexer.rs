
use crate::asm::types::{ParsingError, RegisterNum, Location};


impl Default for Location {
    fn default() -> Self {
        Location { line: 1, column: 1, offset: 0 }
    }
}

struct Lexer<'a>{
    source: &'a [u8],
    pos: Location,
    start_of_curr_lexeme: Location,
}

impl<'a> Lexer<'a> {
    fn new(source: &'a [u8]) -> Lexer<'a> {
        Lexer { source: source, pos: Location::default(), start_of_curr_lexeme: Location::default() }
    }

    fn peek_char(&self) -> Option<u8> {
        if self.pos.offset < self.source.len() {
            Some(self.source[self.pos.offset])
        } else {
            None
        }
    }

    fn peek_n_char(&self, n: usize) -> Option<u8> {
        if self.pos.offset + n < self.source.len() {
            Some(self.source[self.pos.offset + n])
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
    fn lexeme_slice(&self) -> Option<&'a [u8]> {
        if self.start_of_curr_lexeme.offset < self.pos.offset {
            Some(unsafe {self.lexeme_slice_unchecked()})
        } else {
            None
        }
        
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
                Ok(Lexeme::LineBreak)
            },
            _ => {
                while let Some(c) = self.peek_char() && !c.is_ascii_whitespace() {
                    self.pos.advance_char();
                }
                let lexeme_slice= unsafe {self.lexeme_slice_unchecked()};
                if lexeme_slice.len() == 2 && lexeme_slice[0] == b'r'  && (b'0'..=b'7').contains(&lexeme_slice[1]) {
                    return Some(Ok(Lexeme::Register(RegisterNum(lexeme_slice[1] - b'0'))))
                }
                match lexeme_slice {
                    b"add" => Ok(Lexeme::Instruction(InstructionSymbol::Add)),
                    b"and" => Ok(Lexeme::Instruction(InstructionSymbol::And)),
                    _ if lexeme_slice.len() > 20 => Err(ParsingError::LabelTooLong(lexeme_slice.len())),
                    _ => Ok(Lexeme::Label(lexeme_slice))
                }
            }
        })
    }
}


// // Assumes " has already been parsed
// fn parse_string(chars: &str) -> Result<(Vec<u8>, usize), ParsingError> {
//     let chars = chars.clone();
//     let mut string = String::new();

//     let num_chars = 0;
//     let mut escaped = false;
//     for char in chars {
//         if !char.is_ascii() {
//             return Err(());
//         }

//         char

//         match char {
//             '\\' if escaped => {
//                     string.push('\\');
//                     escaped = false;
//                 },
//             '\\' if !escaped => {
//                 escaped = true;
//             },
//             '"' if !escaped => {
//                 break
//             }
//             _ => {
//                 string.push(char);
//             }
//         }
//     }

//     return Ok(string);
// }

#[derive(Debug, PartialEq, Eq)]
enum Lexeme<'a> {
    Directive(DirectiveSymbol),
    Immediate(i32),
    Instruction(InstructionSymbol),
    Label(&'a [u8]),
    Register(RegisterNum),
    String(Vec<u8>),
    LineBreak,
}

#[derive(Debug, PartialEq, Eq)]
enum DirectiveSymbol {
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

// impl InstructionSymbol {
//     pub fn from_str(s: &str) -> Result<Self, ()> {
//         Ok(match s.to_ascii_lowercase().as_bytes() {
//             b"add" => Self::Add,
//             b"and" => Self::And,
//             _ => return Err(())

//         })
//     }
// }


#[cfg(test)]
mod tests {
    use super::*;

    fn lex_unwrap(source: &[u8]) -> Vec<Lexeme> {
        Lexer::new(source).map(|x| x.unwrap()).collect()
    }
    

    #[test]
    fn lexes_instruction_symbols() {
        use InstructionSymbol::*;
        assert_eq!(
            lex_unwrap(b"add and and add"),
            vec![
                Lexeme::Instruction(Add),
                Lexeme::Instruction(And),
                Lexeme::Instruction(And),
                Lexeme::Instruction(Add),]
        )
    }
    #[test]
    fn lexes_registers() {
        use InstructionSymbol::*;
        assert_eq!(
            lex_unwrap(b"r0 r1 r2 r3 r4 r5 r6 r7"),
            vec![
                Lexeme::Register(RegisterNum(0)),
                Lexeme::Register(RegisterNum(1)),
                Lexeme::Register(RegisterNum(2)),
                Lexeme::Register(RegisterNum(3)),
                Lexeme::Register(RegisterNum(4)),
                Lexeme::Register(RegisterNum(5)),
                Lexeme::Register(RegisterNum(6)),
                Lexeme::Register(RegisterNum(7))
                ]
        )
    }

     #[test]
    fn lexes_line_break() {
        assert_eq!(
            lex_unwrap(b"  \n \n \n\n \n"),
            vec![
                Lexeme::LineBreak
                ]
        )
    }

    #[test]
    fn lexes_labels() {
        assert_eq!(
            lex_unwrap(b"this is a whole lot of labels"),
            vec![
                Lexeme::Label(b"this"),
                Lexeme::Label(b"is"),
                Lexeme::Label(b"a"),
                Lexeme::Label(b"whole"),
                Lexeme::Label(b"lot"),
                Lexeme::Label(b"of"),
                Lexeme::Label(b"labels")
                ]
        )
    }
}