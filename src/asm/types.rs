use core::fmt;

#[derive(Debug, Clone)]
struct InvalidNBitNumber(i32);

impl fmt::Display for InvalidNBitNumber {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "number must be {}-bit", self.0)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct RegisterNum(pub u8);

// impl RegisterNum {
//     pub fn new(value: u8) -> Result<RegisterNum, InvalidNBitNumber> {
//         if value >> 4 != 0 {
//             Err(InvalidNBitNumber(4))
//         } else {
//             Ok(RegisterNum(value))
//         }
//     }
// }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location {
    pub line: usize,
    pub column: usize,
    pub offset: usize,
}

impl Location {
    pub fn advance(&mut self, char: u8) {
        if char == b'\n' {
            self.advance_line();
        } else {
            self.advance_char();
        }
    }
    pub fn advance_char(&mut self) {
        self.column += 1;
        self.offset += 1;
    }
    pub fn advance_line(&mut self) {
        self.line += 1;
        self.column = 1;
        self.offset += 1;
    }
}



#[derive(Debug, Clone)]
pub enum ParsingError {
    NonAsciiCharacter(char),
    LabelTooLong(usize)
}

impl fmt::Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ParsingError::*;
        match self {
            NonAsciiCharacter(c) => write!(f, "invalid ASCII character \"{}\"", c),
            LabelTooLong(length) => write!(f, "label must be 20 characters or less, but is {} characters long", length)
        }
        
    }
}