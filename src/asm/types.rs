use std::fmt;

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

impl Default for Location {
    fn default() -> Self {
        Location { line: 1, column: 1, offset: 0 }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsingError {
    pub kind: ParsingErrorKind,
    pub start: Location,
    pub end: Location,
}

impl fmt::Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "line {} column {}: {}", self.start.line, self.start.column, self.kind)
    }
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParsingErrorKind {
    NonAsciiCharacter(char),
    LabelTooLong(usize),
    InvalidDecimalNumber(String),
    InvalidDirective(String),
    ExpectedButFound(String, String),
    SignedNumberOutOfRange(u32, i32),
    UnsignedNumberOutOfRange(u32, i32),
}

impl fmt::Display for ParsingErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ParsingErrorKind::*;
        match self {
            NonAsciiCharacter(c) => write!(f, "invalid ASCII character \"{}\"", c),
            LabelTooLong(length) => write!(f, "label must be 20 characters or less, but is {} characters long", length),
            InvalidDecimalNumber(invalid_number) => write!(f, "invalid decimal number: {}", invalid_number),
            InvalidDirective(invalid_directive) => write!(f, "invalid directive: {}", invalid_directive),
            ExpectedButFound(expectation, finding) => write!(f, "expected {} but found {}", expectation, finding),
            SignedNumberOutOfRange(maximum_bits, received_nuber) => write!(f, "{} is not a valid {}-bit signed number", received_nuber, maximum_bits),
            UnsignedNumberOutOfRange(maximum_bits, received_nuber) => write!(f, "{} is not a valid {}-bit usigned number", received_nuber, maximum_bits),
        }
        
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NBitInt<const BITS: u32, const SIGNED: bool>(i32);

impl<const BITS: u32, const SIGNED: bool> NBitInt<BITS, SIGNED> {
    pub fn new(v: i32) -> Result<Self, ParsingErrorKind> {
        {
            let min = if SIGNED { -(1 << (BITS - 1)) } else { 0 };
            let max = if SIGNED {
                (1 << (BITS - 1)) - 1
            } else {
                (1 << BITS) - 1
            };

            if v < min || v > max {
                if SIGNED {
                    return Err(ParsingErrorKind::SignedNumberOutOfRange(BITS, v));
                } else {
                    return Err(ParsingErrorKind::UnsignedNumberOutOfRange(BITS, v));
                }
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

    pub fn increment(&mut self, v: i32) -> Result<(), ParsingErrorKind> {
        Ok(self.0 = Self::new(self.get() + v)?.get())
    }

    pub fn get_u16(&self) -> u16 {
        assert!(BITS <= 16);
        self.0 as u16
    }

    pub fn get(&self) -> i32 {
        self.0
    }

    pub fn get_max_u16() -> u16 {
        assert!(BITS - (if SIGNED {1} else {0}) <= 15);
        (1 << (BITS - (if SIGNED {1} else {0}))) - 1
    }
}


pub type Imm5 = NBitInt<5, true>;

pub type RegisterNum = NBitInt<3, false>;

pub type Address = NBitInt<16, false>;

pub enum Either<A, B> {
    A(A),
    B(B),
}
