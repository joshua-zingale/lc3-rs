use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location {
    pub line: usize,
    pub column: usize,
    pub offset: usize,
}



impl Location {
    pub fn advance(&mut self, char: char) {
        if char == '\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }

        self.offset += char.len_utf8();
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
    ImmediateOutOfRange(u32, i32, bool),
    InvalidCharacterInLabel,
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
            ImmediateOutOfRange(num_bits, attempted_number, signed) => write!(f, "the number {} does not fit into a(n) {} immediate value of {}-bits", attempted_number, if *signed {"signed"} else {"unsigned"}, num_bits),
            InvalidCharacterInLabel => write!(f, "invalid character in label: labels must only contain ASCII letters and numbers and start with a letter")
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NumberOutOfRangeError {
    pub bits: u32,
    pub attempted_num: i32,
    pub signed: bool
}


impl fmt::Display for NumberOutOfRangeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
         write!(f, "{} is out of range for a {} {}-bit number", self.attempted_num, if self.signed {"signed"} else {"unsigned"}, self.bits)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NBitInt<const BITS: u32, const SIGNED: bool>(i32);

impl<const BITS: u32, const SIGNED: bool> NBitInt<BITS, SIGNED> {
    pub fn new(v: i32) -> Result<Self, NumberOutOfRangeError> {
        {
            let min = if SIGNED { -(1 << (BITS - 1)) } else { 0 };
            let max = if SIGNED {
                (1 << (BITS - 1)) - 1
            } else {
                (1 << BITS) - 1
            };

            if v < min || v > max {
                return Err(NumberOutOfRangeError {
                    bits: BITS,
                    attempted_num: v,
                    signed: SIGNED,
                });
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

    pub fn increment(&mut self, v: i32) -> Result<(), NumberOutOfRangeError> {
        Ok(self.0 = Self::new(self.get() + v)?.get())
    }

    // Returns the N-bit representation as a u16 with 0's prepended for the first 16-N bits
    pub fn get_truncated_u16(&self) -> u16 {
        assert!(BITS <= 16);
        let mask = (1 << BITS) - 1; 
        (self.0 & mask) as u16
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
pub type Imm6 = NBitInt<6, true>;
pub type Imm9 = NBitInt<9, true>;
pub type Imm11 = NBitInt<11, true>;

pub type TrapVec = NBitInt<8, false>;

pub type RegisterNum = NBitInt<3, false>;


pub type Address = NBitInt<16, false>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Either<A, B> {
    A(A),
    B(B),
}