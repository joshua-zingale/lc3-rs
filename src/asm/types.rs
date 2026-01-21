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
        Location {
            line: 1,
            column: 1,
            offset: 0,
        }
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
        write!(
            f,
            "line {} column {}: {}",
            self.start.line, self.start.column, self.kind
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParsingErrorKind {
    NonAsciiCharacter(char),
    UnterminatedStringLiteral,
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
            UnterminatedStringLiteral => write!(
                f,
                "unterminated string literal: there should be a '\"' at the end of the line"
            ),
            LabelTooLong(length) => write!(
                f,
                "label must be 20 characters or less, but is {} characters long",
                length
            ),
            InvalidDecimalNumber(invalid_number) => {
                write!(f, "invalid decimal number: {}", invalid_number)
            }
            InvalidDirective(invalid_directive) => {
                write!(f, "invalid directive: {}", invalid_directive)
            }
            ExpectedButFound(expectation, finding) => {
                write!(f, "expected {} but found {}", expectation, finding)
            }
            ImmediateOutOfRange(num_bits, attempted_number, signed) => write!(
                f,
                "the number {} does not fit into a(n) {} immediate value of {}-bits",
                attempted_number,
                if *signed { "signed" } else { "unsigned" },
                num_bits
            ),
            InvalidCharacterInLabel => write!(
                f,
                "invalid character in label: labels must only contain ASCII letters and numbers and start with a letter"
            ),
        }
    }
}
