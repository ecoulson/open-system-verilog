use crate::{lexer::FilePosition, token::Token};

#[derive(Debug, PartialEq, Eq)]
pub enum Punctuation {
    Asperand,
    Pound,
    Dollar,
    LeftParentheses,
    RightParentheses,
    RightBracket,
    LeftBracket,
    RightBrace,
    LeftBrace,
    BackSlash,
    Semicolon,
    Colon,
    QuestionMark,
    Backtick,
    Period,
    Comma,
    Apostrophe,
    Underscore,
}

impl Punctuation {
    pub fn from_char(ch: char, file_position: FilePosition) -> Result<Token, &'static str> {
        match ch {
            '@' => Ok(Token::build_punctuation_token(
                Punctuation::Asperand,
                file_position,
            )),
            '#' => Ok(Token::build_punctuation_token(
                Punctuation::Pound,
                file_position,
            )),
            '$' => Ok(Token::build_punctuation_token(
                Punctuation::Dollar,
                file_position,
            )),
            '(' => Ok(Token::build_punctuation_token(
                Punctuation::LeftParentheses,
                file_position,
            )),
            ')' => Ok(Token::build_punctuation_token(
                Punctuation::RightParentheses,
                file_position,
            )),
            '[' => Ok(Token::build_punctuation_token(
                Punctuation::LeftBracket,
                file_position,
            )),
            ']' => Ok(Token::build_punctuation_token(
                Punctuation::RightBracket,
                file_position,
            )),
            '{' => Ok(Token::build_punctuation_token(
                Punctuation::LeftBrace,
                file_position,
            )),
            '}' => Ok(Token::build_punctuation_token(
                Punctuation::RightBrace,
                file_position,
            )),
            '\\' => Ok(Token::build_punctuation_token(
                Punctuation::BackSlash,
                file_position,
            )),
            ';' => Ok(Token::build_punctuation_token(
                Punctuation::Semicolon,
                file_position,
            )),
            ':' => Ok(Token::build_punctuation_token(
                Punctuation::Colon,
                file_position,
            )),
            '?' => Ok(Token::build_punctuation_token(
                Punctuation::QuestionMark,
                file_position,
            )),
            '`' => Ok(Token::build_punctuation_token(
                Punctuation::Backtick,
                file_position,
            )),
            '.' => Ok(Token::build_punctuation_token(
                Punctuation::Period,
                file_position,
            )),
            ',' => Ok(Token::build_punctuation_token(
                Punctuation::Comma,
                file_position,
            )),
            '\'' => Ok(Token::build_punctuation_token(
                Punctuation::Apostrophe,
                file_position,
            )),
            '_' => Ok(Token::build_punctuation_token(
                Punctuation::Underscore,
                file_position,
            )),
            _ => Err("Unrecognized punctuation mark"),
        }
    }

    pub fn to_string(&self) -> String {
        String::from(match self {
            Punctuation::Dollar => "$",
            Punctuation::Pound => "#",
            Punctuation::Colon => ":",
            Punctuation::Comma => ",",
            Punctuation::Period => ".",
            Punctuation::Asperand => "@",
            Punctuation::Backtick => "`",
            Punctuation::LeftBrace => "{",
            Punctuation::BackSlash => "\\",
            Punctuation::Semicolon => ";",
            Punctuation::RightBrace => "}",
            Punctuation::Apostrophe => "'",
            Punctuation::Underscore => "_",
            Punctuation::LeftBracket => "[",
            Punctuation::RightBracket => "]",
            Punctuation::QuestionMark => "?",
            Punctuation::LeftParentheses => "(",
            Punctuation::RightParentheses => ")",
        })
    }
}
