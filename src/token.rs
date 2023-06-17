use crate::keywords::Keyword;
use crate::lexer::FilePosition;
use crate::operators::Operator;
use crate::punctuation::Punctuation;

#[derive(Debug, PartialEq, Eq)]
pub enum TokenKind {
    WhiteSpace,
    Comment,
    Number(String),
    StringLiteral(String),
    CharacterSequence(String),
    Operator(Operator),
    Punctuation(Punctuation),
    Keyword(Keyword),
    EscapedIdentifier(String),
    Error(&'static str),
    EOF,
}

pub trait TokenFromSequence {
    fn from_sequence(sequence: &str, position: FilePosition) -> Result<Token, &'static str>;
}

#[derive(Debug, PartialEq, Eq)]
pub struct Token {
    kind: TokenKind,
    file_position: FilePosition,
}

impl Token {
    pub fn new(kind: TokenKind, file_position: FilePosition) -> Token {
        Token {
            kind,
            file_position,
        }
    }

    pub fn build_eof_token(file_position: FilePosition) -> Token {
        Token::new(TokenKind::EOF, file_position)
    }

    pub fn build_white_space_token(file_position: FilePosition) -> Token {
        Token::new(TokenKind::WhiteSpace, file_position)
    }

    pub fn build_comment_token(file_position: FilePosition) -> Token {
        Token::new(TokenKind::Comment, file_position)
    }

    pub fn build_number_token(number: String, file_position: FilePosition) -> Token {
        Token::new(TokenKind::Number(number), file_position)
    }

    pub fn build_string_literal_token(
        string_literal: String,
        file_position: FilePosition,
    ) -> Token {
        Token::new(TokenKind::StringLiteral(string_literal), file_position)
    }

    pub fn build_character_sequence_token(
        character_sequence: String,
        file_position: FilePosition,
    ) -> Token {
        Token::new(TokenKind::CharacterSequence(character_sequence), file_position)
    }

    pub fn build_escaped_identifier_token(
        escaped_identifier: String,
        file_position: FilePosition,
    ) -> Token {
        Token::new(TokenKind::CharacterSequence(escaped_identifier), file_position)
    }

    pub fn build_operator_token(operator: Operator, file_position: FilePosition) -> Token {
        Token::new(TokenKind::Operator(operator), file_position)
    }

    pub fn build_keyword_token(keyword: Keyword, file_position: FilePosition) -> Token {
        Token::new(TokenKind::Keyword(keyword), file_position)
    }

    pub fn build_punctuation_token(
        punctuation: Punctuation,
        file_position: FilePosition,
    ) -> Token {
        Token::new(TokenKind::Punctuation(punctuation), file_position)
    }

    pub fn build_error_token(error: &'static str, file_position: FilePosition) -> Token {
        Token::new(TokenKind::Error(error), file_position)
    }

    pub fn position(&self) -> FilePosition {
        self.file_position.clone()
    }

    pub fn kind(&self) -> &TokenKind {
        &self.kind
    }

    pub fn consume(self) -> TokenKind {
        self.kind
    }
}
