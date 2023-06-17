use crate::keywords::Keyword;
use crate::lexer::FilePosition;
use crate::operators::Operator;
use crate::punctuation::Punctuation;

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
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
    fn from_sequence(sequence: &str, position: FilePosition) -> Result<TokenStruct, &'static str>;
}

#[derive(Debug, PartialEq, Eq)]
pub struct TokenStruct {
    kind: Token,
    file_position: FilePosition,
}

impl TokenStruct {
    pub fn new(kind: Token, file_position: FilePosition) -> TokenStruct {
        TokenStruct {
            kind,
            file_position,
        }
    }

    pub fn build_eof_token(file_position: FilePosition) -> TokenStruct {
        TokenStruct::new(Token::EOF, file_position)
    }

    pub fn build_white_space_token(file_position: FilePosition) -> TokenStruct {
        TokenStruct::new(Token::WhiteSpace, file_position)
    }

    pub fn build_comment_token(file_position: FilePosition) -> TokenStruct {
        TokenStruct::new(Token::Comment, file_position)
    }

    pub fn build_number_token(number: String, file_position: FilePosition) -> TokenStruct {
        TokenStruct::new(Token::Number(number), file_position)
    }

    pub fn build_string_literal_token(
        string_literal: String,
        file_position: FilePosition,
    ) -> TokenStruct {
        TokenStruct::new(Token::StringLiteral(string_literal), file_position)
    }

    pub fn build_character_sequence_token(
        character_sequence: String,
        file_position: FilePosition,
    ) -> TokenStruct {
        TokenStruct::new(Token::CharacterSequence(character_sequence), file_position)
    }

    pub fn build_escaped_identifier_token(
        escaped_identifier: String,
        file_position: FilePosition,
    ) -> TokenStruct {
        TokenStruct::new(Token::CharacterSequence(escaped_identifier), file_position)
    }

    pub fn build_operator_token(operator: Operator, file_position: FilePosition) -> TokenStruct {
        TokenStruct::new(Token::Operator(operator), file_position)
    }

    pub fn build_keyword_token(keyword: Keyword, file_position: FilePosition) -> TokenStruct {
        TokenStruct::new(Token::Keyword(keyword), file_position)
    }

    pub fn build_punctuation_token(
        punctuation: Punctuation,
        file_position: FilePosition,
    ) -> TokenStruct {
        TokenStruct::new(Token::Punctuation(punctuation), file_position)
    }

    pub fn build_error_token(error: &'static str, file_position: FilePosition) -> TokenStruct {
        TokenStruct::new(Token::Error(error), file_position)
    }

    pub fn position(&self) -> FilePosition {
        self.file_position.clone()
    }

    pub fn kind(&self) -> &Token {
        &self.kind
    }

    pub fn consume(self) -> Token {
        self.kind
    }

    pub fn as_code(&self) -> String {
        match self.kind() {
            Token::EOF => format!(
                "TokenStruct::build_eof_token(FilePosition::new({}, {})),",
                self.file_position.row(),
                self.file_position.column()
            ),
            Token::WhiteSpace => format!(
                "TokenStruct::build_white_space_token(FilePosition::new({}, {})),",
                self.file_position.row(),
                self.file_position.column()
            ),
            Token::Comment => format!(
                "TokenStruct::build_comment_token(FilePosition::new({}, {})),",
                self.file_position.row(),
                self.file_position.column()
            ),
            Token::Error(error) => format!(
                "TokenStruct::build_error_token(String::from(\"{}\"), FilePosition::new({}, {})),",
                error,
                self.file_position.row(),
                self.file_position.column()
            ),
            Token::Number(number) => format!(
                "TokenStruct::build_number_token(String::from(\"{}\"), FilePosition::new({}, {})),",
                number,
                self.file_position.row(),
                self.file_position.column()
            ),
            Token::StringLiteral(string_literal) => format!(
                "TokenStruct::build_string_literal_token(String::from(\"{}\"), FilePosition::new({}, {})),",
                string_literal,
                self.file_position.row(),
                self.file_position.column()
            ),
            Token::CharacterSequence(character_sequence) => format!(
                "TokenStruct::build_character_sequence_token(String::from(\"{}\"), FilePosition::new({}, {})),",
                character_sequence,
                self.file_position.row(),
                self.file_position.column()
            ),
            Token::EscapedIdentifier(escaped_identifier) => format!(
                "TokenStruct::build_escaped_identifier_token(String::from(\"{}\"), FilePosition::new({}, {})),",
                escaped_identifier,
                self.file_position.row(),
                self.file_position.column()
            ),
            Token::Operator(operator) => format!(
                "TokenStruct::build_operator_token(Operator::{:?}, FilePosition::new({}, {})),",
                operator,
                self.file_position.row(),
                self.file_position.column()
            ),
            Token::Keyword(keyword) => format!(
                "TokenStruct::build_keyword_token(Keyword::{:?}, FilePosition::new({}, {})),",
                keyword,
                self.file_position.row(),
                self.file_position.column()
            ),
            Token::Punctuation(punctuation) => format!(
                "TokenStruct::build_punctuation_token(Punctuation::{:?}, FilePosition::new({}, {})),",
                punctuation,
                self.file_position.row(),
                self.file_position.column()
            ),

        }
    }
}
