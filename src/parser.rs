use std::{error::Error, iter::Peekable};

use crate::{
    lexer::FilePosition,
    punctuation::Punctuation,
    syntax_node::{IdentifierNode, SyntaxNode},
    token::{Token, TokenKind},
    token_stream::TokenStream,
};

#[derive(Debug)]
pub struct ParseError(String);

impl Error for ParseError {}

impl ParseError {
    fn new(message: &'static str, file_path: &str, file_position: FilePosition) -> ParseError {
        ParseError(format!(
            "error: {}\n-->{}:{}:{}",
            message,
            file_path,
            file_position.row(),
            file_position.column()
        ))
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub struct Parser<'a> {
    file_path: &'a str,
    token_stream: Peekable<TokenStream>,
    errors: Vec<ParseError>,
}

impl<'a> Parser<'a> {
    pub fn new<'b>(file_path: &'b str, token_stream: TokenStream) -> Parser<'b> {
        Parser {
            file_path,
            token_stream: token_stream.peekable(),
            errors: Vec::new(),
        }
    }

    pub fn parse(&mut self) -> Result<SyntaxNode, &Vec<ParseError>> {
        let root: SyntaxNode = self
            .parse_simple_identifier()
            .unwrap_or_else(|error| self.create_error_node(error));

        self.token_stream.next().map(|token| {
            let file_position = token.position();
            match token.consume() {
                TokenKind::EOF => SyntaxNode::EOF,
                _ => self.create_error_node_from_message("Expected EOF", file_position),
            }
        });

        if !self.errors.is_empty() {
            return Err(&self.errors);
        }

        return Ok(root);
    }

    fn create_error_node(&mut self, error: ParseError) -> SyntaxNode {
        self.errors.push(error);
        SyntaxNode::Error
    }

    fn create_error_node_from_message(
        &mut self,
        message: &'static str,
        file_position: FilePosition,
    ) -> SyntaxNode {
        self.errors
            .push(self.create_parse_error(message, file_position));
        SyntaxNode::Error
    }

    fn create_parse_error(&self, message: &'static str, file_position: FilePosition) -> ParseError {
        ParseError::new(message, self.file_path, file_position)
    }

    fn file_position(&mut self) -> Option<FilePosition> {
        self.token_stream.peek().map(|token| token.position())
    }

    fn parse_simple_identifier(&mut self) -> Result<SyntaxNode, ParseError> {
        let mut identifier = Vec::new();
        let position: FilePosition = self.file_position().unwrap();

        identifier.push(
            self.read_simple_identifier_beginning_token()?
                .consume_as_string(),
        );

        while let Some(token) = self.read_simple_identifier_token() {
            identifier.push(token.consume_as_string())
        }

        let identifier = identifier.join("");

        if identifier == "_" {
            return Err(
                self.create_parse_error("Identifier must not consist of solely an '_'", position)
            );
        }

        Ok(IdentifierNode::new(identifier, position))
    }

    fn read_simple_identifier_beginning_token(&mut self) -> Result<Token, ParseError> {
        let position: FilePosition = self.file_position().unwrap();
        self.token_stream
            .next()
            .and_then(|token| match token.kind() {
                TokenKind::CharacterSequence(_)
                | TokenKind::Punctuation(Punctuation::Underscore) => Some(token),
                _ => None,
            })
            .ok_or_else(|| {
                self.create_parse_error(
                    "Identifier must start with _ or character sequence",
                    position,
                )
            })
    }

    fn read_simple_identifier_token(&mut self) -> Option<Token> {
        if let Some(token) = self.token_stream.peek() {
            return match token.kind() {
                TokenKind::CharacterSequence(_)
                | TokenKind::Number(_)
                | TokenKind::Punctuation(Punctuation::Dollar)
                | TokenKind::Punctuation(Punctuation::Underscore) => self.token_stream.next(),
                _ => None,
            };
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        lexer::FilePosition, punctuation::Punctuation, syntax_node::IdentifierNode, token::Token,
        token_stream::TokenStream,
    };

    use super::Parser;

    #[test]
    fn should_parse_identifier() {
        let expected_node = IdentifierNode::new(String::from("abc123$_"), FilePosition::new(1, 1));
        let tokens = vec![
            Token::build_character_sequence_token(String::from("abc"), FilePosition::new(1, 1)),
            Token::build_number_token(String::from("123"), FilePosition::new(1, 1)),
            Token::build_punctuation_token(Punctuation::Dollar, FilePosition::new(1, 1)),
            Token::build_punctuation_token(Punctuation::Underscore, FilePosition::new(1, 1)),
        ];
        let mut parser = Parser::new("", TokenStream::new(tokens));

        let node = parser
            .parse_simple_identifier()
            .expect("Should not be none");

        assert_eq!(node, expected_node);
    }
}
