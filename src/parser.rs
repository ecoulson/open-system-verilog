use std::{error::Error, iter::Peekable};

use crate::{
    lexer::FilePosition,
    punctuation::Punctuation,
    syntax_node::SyntaxNode,
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
    eof_position: FilePosition,
    token_stream: Peekable<TokenStream>,
    errors: Vec<ParseError>,
}

impl<'a> Parser<'a> {
    pub fn new<'b>(file_path: &'b str, token_stream: TokenStream) -> Parser<'b> {
        Parser {
            file_path,
            eof_position: token_stream.eof_position(),
            token_stream: token_stream.peekable(),
            errors: Vec::new(),
        }
    }

    pub fn parse(&mut self) -> Result<SyntaxNode, &Vec<ParseError>> {
        let root: SyntaxNode = self
            .parse_genvar_identifier()
            .unwrap_or_else(|error| self.create_error_node(error));

        if !self.errors.is_empty() {
            return Err(&self.errors);
        }

        return Ok(root);
    }

    fn create_error_node(&mut self, error: ParseError) -> SyntaxNode {
        self.errors.push(error);
        SyntaxNode::build_error()
    }

    fn create_parse_error(&self, message: &'static str, file_position: FilePosition) -> ParseError {
        ParseError::new(message, self.file_path, file_position)
    }

    fn file_position(&mut self) -> FilePosition {
        self.token_stream
            .peek()
            .map_or(self.eof_position, |token| token.position())
    }

    fn parse_genvar_identifier(&mut self) -> Result<SyntaxNode, ParseError> {
        self.parse_identifier()
    }

    fn parse_identifier(&mut self) -> Result<SyntaxNode, ParseError> {
        let file_position = self.file_position();

        if let Ok(token) = self.parse_simple_identifier() {
            return Ok(token);
        }

        if let Ok(token) = self.parse_escaped_identifiers() {
            return Ok(token);
        }

        Err(self.create_parse_error("Expected an identifier", file_position))
    }

    fn parse_simple_identifier(&mut self) -> Result<SyntaxNode, ParseError> {
        let mut identifier = Vec::new();
        let position: FilePosition = self.file_position();

        identifier.push(
            self.read_simple_identifier_beginning_token()?
                .consume_as_string(),
        );

        while let Some(token) = self.read_simple_identifier_token() {
            identifier.push(token.consume_as_string())
        }

        if identifier.len() == 1 && identifier[0] == "" {
            return Err(
                self.create_parse_error("Identifier must not consist of solely an '_'", position)
            );
        }

        Ok(SyntaxNode::build_identifier(identifier.join(""), position))
    }

    fn expect_token<F>(&mut self, constraint: F, message: &'static str) -> Result<Token, ParseError>
    where
        F: FnOnce(&TokenKind) -> bool,
    {
        let file_position = self.file_position();
        self.read_token(constraint)
            .ok_or_else(|| self.create_parse_error(message, file_position))
    }

    fn read_token<F>(&mut self, constraint: F) -> Option<Token>
    where
        F: FnOnce(&TokenKind) -> bool,
    {
        self.token_stream.next_if(|token| constraint(token.kind()))
    }

    fn read_simple_identifier_beginning_token(&mut self) -> Result<Token, ParseError> {
        self.expect_token(
            |kind| match kind {
                TokenKind::CharacterSequence(_)
                | TokenKind::Punctuation(Punctuation::Underscore) => true,
                _ => false,
            },
            "Simple identifier must start with _ or character sequence",
        )
    }

    fn read_simple_identifier_token(&mut self) -> Option<Token> {
        self.read_token(|kind| match kind {
            TokenKind::CharacterSequence(_)
            | TokenKind::Number(_)
            | TokenKind::Punctuation(Punctuation::Underscore)
            | TokenKind::Punctuation(Punctuation::Dollar) => true,
            _ => false,
        })
    }

    fn parse_escaped_identifiers(&mut self) -> Result<SyntaxNode, ParseError> {
        self.expect_token(
            |kind| match kind {
                TokenKind::EscapedIdentifier(_) => true,
                _ => false,
            },
            "Expected an escaped identifier token",
        )
        .map(|token| {
            let position = self.file_position();
            dbg!(&token);
            SyntaxNode::build_identifier(token.consume_as_string(), position)
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        lexer::FilePosition, punctuation::Punctuation, syntax_node::SyntaxNode, token::Token,
        token_stream::TokenStream,
    };

    use super::Parser;

    #[test]
    fn should_parse_identifier() {
        let expected_node =
            SyntaxNode::build_identifier(String::from("abc123$_"), FilePosition::new(1, 1));
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

    #[test]
    fn should_parse_escaped_identifier() {
        let expected_node =
            SyntaxNode::build_identifier(String::from("@+q$"), FilePosition::new(1, 1));
        let tokens = vec![Token::build_escaped_identifier_token(
            String::from("@+q$"),
            FilePosition::new(1, 1),
        )];
        let mut parser = Parser::new("", TokenStream::new(tokens));

        let node = parser
            .parse_escaped_identifiers()
            .expect("Should parse escaped identifiers");

        assert_eq!(node, expected_node)
    }
}
