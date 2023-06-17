use std::iter::Peekable;

use crate::{
    lexer::FilePosition,
    punctuation::Punctuation,
    syntax_node::{IdentifierNode, SyntaxNode},
    token::{Token, TokenKind},
    token_stream::TokenStream,
};

#[derive(Debug)]
struct ParseError {
    message: &'static str,
    file_position: FilePosition,
}

impl ParseError {
    fn new(message: &'static str, file_position: FilePosition) -> ParseError {
        ParseError {
            message,
            file_position,
        }
    }

    fn format_error(&self) -> String {
        format!(
            "error: {}\n--> {}:{}",
            self.message,
            self.file_position.row(),
            self.file_position.column()
        )
    }
}

pub struct Parser {
    token_stream: Peekable<TokenStream>,
    errors: Vec<String>,
}

impl Parser {
    pub fn new(token_stream: TokenStream) -> Parser {
        Parser {
            token_stream: token_stream.peekable(),
            errors: Vec::new(),
        }
    }

    pub fn parse(&mut self) -> Result<SyntaxNode, &Vec<String>> {
        let mut root: Option<SyntaxNode> = None;

        match self.parse_simple_identifier() {
            Err(error) => self.errors.push(error.format_error()),
            Ok(token) => root = Some(token),
        }

        self.next_token().map(|token| match token.consume() {
            TokenKind::EOF => (),
            _ => self.errors.push(String::from("Expected eof")),
        });

        if !self.errors.is_empty() {
            return Err(&self.errors);
        }

        return Ok(root.unwrap());
    }

    fn next_token(&mut self) -> Option<Token> {
        self.token_stream.next()
    }

    fn peek_token(&mut self) -> Option<&Token> {
        self.token_stream.peek()
    }

    fn file_position(&mut self) -> Result<FilePosition, ParseError> {
        self.peek_token()
            .map_or(Err(ParseError::new("", FilePosition::new(0, 0))), |token| {
                Ok(token.position())
            })
    }

    fn is_next_token_character_sequence(&mut self) -> bool {
        self.peek_token().map_or(false, |token| {
            matches!(token.kind(), TokenKind::CharacterSequence(_))
        })
    }

    fn is_next_token_number(&mut self) -> bool {
        self.peek_token()
            .map_or(false, |token| matches!(token.kind(), TokenKind::Number(_)))
    }

    fn is_next_token_punctuation(&mut self, punctuation: Punctuation) -> bool {
        self.peek_token().map_or(false, |token| match token.kind() {
            TokenKind::Punctuation(value) => value == &punctuation,
            _ => false,
        })
    }

    fn parse_simple_identifier(&mut self) -> Result<SyntaxNode, ParseError> {
        let mut identifier = Vec::new();
        let position: FilePosition = self.file_position()?;

        if self.can_read_simple_identifier_beginning_token() {
            let character_sequence = self.consume_next_token_as_string().unwrap();

            identifier.push(character_sequence);
        } else {
            return Err(ParseError::new(
                "Identifier must start with _ or character sequence",
                FilePosition::new(1, 1),
            ));
        }

        while self.can_read_simple_identifier_token() {
            if let Some(part) = self.consume_next_token_as_string() {
                identifier.push(part);
            }
        }

        let identifier = identifier.join("");

        if identifier == "_" {
            return Err(ParseError::new(
                "Identifier must not consist of solely an '_'",
                position,
            ));
        }

        Ok(IdentifierNode::new(identifier, position))
    }

    fn can_read_simple_identifier_beginning_token(&mut self) -> bool {
        self.is_next_token_character_sequence()
            || self.is_next_token_punctuation(Punctuation::Underscore)
    }

    fn can_read_simple_identifier_token(&mut self) -> bool {
        self.is_next_token_character_sequence()
            || self.is_next_token_number()
            || self.is_next_token_punctuation(Punctuation::Dollar)
            || self.is_next_token_punctuation(Punctuation::Underscore)
    }

    fn consume_next_token_as_string(&mut self) -> Option<String> {
        self.next_token()
            .map_or(None, |token| match token.consume() {
                TokenKind::CharacterSequence(string) | TokenKind::Number(string) => Some(string),
                TokenKind::Punctuation(punctuation) => Some(punctuation.to_string()),
                _ => None,
            })
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
        let mut parser = Parser::new(TokenStream::new(tokens));

        let node = parser
            .parse_simple_identifier()
            .expect("Should not be none");

        assert_eq!(node, expected_node);
    }
}
