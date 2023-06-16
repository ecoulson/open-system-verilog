use std::iter::Peekable;

use crate::{
    lexer::FilePosition,
    punctuation::Punctuation,
    syntax_node::{IdentifierNode, SyntaxNode},
    token::{Token, TokenStruct},
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

        if let Some(token) = self.next_token() {
            match token.consume() {
                Token::EOF => (),
                _ => self.errors.push(String::from("Expected eof")),
            };
        }

        if !self.errors.is_empty() {
            return Err(&self.errors);
        }

        return Ok(root.unwrap());
    }

    fn next_token(&mut self) -> Option<TokenStruct> {
        self.token_stream.next()
    }

    fn peek_token(&mut self) -> Option<&TokenStruct> {
        self.token_stream.peek()
    }

    fn file_position(&mut self) -> Result<FilePosition, ParseError> {
        if let Some(token) = self.peek_token() {
            return Ok(token.position());
        }

        Err(ParseError::new("", FilePosition::new(0, 0)))
    }

    fn is_next_token_character_sequence(&mut self) -> bool {
        if let Some(token) = self.peek_token() {
            match token.kind() {
                Token::CharacterSequence(_) => true,
                _ => false,
            }
        } else {
            false
        }
    }

    fn is_next_token_number(&mut self) -> bool {
        if let Some(token) = self.peek_token() {
            match token.kind() {
                Token::Number(_) => true,
                _ => false,
            }
        } else {
            false
        }
    }

    fn is_next_token_punctuation(&mut self, punctuation: Punctuation) -> bool {
        if let Some(token) = self.peek_token() {
            match token.kind() {
                Token::Punctuation(other) => other == &punctuation,
                _ => false,
            }
        } else {
            false
        }
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
        if let Some(token) = self.next_token() {
            match token.consume() {
                Token::CharacterSequence(string) | Token::Number(string) => Some(string),
                Token::Punctuation(token) => Some(Parser::parse_punctuation(token)),
                _ => None,
            }
        } else {
            None
        }
    }

    fn parse_punctuation(punctuation: Punctuation) -> String {
        String::from(match punctuation {
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

#[cfg(test)]
mod tests {
    use crate::{
        lexer::FilePosition,
        punctuation::Punctuation,
        syntax_node::IdentifierNode,
        token::{BuildToken, CharacterSequenceToken, NumberToken, PunctuationToken},
        token_stream::TokenStream,
    };

    use super::Parser;

    #[test]
    fn should_parse_identifier() {
        let expected_node = IdentifierNode::new(String::from("abc123$_"), FilePosition::new(1, 1));
        let tokens = vec![
            CharacterSequenceToken::build_token(String::from("abc"), FilePosition::new(1, 1)),
            NumberToken::build_token(String::from("123"), FilePosition::new(1, 1)),
            PunctuationToken::build_token(Punctuation::Dollar, FilePosition::new(1, 1)),
            PunctuationToken::build_token(Punctuation::Underscore, FilePosition::new(1, 1)),
        ];
        let mut parser = Parser::new(TokenStream::new(tokens));

        let node = parser
            .parse_simple_identifier()
            .expect("Should not be none");

        assert_eq!(node, expected_node);
    }
}
