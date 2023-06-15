use std::iter::Peekable;

use crate::{
    lexer::FilePosition,
    punctuation::Punctuation,
    syntax_node::{IdentifierNode, SyntaxNode},
    token::{Consume, Token},
    token_stream::TokenStream,
};

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
            Err(message) => self.errors.push(message),
            Ok(token) => root = Some(token),
        }

        match self.next_token() {
            Some(Token::EOF(_)) => (),
            _ => self.errors.push(String::from("Expected eof")),
        };

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

    fn is_next_token_character_sequence(&mut self) -> bool {
        match self.peek_token() {
            Some(Token::CharacterSequence(_)) => true,
            _ => false,
        }
    }

    fn is_next_token_number(&mut self) -> bool {
        match self.peek_token() {
            Some(Token::Number(_)) => true,
            _ => false,
        }
    }

    fn is_next_token_punctuation(&mut self, punctuation: Punctuation) -> bool {
        match self.peek_token() {
            Some(Token::Punctuation(token)) => token.punctuation() == &punctuation,
            _ => false,
        }
    }

    fn parse_simple_identifier(&mut self) -> Result<SyntaxNode, String> {
        let mut identifier = Vec::new();
        let position: Option<FilePosition>;

        if self.can_read_simple_identifier_beginning_token() {
            let (character_sequence, file_position) = self.consume_next_token_as_string().unwrap();

            position = Some(file_position);
            identifier.push(character_sequence);
        } else {
            return Err(String::from(
                "Identifier must start with _ or character sequence",
            ));
        }

        while self.can_read_simple_identifier_token() {
            if let Some((part, _)) = self.consume_next_token_as_string() {
                identifier.push(part);
            }
        }

        Ok(IdentifierNode::new(identifier.join(""), position.unwrap()))
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

    fn consume_next_token_as_string(&mut self) -> Option<(String, FilePosition)> {
        match self.next_token() {
            Some(Token::CharacterSequence(token)) => Some(token.consume()),
            Some(Token::Number(token)) => Some(token.consume()),
            Some(Token::Punctuation(token)) => {
                let (punctuation, position) = token.consume();
                Some((Parser::parse_punctuation(punctuation), position))
            }
            _ => None,
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
