use std::collections::VecDeque;

use crate::{token::Token, lexer::FilePosition};

#[derive(Debug)]
pub struct TokenStream {
    tokens: VecDeque<Token>,
}

impl TokenStream {
    pub fn new(tokens: Vec<Token>) -> TokenStream {
        TokenStream {
            tokens: VecDeque::from(tokens),
        }
    }

    pub fn eof_position(&self) -> FilePosition {
        self.tokens.back().map_or(FilePosition::new(1, 1), |token| token.position())
    }
}

impl Iterator for TokenStream {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.tokens.pop_front()
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::FilePosition;
    use crate::token::Token;

    use super::TokenStream;

    #[test]
    fn should_iterate_over_token_stream() {
        let expected_tokens = vec![
            Token::build_number_token(String::from("123"), FilePosition::new(1, 1)),
            Token::build_string_literal_token(String::from("foo"), FilePosition::new(1, 1)),
            Token::build_character_sequence_token(
                String::from("abc"),
                FilePosition::new(1, 1),
            ),
            Token::build_eof_token(FilePosition::new(1, 1)),
        ];

        let mut token_stream = TokenStream::new(vec![
            Token::build_number_token(String::from("123"), FilePosition::new(1, 1)),
            Token::build_string_literal_token(String::from("foo"), FilePosition::new(1, 1)),
            Token::build_character_sequence_token(
                String::from("abc"),
                FilePosition::new(1, 1),
            ),
            Token::build_eof_token(FilePosition::new(1, 1)),
        ]);

        assert_eq!(token_stream.next().unwrap(), expected_tokens[0]);
        assert_eq!(token_stream.next().unwrap(), expected_tokens[1]);
        assert_eq!(token_stream.next().unwrap(), expected_tokens[2]);
        assert_eq!(token_stream.next().unwrap(), expected_tokens[3]);
        assert!(token_stream.next().is_none());
    }
}
