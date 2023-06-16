use std::collections::VecDeque;

use crate::token::TokenStruct;

#[derive(Debug)]
pub struct TokenStream {
    tokens: VecDeque<TokenStruct>,
}

impl TokenStream {
    pub fn new(tokens: Vec<TokenStruct>) -> TokenStream {
        TokenStream {
            tokens: VecDeque::from(tokens),
        }
    }
}

impl Iterator for TokenStream {
    type Item = TokenStruct;

    fn next(&mut self) -> Option<Self::Item> {
        self.tokens.pop_front()
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::FilePosition;
    use crate::token::TokenStruct;

    use super::TokenStream;

    #[test]
    fn should_iterate_over_token_stream() {
        let expected_tokens = vec![
            TokenStruct::build_number_token(String::from("123"), FilePosition::new(1, 1)),
            TokenStruct::build_string_literal_token(String::from("foo"), FilePosition::new(1, 1)),
            TokenStruct::build_character_sequence_token(
                String::from("abc"),
                FilePosition::new(1, 1),
            ),
            TokenStruct::build_eof_token(FilePosition::new(1, 1)),
        ];

        let mut token_stream = TokenStream::new(vec![
            TokenStruct::build_number_token(String::from("123"), FilePosition::new(1, 1)),
            TokenStruct::build_string_literal_token(String::from("foo"), FilePosition::new(1, 1)),
            TokenStruct::build_character_sequence_token(
                String::from("abc"),
                FilePosition::new(1, 1),
            ),
            TokenStruct::build_eof_token(FilePosition::new(1, 1)),
        ]);

        assert_eq!(token_stream.next().unwrap(), expected_tokens[0]);
        assert_eq!(token_stream.next().unwrap(), expected_tokens[1]);
        assert_eq!(token_stream.next().unwrap(), expected_tokens[2]);
        assert_eq!(token_stream.next().unwrap(), expected_tokens[3]);
        assert!(token_stream.next().is_none());
    }
}
