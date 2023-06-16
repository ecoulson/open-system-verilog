use std::collections::VecDeque;

use crate::token::{Token, TokenStruct};

#[derive(Debug)]
pub struct TokenStream {
    tokens: VecDeque<TokenStruct>,
}

impl TokenStream {
    pub fn new(tokens: Vec<Token>) -> TokenStream {
        TokenStream {
            tokens: VecDeque::from(
                tokens
                    .into_iter()
                    .map(|token| TokenStruct::new(token))
                    .collect::<Vec<TokenStruct>>(),
            ),
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
    use crate::token::{
        BuildToken, CharacterSequenceToken, NumberToken, StringLiteralToken, Token, TokenStruct,
    };

    use super::TokenStream;

    #[test]
    fn should_iterate_over_token_stream() {
        let expected_tokens = vec![
            TokenStruct::new(NumberToken::build_token(
                String::from("123"),
                FilePosition::new(1, 1),
            )),
            TokenStruct::new(StringLiteralToken::build_token(
                String::from("foo"),
                FilePosition::new(1, 1),
            )),
            TokenStruct::new(CharacterSequenceToken::build_token(
                String::from("abc"),
                FilePosition::new(1, 1),
            )),
            TokenStruct::new(Token::EOF(FilePosition::new(1, 1))),
        ];

        let mut token_stream = TokenStream::new(vec![
            NumberToken::build_token(String::from("123"), FilePosition::new(1, 1)),
            StringLiteralToken::build_token(String::from("foo"), FilePosition::new(1, 1)),
            CharacterSequenceToken::build_token(String::from("abc"), FilePosition::new(1, 1)),
            Token::EOF(FilePosition::new(1, 1)),
        ]);

        assert_eq!(token_stream.next().unwrap(), expected_tokens[0]);
        assert_eq!(token_stream.next().unwrap(), expected_tokens[1]);
        assert_eq!(token_stream.next().unwrap(), expected_tokens[2]);
        assert_eq!(token_stream.next().unwrap(), expected_tokens[3]);
        assert!(token_stream.next().is_none());
    }
}
