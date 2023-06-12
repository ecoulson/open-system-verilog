use crate::token::Token;

#[derive(Debug)]
pub struct TokenStream {
    tokens: Vec<Token>,
}

impl TokenStream {
    pub fn new(tokens: Vec<Token>) -> TokenStream {
        TokenStream {
            tokens,
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &Token> + '_ {
        self.tokens.iter()
    }
}

#[cfg(test)]
mod tests {
    use crate::token::{NumberToken, BuildToken, StringLiteralToken, CharacterSequenceToken, Token};
    use crate::lexer::FilePosition;

    use super::TokenStream;

    #[test]
    fn should_iterate_over_token_stream() {
        let tokens = vec![
            NumberToken::build_token(String::from("123"), FilePosition::new(1, 1)),
            StringLiteralToken::build_token(String::from("foo"), FilePosition::new(1, 1)),
            CharacterSequenceToken::build_token(String::from("abc"), FilePosition::new(1, 1)),
            Token::EOF(FilePosition::new(1,1))
        ];
        
        let token_stream = TokenStream::new(tokens);
        let mut x = token_stream.iter();

        assert_eq!(x.next().unwrap(), &token_stream.tokens[0]);
        assert_eq!(x.next().unwrap(), &token_stream.tokens[1]);
        assert_eq!(x.next().unwrap(), &token_stream.tokens[2]);
        assert_eq!(x.next().unwrap(), &token_stream.tokens[3]);
        assert!(x.next().is_none());
    }
}
