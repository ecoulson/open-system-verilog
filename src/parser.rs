use crate::{
    syntax_node::{IdentifierNode, SyntaxNode},
    token::Token,
    token_stream::TokenStream,
};

pub struct Parser<'a> {
    token_stream: Box<dyn Iterator<Item = &'a Token> + 'a>,
}

impl<'a> Parser<'a> {
    pub fn new<'b>(token_stream: &'b TokenStream) -> Parser<'b> {
        Parser {
            token_stream: Box::new(token_stream.iter()),
        }
    }

    pub fn parse(&mut self) -> Option<SyntaxNode> {
        let token = self.token_stream.next().unwrap();
        self.token_stream.next().unwrap(); // Temporary unwarp for eof

        match token {
            Token::CharacterSequence(token) => Some(IdentifierNode::new(
                token.character_sequence(),
                token.position(),
            )),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        lexer::FilePosition,
        syntax_node::IdentifierNode,
        token::{BuildToken, CharacterSequenceToken, Token},
        token_stream::TokenStream,
    };

    use super::Parser;

    #[test]
    fn should_parse_simple_identifier() {
        let identifier = String::from("abc");
        let position = FilePosition::new(1, 1);
        let expected_ast = IdentifierNode::new(&identifier, &position);
        let tokens = TokenStream::new(vec![
            CharacterSequenceToken::build_token(String::from("abc"), FilePosition::new(1, 1)),
            Token::EOF(FilePosition::new(1, 4)),
        ]);
        let mut parser = Parser::new(&tokens);

        let ast = parser.parse().unwrap();

        assert_eq!(ast, expected_ast);
        assert!(parser.token_stream.next().is_none());
    }
}
