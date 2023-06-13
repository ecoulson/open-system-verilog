use crate::{
    syntax_node::{IdentifierNode, SyntaxNode},
    token::Token,
    token_stream::TokenStream,
};

pub struct Parser {
    token_stream: TokenStream,
}

impl Parser {
    pub fn new(token_stream: TokenStream) -> Parser {
        Parser { token_stream }
    }

    pub fn parse(&mut self) -> Option<SyntaxNode> {
        let simple_identifier = self.parse_simple_identifier();

        match self.next_token() {
            Some(Token::EOF(_)) => simple_identifier,
            _ => None,
        }
    }

    fn next_token(&mut self) -> Option<Token> {
        self.token_stream.next()
    }

    fn parse_simple_identifier(&mut self) -> Option<SyntaxNode> {
        if let Some(Token::CharacterSequence(token)) = self.next_token() {
            let (identifier, position) = token.consume();
            return Some(IdentifierNode::new(identifier, position));
        }

        None
    }
}
