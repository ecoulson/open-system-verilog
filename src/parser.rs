use crate::{
    syntax_node::{IdentifierNode, SyntaxNode},
    token:: Token,
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
        if let Token::CharacterSequence(token) = self.next_token().unwrap() {
            let (identifier, position) = token.consume();
            return Some(IdentifierNode::new(identifier, position));
        }

        None
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
        let expected_ast = IdentifierNode::new(identifier, position);
        let tokens = TokenStream::new(vec![
            CharacterSequenceToken::build_token(String::from("abc"), FilePosition::new(1, 1)),
            Token::EOF(FilePosition::new(1, 4)),
        ]);
        let mut parser = Parser::new(tokens);

        let ast = parser.parse().unwrap();

        assert_eq!(ast, expected_ast);
        assert!(parser.token_stream.next().is_none());
    }
}
