use crate::{syntax_node::{SyntaxNode, IdentifierNode}, token_stream::TokenStream, lexer::FilePosition};

pub struct Parser {
    token_stream: TokenStream,
    errors: Vec<String>,
}

impl Parser {
    pub fn new(token_stream: TokenStream) -> Parser {
        Parser {
            token_stream,
            errors: vec![],
        }
    }

    pub fn parse(&mut self) -> Result<Option<SyntaxNode>, Vec<String>> {
        Ok(Some(IdentifierNode::new(String::from("abc"), FilePosition::new(1,1))))
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        lexer::FilePosition,
        syntax_node::IdentifierNode,
        token::{BuildToken, CharacterSequenceToken},
        token_stream::TokenStream,
    };

    use super::Parser;

    #[test]
    fn should_parse_simple_identifier() -> Result<(), Vec<String>> {
        let expected_ast = IdentifierNode::new(String::from("abc"), FilePosition::new(1, 1));
        let tokens = TokenStream::new(vec![CharacterSequenceToken::build_token(
            String::from("abc"),
            FilePosition::new(0, 0),
        )]);
        let mut parser = Parser::new(tokens);

        let ast = parser.parse()?.unwrap();

        assert_eq!(ast, expected_ast);

        Ok(())
    }
}
