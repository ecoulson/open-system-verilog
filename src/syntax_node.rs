use crate::lexer::FilePosition;

#[derive(Debug, PartialEq, Eq)]
pub enum SyntaxNode {
    Identifier(IdentifierNode),
    Error,
    EOF,
}

#[derive(Debug, PartialEq, Eq)]
pub struct IdentifierNode {
    identifier: String,
    position: FilePosition,
}

impl IdentifierNode {
    pub fn new(identifier: String, position: FilePosition) -> SyntaxNode {
        SyntaxNode::Identifier(IdentifierNode {
            identifier,
            position,
        })
    }
}
