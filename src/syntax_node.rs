use crate::lexer::FilePosition;

#[derive(Debug, PartialEq, Eq)]
pub enum SyntaxNode<'a> {
    Identifier(IdentifierNode<'a>),
}

#[derive(Debug, PartialEq, Eq)]
pub struct IdentifierNode<'a> {
    identifier: &'a String,
    position: &'a FilePosition,
}

impl<'a> IdentifierNode<'a> {
    pub fn new<'b>(identifier: &'b String, position: &'b FilePosition) -> SyntaxNode<'b> {
        SyntaxNode::Identifier(IdentifierNode {
            identifier,
            position,
        })
    }
}
