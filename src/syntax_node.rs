use crate::lexer::FilePosition;

#[derive(Debug, PartialEq, Eq)]
pub enum SyntaxNodeKind {
    Identifier(String),
    Error,
    EOF,
}

#[derive(Debug, PartialEq)]
pub struct SyntaxNode {
    kind: SyntaxNodeKind,
    position: FilePosition,
}

impl SyntaxNode {
    pub fn build_identifier(identifier: String, position: FilePosition) -> SyntaxNode {
        SyntaxNode {
            kind: SyntaxNodeKind::Identifier(identifier),
            position,
        }
    }

    pub fn build_error() -> SyntaxNode {
        SyntaxNode {
            kind: SyntaxNodeKind::Error,
            position: FilePosition::new(0, 0),
        }
    }

    pub fn build_eof() -> SyntaxNode {
        SyntaxNode {
            kind: SyntaxNodeKind::EOF,
            position: FilePosition::new(0, 0),
        }
    }
}
