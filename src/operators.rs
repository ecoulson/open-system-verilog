use crate::{lexer::FilePosition, token::{Token, TokenFromSequence}};

pub const OPERATOR_SYMBOLS: [&'static str; 50] = [
    "+", "-", "!", "~", "&", "~&", "|", "~|", "^", "~^", "^~", "++", "--", "**", "*", "/", "%",
    ">>", "<<", ">>>", "<<<", "<", "<=", ">", ">=", "inside", "dist", "==", "!=", "===", "!==",
    "==?", "!=?", "&&", "||", "->", "<->", "=", "+=", "-=", "*=", "/=", "%=", "&=", "^=", "|=",
    "<<=", ">>=", "<<<=", ">>>=",
];

// Missing replication and conditional operators ( will be used in parse but not tokenization)
#[derive(Debug, PartialEq, Eq)]
pub enum Operator {
    Modulo,
    Negation,
    BinaryAssignment,
    AdditionAssignment,
    SubtractionAssignment,
    MultiplicationAssignment,
    DivisionAssignment,
    ModuloAssignment,
    BitwiseAndAssignment,
    BitwiseOrAssignment,
    BitwiseXorAssignment,
    LogicalLeftShiftAssignment,
    LogicalRightShiftAssignment,
    ArithmeticRightShiftAssignment,
    ArithmeticLeftShiftAssignment,
    Addition,
    Subtraction,
    Multiplication,
    Division,
    Exponentiation,
    Not,
    BitwiseAnd,
    Nand,
    BitwiseOr,
    Nor,
    Xor,
    Xnor,
    LogicalLeftShift,
    LogicalRightShift,
    ArithmeticLeftShift,
    ArithmeticRightShift,
    LogicalAnd,
    LogicalOr,
    Implication,
    Equivalence,
    LessThan,
    GreaterThan,
    LessThanOrEqualTo,
    GreaterThanOrEqualTo,
    CaseEquality,
    CaseInequality,
    LogicalEquality,
    LogicalInequality,
    WildcardEquality,
    WildcardInequality,
    Increment,
    Decrement,
    Inside,
    Distribution,
}

impl TokenFromSequence for Operator {
    fn from_sequence(sequence: &str, position: FilePosition) -> Result<Token, &'static str> {
        match sequence {
            "+" => Ok(Token::build_operator_token(Operator::Addition, position)),
            "-" => Ok(Token::build_operator_token(Operator::Subtraction, position)),
            "!" => Ok(Token::build_operator_token(Operator::Not, position)),
            "~" => Ok(Token::build_operator_token(Operator::Negation, position)),
            "&" => Ok(Token::build_operator_token(Operator::BitwiseAnd, position)),
            "~&" => Ok(Token::build_operator_token(Operator::Nand, position)),
            "|" => Ok(Token::build_operator_token(Operator::BitwiseOr, position)),
            "~|" => Ok(Token::build_operator_token(Operator::Nor, position)),
            "^" => Ok(Token::build_operator_token(Operator::Xor, position)),
            "~^" => Ok(Token::build_operator_token(Operator::Xnor, position)),
            "^~" => Ok(Token::build_operator_token(Operator::Xnor, position)),
            "++" => Ok(Token::build_operator_token(Operator::Increment, position)),
            "--" => Ok(Token::build_operator_token(Operator::Decrement, position)),
            "**" => Ok(Token::build_operator_token(
                Operator::Exponentiation,
                position,
            )),
            "*" => Ok(Token::build_operator_token(
                Operator::Multiplication,
                position,
            )),
            "/" => Ok(Token::build_operator_token(Operator::Division, position)),
            "%" => Ok(Token::build_operator_token(Operator::Modulo, position)),
            ">>" => Ok(Token::build_operator_token(
                Operator::LogicalRightShift,
                position,
            )),
            "<<" => Ok(Token::build_operator_token(
                Operator::LogicalLeftShift,
                position,
            )),
            ">>>" => Ok(Token::build_operator_token(
                Operator::ArithmeticRightShift,
                position,
            )),
            "<<<" => Ok(Token::build_operator_token(
                Operator::ArithmeticLeftShift,
                position,
            )),
            "<" => Ok(Token::build_operator_token(Operator::LessThan, position)),
            "<=" => Ok(Token::build_operator_token(
                Operator::LessThanOrEqualTo,
                position,
            )),
            ">" => Ok(Token::build_operator_token(Operator::GreaterThan, position)),
            ">=" => Ok(Token::build_operator_token(
                Operator::GreaterThanOrEqualTo,
                position,
            )),
            "inside" => Ok(Token::build_operator_token(Operator::Inside, position)),
            "dist" => Ok(Token::build_operator_token(Operator::Distribution, position)),
            "==" => Ok(Token::build_operator_token(
                Operator::LogicalEquality,
                position,
            )),
            "!=" => Ok(Token::build_operator_token(
                Operator::LogicalInequality,
                position,
            )),
            "===" => Ok(Token::build_operator_token(Operator::CaseEquality, position)),
            "!==" => Ok(Token::build_operator_token(
                Operator::CaseInequality,
                position,
            )),
            "==?" => Ok(Token::build_operator_token(
                Operator::WildcardEquality,
                position,
            )),
            "!=?" => Ok(Token::build_operator_token(
                Operator::WildcardInequality,
                position,
            )),
            "&&" => Ok(Token::build_operator_token(Operator::LogicalAnd, position)),
            "||" => Ok(Token::build_operator_token(Operator::LogicalOr, position)),
            "->" => Ok(Token::build_operator_token(Operator::Implication, position)),
            "<->" => Ok(Token::build_operator_token(Operator::Equivalence, position)),
            "=" => Ok(Token::build_operator_token(
                Operator::BinaryAssignment,
                position,
            )),
            "+=" => Ok(Token::build_operator_token(
                Operator::AdditionAssignment,
                position,
            )),
            "-=" => Ok(Token::build_operator_token(
                Operator::SubtractionAssignment,
                position,
            )),
            "*=" => Ok(Token::build_operator_token(
                Operator::MultiplicationAssignment,
                position,
            )),
            "/=" => Ok(Token::build_operator_token(
                Operator::DivisionAssignment,
                position,
            )),
            "%=" => Ok(Token::build_operator_token(
                Operator::ModuloAssignment,
                position,
            )),
            "&=" => Ok(Token::build_operator_token(
                Operator::BitwiseAndAssignment,
                position,
            )),
            "^=" => Ok(Token::build_operator_token(
                Operator::BitwiseXorAssignment,
                position,
            )),
            "|=" => Ok(Token::build_operator_token(
                Operator::BitwiseOrAssignment,
                position,
            )),
            "<<=" => Ok(Token::build_operator_token(
                Operator::LogicalLeftShiftAssignment,
                position,
            )),
            ">>=" => Ok(Token::build_operator_token(
                Operator::LogicalRightShiftAssignment,
                position,
            )),
            "<<<=" => Ok(Token::build_operator_token(
                Operator::ArithmeticLeftShiftAssignment,
                position,
            )),
            ">>>=" => Ok(Token::build_operator_token(
                Operator::ArithmeticRightShiftAssignment,
                position,
            )),
            _ => Err("Unrecognized operator"),
        }
    }
}
