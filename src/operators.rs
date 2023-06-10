pub const OPERATOR_SYMBOLS: [&'static str; 50] = [
    "+", "-", "!", "~", "&", "~&", "|", "~|", "^", "~^", "^~", "++", "--", "**", "*", "/", "%",
    ">>", "<<", ">>>", "<<<", "<", "<=", ">", ">=", "inside", "dist", "==", "!=", "===", "!==",
    "==?", "!=?", "&&", "||", "->", "<->", "=", "+=", "-=", "*=", "/=", "%=", "&=", "^=", "|=",
    "<<=", ">>=", "<<<=", ">>>=",
];

// Missing replication and conditional operators ( will be used in parse but not tokenization)
#[derive(Debug)]
pub enum Operator {
    Modulo,
    Negation,
    BinaryAssignment,
    AdditionAssignment,
    SubtractionAssignment,
    MultiplcationAssignment,
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

