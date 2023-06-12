use crate::keywords::Keyword;
use crate::lexer::FilePosition;
use crate::operators::Operator;
use crate::punctuation::Punctuation;

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    WhiteSpace,
    Comment,
    Number(NumberToken),
    StringLiteral(StringLiteralToken),
    CharacterSequence(CharacterSequenceToken),
    Operator(OperatorToken),
    Punctuation(PunctuationToken),
    Keyword(KeywordToken),
    EscapedIdentifier(EscapedIdentifierToken),
    Error(ErrorToken),
    EOF(FilePosition),
}

pub trait TokenFromSequence {
    fn from_sequence(sequence: &str, position: FilePosition) -> Result<Token, &'static str>;
}

pub trait BuildToken<T> {
    fn build_token(value: T, position: FilePosition) -> Token;
}

#[derive(Debug, PartialEq, Eq)]
pub struct NumberToken {
    number: String,
    position: FilePosition,
}

#[derive(Debug, PartialEq, Eq)]
pub struct StringLiteralToken {
    string_literal: String,
    position: FilePosition,
}

#[derive(Debug, PartialEq, Eq)]
pub struct CharacterSequenceToken {
    character_sequence: String,
    position: FilePosition,
}

#[derive(Debug, PartialEq, Eq)]
pub struct OperatorToken {
    operator: Operator,
    position: FilePosition,
}

#[derive(Debug, PartialEq, Eq)]
pub struct PunctuationToken {
    punctuation: Punctuation,
    position: FilePosition,
}

#[derive(Debug, PartialEq, Eq)]
pub struct KeywordToken {
    keyword: Keyword,
    position: FilePosition,
}

#[derive(Debug, PartialEq, Eq)]
pub struct EscapedIdentifierToken {
    identifier: String,
    position: FilePosition,
}

#[derive(Debug, PartialEq, Eq)]
pub struct ErrorToken {
    message: &'static str,
    position: FilePosition,
}

impl BuildToken<String> for NumberToken {
    fn build_token(number: String, position: FilePosition) -> Token {
        Token::Number(NumberToken { number, position })
    }
}

impl BuildToken<String> for StringLiteralToken {
    fn build_token(string_literal: String, position: FilePosition) -> Token {
        Token::StringLiteral(StringLiteralToken {
            string_literal,
            position,
        })
    }
}

impl BuildToken<String> for CharacterSequenceToken {
    fn build_token(character_sequence: String, position: FilePosition) -> Token {
        Token::CharacterSequence(CharacterSequenceToken {
            character_sequence,
            position,
        })
    }
}

impl BuildToken<Operator> for OperatorToken {
    fn build_token(operator: Operator, position: FilePosition) -> Token {
        Token::Operator(OperatorToken { operator, position })
    }
}

impl BuildToken<Keyword> for KeywordToken {
    fn build_token(keyword: Keyword, position: FilePosition) -> Token {
        Token::Keyword(KeywordToken { keyword, position })
    }
}

impl BuildToken<Punctuation> for PunctuationToken {
    fn build_token(punctuation: Punctuation, position: FilePosition) -> Token {
        Token::Punctuation(PunctuationToken {
            punctuation,
            position,
        })
    }
}

impl BuildToken<String> for EscapedIdentifierToken {
    fn build_token(identifier: String, position: FilePosition) -> Token {
        Token::EscapedIdentifier(EscapedIdentifierToken {
            identifier,
            position
        })
    }
}

impl BuildToken<&'static str> for ErrorToken {
    fn build_token(message: &'static str, position: FilePosition) -> Token {
        Token::Error(ErrorToken { message, position })
    }
}

impl TokenFromSequence for OperatorToken {
    fn from_sequence(sequence: &str, position: FilePosition) -> Result<Token, &'static str> {
        match sequence {
            "+" => Ok(OperatorToken::build_token(Operator::Addition, position)),
            "-" => Ok(OperatorToken::build_token(Operator::Subtraction, position)),
            "!" => Ok(OperatorToken::build_token(Operator::Not, position)),
            "~" => Ok(OperatorToken::build_token(Operator::Negation, position)),
            "&" => Ok(OperatorToken::build_token(Operator::BitwiseAnd, position)),
            "~&" => Ok(OperatorToken::build_token(Operator::Nand, position)),
            "|" => Ok(OperatorToken::build_token(Operator::BitwiseOr, position)),
            "~|" => Ok(OperatorToken::build_token(Operator::Nor, position)),
            "^" => Ok(OperatorToken::build_token(Operator::Xor, position)),
            "~^" => Ok(OperatorToken::build_token(Operator::Xnor, position)),
            "^~" => Ok(OperatorToken::build_token(Operator::Xnor, position)),
            "++" => Ok(OperatorToken::build_token(Operator::Increment, position)),
            "--" => Ok(OperatorToken::build_token(Operator::Decrement, position)),
            "**" => Ok(OperatorToken::build_token(
                Operator::Exponentiation,
                position,
            )),
            "*" => Ok(OperatorToken::build_token(
                Operator::Multiplication,
                position,
            )),
            "/" => Ok(OperatorToken::build_token(Operator::Division, position)),
            "%" => Ok(OperatorToken::build_token(Operator::Modulo, position)),
            ">>" => Ok(OperatorToken::build_token(
                Operator::LogicalRightShift,
                position,
            )),
            "<<" => Ok(OperatorToken::build_token(
                Operator::LogicalLeftShift,
                position,
            )),
            ">>>" => Ok(OperatorToken::build_token(
                Operator::ArithmeticRightShift,
                position,
            )),
            "<<<" => Ok(OperatorToken::build_token(
                Operator::ArithmeticLeftShift,
                position,
            )),
            "<" => Ok(OperatorToken::build_token(Operator::LessThan, position)),
            "<=" => Ok(OperatorToken::build_token(
                Operator::LessThanOrEqualTo,
                position,
            )),
            ">" => Ok(OperatorToken::build_token(Operator::GreaterThan, position)),
            ">=" => Ok(OperatorToken::build_token(
                Operator::GreaterThanOrEqualTo,
                position,
            )),
            "inside" => Ok(OperatorToken::build_token(Operator::Inside, position)),
            "dist" => Ok(OperatorToken::build_token(Operator::Distribution, position)),
            "==" => Ok(OperatorToken::build_token(
                Operator::LogicalEquality,
                position,
            )),
            "!=" => Ok(OperatorToken::build_token(
                Operator::LogicalInequality,
                position,
            )),
            "===" => Ok(OperatorToken::build_token(Operator::CaseEquality, position)),
            "!==" => Ok(OperatorToken::build_token(
                Operator::CaseInequality,
                position,
            )),
            "==?" => Ok(OperatorToken::build_token(
                Operator::WildcardEquality,
                position,
            )),
            "!=?" => Ok(OperatorToken::build_token(
                Operator::WildcardInequality,
                position,
            )),
            "&&" => Ok(OperatorToken::build_token(Operator::LogicalAnd, position)),
            "||" => Ok(OperatorToken::build_token(Operator::LogicalOr, position)),
            "->" => Ok(OperatorToken::build_token(Operator::Implication, position)),
            "<->" => Ok(OperatorToken::build_token(Operator::Equivalence, position)),
            "=" => Ok(OperatorToken::build_token(
                Operator::BinaryAssignment,
                position,
            )),
            "+=" => Ok(OperatorToken::build_token(
                Operator::AdditionAssignment,
                position,
            )),
            "-=" => Ok(OperatorToken::build_token(
                Operator::SubtractionAssignment,
                position,
            )),
            "*=" => Ok(OperatorToken::build_token(
                Operator::MultiplicationAssignment,
                position,
            )),
            "/=" => Ok(OperatorToken::build_token(
                Operator::DivisionAssignment,
                position,
            )),
            "%=" => Ok(OperatorToken::build_token(
                Operator::ModuloAssignment,
                position,
            )),
            "&=" => Ok(OperatorToken::build_token(
                Operator::BitwiseAndAssignment,
                position,
            )),
            "^=" => Ok(OperatorToken::build_token(
                Operator::BitwiseXorAssignment,
                position,
            )),
            "|=" => Ok(OperatorToken::build_token(
                Operator::BitwiseOrAssignment,
                position,
            )),
            "<<=" => Ok(OperatorToken::build_token(
                Operator::LogicalLeftShiftAssignment,
                position,
            )),
            ">>=" => Ok(OperatorToken::build_token(
                Operator::LogicalRightShiftAssignment,
                position,
            )),
            "<<<=" => Ok(OperatorToken::build_token(
                Operator::ArithmeticLeftShiftAssignment,
                position,
            )),
            ">>>=" => Ok(OperatorToken::build_token(
                Operator::ArithmeticRightShiftAssignment,
                position,
            )),
            _ => Err("Unrecognized operator"),
        }
    }
}

impl TokenFromSequence for KeywordToken {
    fn from_sequence(sequence: &str, position: FilePosition) -> Result<Token, &'static str> {
        match sequence {
            "accept_on" => Ok(KeywordToken::build_token(Keyword::AcceptOn, position)),
            "alias" => Ok(KeywordToken::build_token(Keyword::Alias, position)),
            "always" => Ok(KeywordToken::build_token(Keyword::Always, position)),
            "always_comb" => Ok(KeywordToken::build_token(Keyword::AlwaysComb, position)),
            "always_ff" => Ok(KeywordToken::build_token(Keyword::AlwaysFF, position)),
            "always_latch" => Ok(KeywordToken::build_token(Keyword::AlwaysLatch, position)),
            "and" => Ok(KeywordToken::build_token(Keyword::And, position)),
            "assert" => Ok(KeywordToken::build_token(Keyword::Assert, position)),
            "assign" => Ok(KeywordToken::build_token(Keyword::Assign, position)),
            "assume" => Ok(KeywordToken::build_token(Keyword::Assume, position)),
            "automatic" => Ok(KeywordToken::build_token(Keyword::Automatic, position)),
            "before" => Ok(KeywordToken::build_token(Keyword::Before, position)),
            "begin" => Ok(KeywordToken::build_token(Keyword::Begin, position)),
            "bind" => Ok(KeywordToken::build_token(Keyword::Bind, position)),
            "bins" => Ok(KeywordToken::build_token(Keyword::Bins, position)),
            "binsof" => Ok(KeywordToken::build_token(Keyword::Binsof, position)),
            "bit" => Ok(KeywordToken::build_token(Keyword::Bit, position)),
            "break" => Ok(KeywordToken::build_token(Keyword::Break, position)),
            "buf" => Ok(KeywordToken::build_token(Keyword::Buf, position)),
            "bufif0" => Ok(KeywordToken::build_token(Keyword::Bufif0, position)),
            "bufif1" => Ok(KeywordToken::build_token(Keyword::Bufif1, position)),
            "byte" => Ok(KeywordToken::build_token(Keyword::Byte, position)),
            "case" => Ok(KeywordToken::build_token(Keyword::Case, position)),
            "casex" => Ok(KeywordToken::build_token(Keyword::Casex, position)),
            "casez" => Ok(KeywordToken::build_token(Keyword::Casez, position)),
            "cell" => Ok(KeywordToken::build_token(Keyword::Cell, position)),
            "chandle" => Ok(KeywordToken::build_token(Keyword::Chandle, position)),
            "checker" => Ok(KeywordToken::build_token(Keyword::Checker, position)),
            "class" => Ok(KeywordToken::build_token(Keyword::Class, position)),
            "clocking" => Ok(KeywordToken::build_token(Keyword::Clocking, position)),
            "cmos" => Ok(KeywordToken::build_token(Keyword::Cmos, position)),
            "config" => Ok(KeywordToken::build_token(Keyword::Config, position)),
            "const" => Ok(KeywordToken::build_token(Keyword::Const, position)),
            "constraint" => Ok(KeywordToken::build_token(Keyword::Constraint, position)),
            "context" => Ok(KeywordToken::build_token(Keyword::Context, position)),
            "continue" => Ok(KeywordToken::build_token(Keyword::Continue, position)),
            "cover" => Ok(KeywordToken::build_token(Keyword::Cover, position)),
            "covergroup" => Ok(KeywordToken::build_token(Keyword::Covergroup, position)),
            "coverpoint" => Ok(KeywordToken::build_token(Keyword::Coverpoint, position)),
            "cross" => Ok(KeywordToken::build_token(Keyword::Cross, position)),
            "deassign" => Ok(KeywordToken::build_token(Keyword::Deassign, position)),
            "default" => Ok(KeywordToken::build_token(Keyword::Default, position)),
            "defparam" => Ok(KeywordToken::build_token(Keyword::Defparam, position)),
            "design" => Ok(KeywordToken::build_token(Keyword::Design, position)),
            "disable" => Ok(KeywordToken::build_token(Keyword::Disable, position)),
            "do" => Ok(KeywordToken::build_token(Keyword::Do, position)),
            "edge" => Ok(KeywordToken::build_token(Keyword::Edge, position)),
            "else" => Ok(KeywordToken::build_token(Keyword::Else, position)),
            "end" => Ok(KeywordToken::build_token(Keyword::End, position)),
            "endcase" => Ok(KeywordToken::build_token(Keyword::Endcase, position)),
            "endchecker" => Ok(KeywordToken::build_token(Keyword::Endchecker, position)),
            "endclass" => Ok(KeywordToken::build_token(Keyword::Endclass, position)),
            "endclocking" => Ok(KeywordToken::build_token(Keyword::Endclocking, position)),
            "endconfig" => Ok(KeywordToken::build_token(Keyword::Endconfig, position)),
            "endfunction" => Ok(KeywordToken::build_token(Keyword::Endfunction, position)),
            "endgenerate" => Ok(KeywordToken::build_token(Keyword::Endgenerate, position)),
            "endgroup" => Ok(KeywordToken::build_token(Keyword::Endgroup, position)),
            "endinterface" => Ok(KeywordToken::build_token(Keyword::Endinterface, position)),
            "endmodule" => Ok(KeywordToken::build_token(Keyword::Endmodule, position)),
            "endpackage" => Ok(KeywordToken::build_token(Keyword::Endpackage, position)),
            "endprimitive" => Ok(KeywordToken::build_token(Keyword::Endprimitive, position)),
            "endprogram" => Ok(KeywordToken::build_token(Keyword::Endprogram, position)),
            "endproperty" => Ok(KeywordToken::build_token(Keyword::Endproperty, position)),
            "endspecify" => Ok(KeywordToken::build_token(Keyword::Endspecify, position)),
            "endsequence" => Ok(KeywordToken::build_token(Keyword::Endsequence, position)),
            "endtable" => Ok(KeywordToken::build_token(Keyword::Endtable, position)),
            "endtask" => Ok(KeywordToken::build_token(Keyword::Endtask, position)),
            "enum" => Ok(KeywordToken::build_token(Keyword::Enum, position)),
            "event" => Ok(KeywordToken::build_token(Keyword::Event, position)),
            "eventually" => Ok(KeywordToken::build_token(Keyword::Eventually, position)),
            "expect" => Ok(KeywordToken::build_token(Keyword::Expect, position)),
            "export" => Ok(KeywordToken::build_token(Keyword::Export, position)),
            "extends" => Ok(KeywordToken::build_token(Keyword::Extends, position)),
            "extern" => Ok(KeywordToken::build_token(Keyword::Extern, position)),
            "final" => Ok(KeywordToken::build_token(Keyword::Final, position)),
            "first_match" => Ok(KeywordToken::build_token(Keyword::FirstMatch, position)),
            "for" => Ok(KeywordToken::build_token(Keyword::For, position)),
            "force" => Ok(KeywordToken::build_token(Keyword::Force, position)),
            "foreach" => Ok(KeywordToken::build_token(Keyword::Foreach, position)),
            "forever" => Ok(KeywordToken::build_token(Keyword::Forever, position)),
            "fork" => Ok(KeywordToken::build_token(Keyword::Fork, position)),
            "forkjoin" => Ok(KeywordToken::build_token(Keyword::Forkjoin, position)),
            "function" => Ok(KeywordToken::build_token(Keyword::Function, position)),
            "generate" => Ok(KeywordToken::build_token(Keyword::Generate, position)),
            "genvar" => Ok(KeywordToken::build_token(Keyword::Genvar, position)),
            "global" => Ok(KeywordToken::build_token(Keyword::Global, position)),
            "highz0" => Ok(KeywordToken::build_token(Keyword::Highz0, position)),
            "highz1" => Ok(KeywordToken::build_token(Keyword::Highz1, position)),
            "if" => Ok(KeywordToken::build_token(Keyword::If, position)),
            "iff" => Ok(KeywordToken::build_token(Keyword::Iff, position)),
            "ifnone" => Ok(KeywordToken::build_token(Keyword::Ifnone, position)),
            "ignore_bins" => Ok(KeywordToken::build_token(Keyword::IgnoreBins, position)),
            "illegal_bins" => Ok(KeywordToken::build_token(Keyword::IllegalBins, position)),
            "implements" => Ok(KeywordToken::build_token(Keyword::Implements, position)),
            "implies" => Ok(KeywordToken::build_token(Keyword::Implies, position)),
            "import" => Ok(KeywordToken::build_token(Keyword::Import, position)),
            "incdir" => Ok(KeywordToken::build_token(Keyword::Incdir, position)),
            "include" => Ok(KeywordToken::build_token(Keyword::Include, position)),
            "initial" => Ok(KeywordToken::build_token(Keyword::Initial, position)),
            "inout" => Ok(KeywordToken::build_token(Keyword::Inout, position)),
            "input" => Ok(KeywordToken::build_token(Keyword::Input, position)),
            "instance" => Ok(KeywordToken::build_token(Keyword::Instance, position)),
            "int" => Ok(KeywordToken::build_token(Keyword::Int, position)),
            "integer" => Ok(KeywordToken::build_token(Keyword::Integer, position)),
            "interconnect" => Ok(KeywordToken::build_token(Keyword::Interconnect, position)),
            "interface" => Ok(KeywordToken::build_token(Keyword::Interface, position)),
            "intersect" => Ok(KeywordToken::build_token(Keyword::Intersect, position)),
            "join" => Ok(KeywordToken::build_token(Keyword::Join, position)),
            "join_any" => Ok(KeywordToken::build_token(Keyword::JoinAny, position)),
            "join_none" => Ok(KeywordToken::build_token(Keyword::JoinNone, position)),
            "large" => Ok(KeywordToken::build_token(Keyword::Large, position)),
            "let" => Ok(KeywordToken::build_token(Keyword::Let, position)),
            "liblist" => Ok(KeywordToken::build_token(Keyword::Liblist, position)),
            "library" => Ok(KeywordToken::build_token(Keyword::Library, position)),
            "local" => Ok(KeywordToken::build_token(Keyword::Local, position)),
            "localparam" => Ok(KeywordToken::build_token(Keyword::Localparam, position)),
            "logic" => Ok(KeywordToken::build_token(Keyword::Logic, position)),
            "longint" => Ok(KeywordToken::build_token(Keyword::Longint, position)),
            "macromodule" => Ok(KeywordToken::build_token(Keyword::Macromodule, position)),
            "matches" => Ok(KeywordToken::build_token(Keyword::Matches, position)),
            "medium" => Ok(KeywordToken::build_token(Keyword::Medium, position)),
            "modport" => Ok(KeywordToken::build_token(Keyword::Modport, position)),
            "module" => Ok(KeywordToken::build_token(Keyword::Module, position)),
            "nand" => Ok(KeywordToken::build_token(Keyword::Nand, position)),
            "negedge" => Ok(KeywordToken::build_token(Keyword::Negedge, position)),
            "nettype" => Ok(KeywordToken::build_token(Keyword::Nettype, position)),
            "new" => Ok(KeywordToken::build_token(Keyword::New, position)),
            "nexttime" => Ok(KeywordToken::build_token(Keyword::Nexttime, position)),
            "nmos" => Ok(KeywordToken::build_token(Keyword::Nmos, position)),
            "nor" => Ok(KeywordToken::build_token(Keyword::Nor, position)),
            "noshowcancelled" => Ok(KeywordToken::build_token(
                Keyword::Noshowcancelled,
                position,
            )),
            "not" => Ok(KeywordToken::build_token(Keyword::Not, position)),
            "notif0" => Ok(KeywordToken::build_token(Keyword::Notif0, position)),
            "notif1" => Ok(KeywordToken::build_token(Keyword::Notif1, position)),
            "null" => Ok(KeywordToken::build_token(Keyword::Null, position)),
            "or" => Ok(KeywordToken::build_token(Keyword::Or, position)),
            "output" => Ok(KeywordToken::build_token(Keyword::Output, position)),
            "package" => Ok(KeywordToken::build_token(Keyword::Package, position)),
            "packed" => Ok(KeywordToken::build_token(Keyword::Packed, position)),
            "parameter" => Ok(KeywordToken::build_token(Keyword::Parameter, position)),
            "pmos" => Ok(KeywordToken::build_token(Keyword::Pmos, position)),
            "posedge" => Ok(KeywordToken::build_token(Keyword::Posedge, position)),
            "primitive" => Ok(KeywordToken::build_token(Keyword::Primitive, position)),
            "priority" => Ok(KeywordToken::build_token(Keyword::Priority, position)),
            "program" => Ok(KeywordToken::build_token(Keyword::Program, position)),
            "property" => Ok(KeywordToken::build_token(Keyword::Property, position)),
            "protected" => Ok(KeywordToken::build_token(Keyword::Protected, position)),
            "pull0" => Ok(KeywordToken::build_token(Keyword::Pull0, position)),
            "pull1" => Ok(KeywordToken::build_token(Keyword::Pull1, position)),
            "pulldown" => Ok(KeywordToken::build_token(Keyword::Pulldown, position)),
            "pullup" => Ok(KeywordToken::build_token(Keyword::Pullup, position)),
            "pulsestyle_ondetect" => Ok(KeywordToken::build_token(
                Keyword::PulsestyleOndetect,
                position,
            )),
            "pulsestyle_onevent" => Ok(KeywordToken::build_token(
                Keyword::PulsestyleOnevent,
                position,
            )),
            "pure" => Ok(KeywordToken::build_token(Keyword::Pure, position)),
            "rand" => Ok(KeywordToken::build_token(Keyword::Rand, position)),
            "randc" => Ok(KeywordToken::build_token(Keyword::Randc, position)),
            "randcase" => Ok(KeywordToken::build_token(Keyword::Randcase, position)),
            "randsequence" => Ok(KeywordToken::build_token(Keyword::Randsequence, position)),
            "rcmos" => Ok(KeywordToken::build_token(Keyword::Rcmos, position)),
            "real" => Ok(KeywordToken::build_token(Keyword::Real, position)),
            "realtime" => Ok(KeywordToken::build_token(Keyword::Realtime, position)),
            "ref" => Ok(KeywordToken::build_token(Keyword::Ref, position)),
            "reg" => Ok(KeywordToken::build_token(Keyword::Reg, position)),
            "reject_on" => Ok(KeywordToken::build_token(Keyword::RejectOn, position)),
            "release" => Ok(KeywordToken::build_token(Keyword::Release, position)),
            "repeat" => Ok(KeywordToken::build_token(Keyword::Repeat, position)),
            "restrict" => Ok(KeywordToken::build_token(Keyword::Restrict, position)),
            "return" => Ok(KeywordToken::build_token(Keyword::Return, position)),
            "rnmos" => Ok(KeywordToken::build_token(Keyword::Rnmos, position)),
            "rpmos" => Ok(KeywordToken::build_token(Keyword::Rpmos, position)),
            "rtran" => Ok(KeywordToken::build_token(Keyword::Rtran, position)),
            "rtranif0" => Ok(KeywordToken::build_token(Keyword::Rtranif0, position)),
            "rtranif1" => Ok(KeywordToken::build_token(Keyword::Rtranif1, position)),
            "s_always" => Ok(KeywordToken::build_token(Keyword::SAlways, position)),
            "s_eventually" => Ok(KeywordToken::build_token(Keyword::SEventually, position)),
            "s_nexttime" => Ok(KeywordToken::build_token(Keyword::SNexttime, position)),
            "s_until" => Ok(KeywordToken::build_token(Keyword::SUntil, position)),
            "s_until_with" => Ok(KeywordToken::build_token(Keyword::SUntilWith, position)),
            "scalared" => Ok(KeywordToken::build_token(Keyword::Scalared, position)),
            "sequence" => Ok(KeywordToken::build_token(Keyword::Sequence, position)),
            "shortint" => Ok(KeywordToken::build_token(Keyword::Shortint, position)),
            "shortreal" => Ok(KeywordToken::build_token(Keyword::Shortreal, position)),
            "showcancelled" => Ok(KeywordToken::build_token(Keyword::Showcancelled, position)),
            "signed" => Ok(KeywordToken::build_token(Keyword::Signed, position)),
            "small" => Ok(KeywordToken::build_token(Keyword::Small, position)),
            "soft" => Ok(KeywordToken::build_token(Keyword::Soft, position)),
            "solve" => Ok(KeywordToken::build_token(Keyword::Solve, position)),
            "specify" => Ok(KeywordToken::build_token(Keyword::Specify, position)),
            "specparam" => Ok(KeywordToken::build_token(Keyword::Specparam, position)),
            "static" => Ok(KeywordToken::build_token(Keyword::Static, position)),
            "string" => Ok(KeywordToken::build_token(Keyword::String, position)),
            "strong" => Ok(KeywordToken::build_token(Keyword::Strong, position)),
            "strong0" => Ok(KeywordToken::build_token(Keyword::Strong0, position)),
            "strong1" => Ok(KeywordToken::build_token(Keyword::Strong1, position)),
            "struct" => Ok(KeywordToken::build_token(Keyword::Struct, position)),
            "super" => Ok(KeywordToken::build_token(Keyword::Super, position)),
            "supply0" => Ok(KeywordToken::build_token(Keyword::Supply0, position)),
            "supply1" => Ok(KeywordToken::build_token(Keyword::Supply1, position)),
            "sync_accept_on" => Ok(KeywordToken::build_token(Keyword::SyncAcceptOn, position)),
            "sync_reject_on" => Ok(KeywordToken::build_token(Keyword::SyncRejectOn, position)),
            "table" => Ok(KeywordToken::build_token(Keyword::Table, position)),
            "tagged" => Ok(KeywordToken::build_token(Keyword::Tagged, position)),
            "task" => Ok(KeywordToken::build_token(Keyword::Task, position)),
            "this" => Ok(KeywordToken::build_token(Keyword::This, position)),
            "throughout" => Ok(KeywordToken::build_token(Keyword::Throughout, position)),
            "time" => Ok(KeywordToken::build_token(Keyword::Time, position)),
            "timeprecision" => Ok(KeywordToken::build_token(Keyword::Timeprecision, position)),
            "timeunit" => Ok(KeywordToken::build_token(Keyword::Timeunit, position)),
            "tran" => Ok(KeywordToken::build_token(Keyword::Tran, position)),
            "tranif0" => Ok(KeywordToken::build_token(Keyword::Tranif0, position)),
            "tranif1" => Ok(KeywordToken::build_token(Keyword::Tranif1, position)),
            "tri" => Ok(KeywordToken::build_token(Keyword::Tri, position)),
            "tri0" => Ok(KeywordToken::build_token(Keyword::Tri0, position)),
            "tri1" => Ok(KeywordToken::build_token(Keyword::Tri1, position)),
            "triand" => Ok(KeywordToken::build_token(Keyword::Triand, position)),
            "trior" => Ok(KeywordToken::build_token(Keyword::Trior, position)),
            "trireg" => Ok(KeywordToken::build_token(Keyword::Trireg, position)),
            "type" => Ok(KeywordToken::build_token(Keyword::Type, position)),
            "typedef" => Ok(KeywordToken::build_token(Keyword::Typedef, position)),
            "union" => Ok(KeywordToken::build_token(Keyword::Union, position)),
            "unique" => Ok(KeywordToken::build_token(Keyword::Unique, position)),
            "unique0" => Ok(KeywordToken::build_token(Keyword::Unique0, position)),
            "unsigned" => Ok(KeywordToken::build_token(Keyword::Unsigned, position)),
            "until" => Ok(KeywordToken::build_token(Keyword::Until, position)),
            "until_with" => Ok(KeywordToken::build_token(Keyword::UntilWith, position)),
            "untyped" => Ok(KeywordToken::build_token(Keyword::Untyped, position)),
            "use" => Ok(KeywordToken::build_token(Keyword::Use, position)),
            "uwire" => Ok(KeywordToken::build_token(Keyword::Uwire, position)),
            "var" => Ok(KeywordToken::build_token(Keyword::Var, position)),
            "vectored" => Ok(KeywordToken::build_token(Keyword::Vectored, position)),
            "virtual" => Ok(KeywordToken::build_token(Keyword::Virtual, position)),
            "void" => Ok(KeywordToken::build_token(Keyword::Void, position)),
            "wait" => Ok(KeywordToken::build_token(Keyword::Wait, position)),
            "wait_order" => Ok(KeywordToken::build_token(Keyword::WaitOrder, position)),
            "wand" => Ok(KeywordToken::build_token(Keyword::Wand, position)),
            "weak" => Ok(KeywordToken::build_token(Keyword::Weak, position)),
            "weak0" => Ok(KeywordToken::build_token(Keyword::Weak0, position)),
            "weak1" => Ok(KeywordToken::build_token(Keyword::Weak1, position)),
            "while" => Ok(KeywordToken::build_token(Keyword::While, position)),
            "wildcard" => Ok(KeywordToken::build_token(Keyword::Wildcard, position)),
            "wire" => Ok(KeywordToken::build_token(Keyword::Wire, position)),
            "with" => Ok(KeywordToken::build_token(Keyword::With, position)),
            "within" => Ok(KeywordToken::build_token(Keyword::Within, position)),
            "wor" => Ok(KeywordToken::build_token(Keyword::Wor, position)),
            "xnor" => Ok(KeywordToken::build_token(Keyword::Xnor, position)),
            "xor" => Ok(KeywordToken::build_token(Keyword::Xor, position)),
            _ => Err("Unrecognized keyword"),
        }
    }
}
