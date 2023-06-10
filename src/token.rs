use crate::keywords::Keyword;
use crate::operators::Operator;
use crate::punctuation::Punctuation;

#[derive(Debug)]
pub enum Token {
    WhiteSpace,
    Comment,
    Number(NumberToken),
    StringLiteral(StringLiteralToken),
    CharacterSequence(CharacterSequenceToken),
    Operator(OperatorToken),
    Punctuation(PunctuationToken),
    Keyword(KeywordToken),
    Error(ErrorToken),
    EOF,
}

pub trait TokenFromSequence {
    fn from_sequence(sequence: &str) -> Result<Token, &'static str>;
}

pub trait BuildToken<T> {
    fn build_token(value: T) -> Token;
}

#[derive(Debug)]
pub struct NumberToken {
    number: String,
}

#[derive(Debug)]
pub struct StringLiteralToken {
    string_literal: String,
}

#[derive(Debug)]
pub struct CharacterSequenceToken {
    character_sequence: String,
}

#[derive(Debug)]
pub struct OperatorToken {
    operator: Operator,
}

#[derive(Debug)]
pub struct PunctuationToken {
    punctuation: Punctuation,
}

#[derive(Debug)]
pub struct KeywordToken {
    keyword: Keyword,
}

#[derive(Debug)]
pub struct ErrorToken {
    message: &'static str,
}

impl BuildToken<String> for NumberToken {
    fn build_token(number: String) -> Token {
        Token::Number(NumberToken { number })
    }
}

impl BuildToken<String> for StringLiteralToken {
    fn build_token(string_literal: String) -> Token {
        Token::StringLiteral(StringLiteralToken { string_literal })
    }
}

impl BuildToken<String> for CharacterSequenceToken {
    fn build_token(character_sequence: String) -> Token {
        Token::CharacterSequence(CharacterSequenceToken { character_sequence })
    }
}

impl BuildToken<Operator> for OperatorToken {
    fn build_token(operator: Operator) -> Token {
        Token::Operator(OperatorToken { operator })
    }
}

impl BuildToken<Keyword> for KeywordToken {
    fn build_token(keyword: Keyword) -> Token {
        Token::Keyword(KeywordToken { keyword })
    }
}

impl BuildToken<Punctuation> for PunctuationToken {
    fn build_token(punctuation: Punctuation) -> Token {
        Token::Punctuation(PunctuationToken { punctuation })
    }
}

impl BuildToken<&'static str> for ErrorToken {
    fn build_token(message: &'static str) -> Token {
        Token::Error(ErrorToken { message })
    }
}

impl TokenFromSequence for OperatorToken {
    fn from_sequence(sequence: &str) -> Result<Token, &'static str> {
        match sequence {
            "+" => Ok(OperatorToken::build_token(Operator::Addition)),
            "-" => Ok(OperatorToken::build_token(Operator::Subtraction)),
            "!" => Ok(OperatorToken::build_token(Operator::Not)),
            "~" => Ok(OperatorToken::build_token(Operator::Negation)),
            "&" => Ok(OperatorToken::build_token(Operator::BitwiseAnd)),
            "~&" => Ok(OperatorToken::build_token(Operator::Nand)),
            "|" => Ok(OperatorToken::build_token(Operator::BitwiseOr)),
            "~|" => Ok(OperatorToken::build_token(Operator::Nor)),
            "^" => Ok(OperatorToken::build_token(Operator::Xor)),
            "~^" => Ok(OperatorToken::build_token(Operator::Xnor)),
            "^~" => Ok(OperatorToken::build_token(Operator::Xnor)),
            "++" => Ok(OperatorToken::build_token(Operator::Increment)),
            "--" => Ok(OperatorToken::build_token(Operator::Decrement)),
            "**" => Ok(OperatorToken::build_token(Operator::Exponentiation)),
            "*" => Ok(OperatorToken::build_token(Operator::Multiplication)),
            "/" => Ok(OperatorToken::build_token(Operator::Division)),
            "%" => Ok(OperatorToken::build_token(Operator::Modulo)),
            ">>" => Ok(OperatorToken::build_token(Operator::ArithmeticRightShift)),
            "<<" => Ok(OperatorToken::build_token(Operator::ArithmeticLeftShift)),
            ">>>" => Ok(OperatorToken::build_token(Operator::LogicalRightShift)),
            "<<<" => Ok(OperatorToken::build_token(Operator::LogicalLeftShift)),
            "<" => Ok(OperatorToken::build_token(Operator::LessThan)),
            "<=" => Ok(OperatorToken::build_token(Operator::LessThanOrEqualTo)),
            ">" => Ok(OperatorToken::build_token(Operator::GreaterThan)),
            ">=" => Ok(OperatorToken::build_token(Operator::GreaterThanOrEqualTo)),
            "inside" => Ok(OperatorToken::build_token(Operator::Inside)),
            "dist" => Ok(OperatorToken::build_token(Operator::Distribution)),
            "==" => Ok(OperatorToken::build_token(Operator::LogicalEquality)),
            "!=" => Ok(OperatorToken::build_token(Operator::LogicalInequality)),
            "===" => Ok(OperatorToken::build_token(Operator::CaseEquality)),
            "!==" => Ok(OperatorToken::build_token(Operator::CaseInequality)),
            "==?" => Ok(OperatorToken::build_token(Operator::WildcardEquality)),
            "!=?" => Ok(OperatorToken::build_token(Operator::WildcardInequality)),
            "&&" => Ok(OperatorToken::build_token(Operator::LogicalAnd)),
            "||" => Ok(OperatorToken::build_token(Operator::LogicalOr)),
            "->" => Ok(OperatorToken::build_token(Operator::Implication)),
            "<->" => Ok(OperatorToken::build_token(Operator::Equivalence)),
            "=" => Ok(OperatorToken::build_token(Operator::BinaryAssignment)),
            "+=" => Ok(OperatorToken::build_token(Operator::AdditionAssignment)),
            "-=" => Ok(OperatorToken::build_token(Operator::SubtractionAssignment)),
            "*=" => Ok(OperatorToken::build_token(
                Operator::MultiplcationAssignment,
            )),
            "/=" => Ok(OperatorToken::build_token(Operator::DivisionAssignment)),
            "%=" => Ok(OperatorToken::build_token(Operator::ModuloAssignment)),
            "&=" => Ok(OperatorToken::build_token(Operator::BitwiseAndAssignment)),
            "^=" => Ok(OperatorToken::build_token(Operator::BitwiseXorAssignment)),
            "|=" => Ok(OperatorToken::build_token(Operator::BitwiseOrAssignment)),
            "<<=" => Ok(OperatorToken::build_token(
                Operator::ArithmeticLeftShiftAssignment,
            )),
            ">>=" => Ok(OperatorToken::build_token(
                Operator::ArithmeticRightShiftAssignment,
            )),
            "<<<=" => Ok(OperatorToken::build_token(
                Operator::LogicalLeftShiftAssignment,
            )),
            ">>>=" => Ok(OperatorToken::build_token(
                Operator::LogicalRightShiftAssignment,
            )),
            _ => Err("Unrecognized operator"),
        }
    }
}

impl TokenFromSequence for KeywordToken {
    fn from_sequence(sequence: &str) -> Result<Token, &'static str> {
        match sequence {
            "accept_on" => Ok(KeywordToken::build_token(Keyword::AcceptOn)),
            "alias" => Ok(KeywordToken::build_token(Keyword::Alias)),
            "always" => Ok(KeywordToken::build_token(Keyword::Always)),
            "always_comb" => Ok(KeywordToken::build_token(Keyword::AlwaysComb)),
            "always_ff" => Ok(KeywordToken::build_token(Keyword::AlwaysFF)),
            "always_latch" => Ok(KeywordToken::build_token(Keyword::AlwaysLatch)),
            "and" => Ok(KeywordToken::build_token(Keyword::And)),
            "assert" => Ok(KeywordToken::build_token(Keyword::Assert)),
            "assign" => Ok(KeywordToken::build_token(Keyword::Assign)),
            "assume" => Ok(KeywordToken::build_token(Keyword::Assume)),
            "automatic" => Ok(KeywordToken::build_token(Keyword::Automatic)),
            "before" => Ok(KeywordToken::build_token(Keyword::Before)),
            "begin" => Ok(KeywordToken::build_token(Keyword::Begin)),
            "bind" => Ok(KeywordToken::build_token(Keyword::Bind)),
            "bins" => Ok(KeywordToken::build_token(Keyword::Bins)),
            "binsof" => Ok(KeywordToken::build_token(Keyword::Binsof)),
            "bit" => Ok(KeywordToken::build_token(Keyword::Bit)),
            "break" => Ok(KeywordToken::build_token(Keyword::Break)),
            "buf" => Ok(KeywordToken::build_token(Keyword::Buf)),
            "bufif0" => Ok(KeywordToken::build_token(Keyword::Bufif0)),
            "bufif1" => Ok(KeywordToken::build_token(Keyword::Bufif1)),
            "byte" => Ok(KeywordToken::build_token(Keyword::Byte)),
            "case" => Ok(KeywordToken::build_token(Keyword::Case)),
            "casex" => Ok(KeywordToken::build_token(Keyword::Casex)),
            "casez" => Ok(KeywordToken::build_token(Keyword::Casez)),
            "cell" => Ok(KeywordToken::build_token(Keyword::Cell)),
            "chandle" => Ok(KeywordToken::build_token(Keyword::Chandle)),
            "checker" => Ok(KeywordToken::build_token(Keyword::Checker)),
            "class" => Ok(KeywordToken::build_token(Keyword::Class)),
            "clocking" => Ok(KeywordToken::build_token(Keyword::Clocking)),
            "cmos" => Ok(KeywordToken::build_token(Keyword::Cmos)),
            "config" => Ok(KeywordToken::build_token(Keyword::Config)),
            "const" => Ok(KeywordToken::build_token(Keyword::Const)),
            "constraint" => Ok(KeywordToken::build_token(Keyword::Constraint)),
            "context" => Ok(KeywordToken::build_token(Keyword::Context)),
            "continue" => Ok(KeywordToken::build_token(Keyword::Continue)),
            "cover" => Ok(KeywordToken::build_token(Keyword::Cover)),
            "covergroup" => Ok(KeywordToken::build_token(Keyword::Covergroup)),
            "coverpoint" => Ok(KeywordToken::build_token(Keyword::Coverpoint)),
            "cross" => Ok(KeywordToken::build_token(Keyword::Cross)),
            "deassign" => Ok(KeywordToken::build_token(Keyword::Deassign)),
            "default" => Ok(KeywordToken::build_token(Keyword::Default)),
            "defparam" => Ok(KeywordToken::build_token(Keyword::Defparam)),
            "design" => Ok(KeywordToken::build_token(Keyword::Design)),
            "disable" => Ok(KeywordToken::build_token(Keyword::Disable)),
            "do" => Ok(KeywordToken::build_token(Keyword::Do)),
            "edge" => Ok(KeywordToken::build_token(Keyword::Edge)),
            "else" => Ok(KeywordToken::build_token(Keyword::Else)),
            "end" => Ok(KeywordToken::build_token(Keyword::End)),
            "endcase" => Ok(KeywordToken::build_token(Keyword::Endcase)),
            "endchecker" => Ok(KeywordToken::build_token(Keyword::Endchecker)),
            "endclass" => Ok(KeywordToken::build_token(Keyword::Endclass)),
            "endclocking" => Ok(KeywordToken::build_token(Keyword::Endclocking)),
            "endconfig" => Ok(KeywordToken::build_token(Keyword::Endconfig)),
            "endfunction" => Ok(KeywordToken::build_token(Keyword::Endfunction)),
            "endgenerate" => Ok(KeywordToken::build_token(Keyword::Endgenerate)),
            "endgroup" => Ok(KeywordToken::build_token(Keyword::Endgroup)),
            "endinterface" => Ok(KeywordToken::build_token(Keyword::Endinterface)),
            "endmodule" => Ok(KeywordToken::build_token(Keyword::Endmodule)),
            "endpackage" => Ok(KeywordToken::build_token(Keyword::Endpackage)),
            "endprimitive" => Ok(KeywordToken::build_token(Keyword::Endprimitive)),
            "endprogram" => Ok(KeywordToken::build_token(Keyword::Endprogram)),
            "endproperty" => Ok(KeywordToken::build_token(Keyword::Endproperty)),
            "endspecify" => Ok(KeywordToken::build_token(Keyword::Endspecify)),
            "endsequence" => Ok(KeywordToken::build_token(Keyword::Endsequence)),
            "endtable" => Ok(KeywordToken::build_token(Keyword::Endtable)),
            "endtask" => Ok(KeywordToken::build_token(Keyword::Endtask)),
            "enum" => Ok(KeywordToken::build_token(Keyword::Enum)),
            "event" => Ok(KeywordToken::build_token(Keyword::Event)),
            "eventually" => Ok(KeywordToken::build_token(Keyword::Eventually)),
            "expect" => Ok(KeywordToken::build_token(Keyword::Expect)),
            "export" => Ok(KeywordToken::build_token(Keyword::Export)),
            "extends" => Ok(KeywordToken::build_token(Keyword::Extends)),
            "extern" => Ok(KeywordToken::build_token(Keyword::Extern)),
            "final" => Ok(KeywordToken::build_token(Keyword::Final)),
            "first_match" => Ok(KeywordToken::build_token(Keyword::FirstMatch)),
            "for" => Ok(KeywordToken::build_token(Keyword::For)),
            "force" => Ok(KeywordToken::build_token(Keyword::Force)),
            "foreach" => Ok(KeywordToken::build_token(Keyword::Foreach)),
            "forever" => Ok(KeywordToken::build_token(Keyword::Forever)),
            "fork" => Ok(KeywordToken::build_token(Keyword::Fork)),
            "forkjoin" => Ok(KeywordToken::build_token(Keyword::Forkjoin)),
            "function" => Ok(KeywordToken::build_token(Keyword::Function)),
            "generate" => Ok(KeywordToken::build_token(Keyword::Generate)),
            "genvar" => Ok(KeywordToken::build_token(Keyword::Genvar)),
            "global" => Ok(KeywordToken::build_token(Keyword::Global)),
            "highz0" => Ok(KeywordToken::build_token(Keyword::Highz0)),
            "highz1" => Ok(KeywordToken::build_token(Keyword::Highz1)),
            "if" => Ok(KeywordToken::build_token(Keyword::If)),
            "iff" => Ok(KeywordToken::build_token(Keyword::Iff)),
            "ifnone" => Ok(KeywordToken::build_token(Keyword::Ifnone)),
            "ignore_bins" => Ok(KeywordToken::build_token(Keyword::IgnoreBins)),
            "illegal_bins" => Ok(KeywordToken::build_token(Keyword::IllegalBins)),
            "implements" => Ok(KeywordToken::build_token(Keyword::Implements)),
            "implies" => Ok(KeywordToken::build_token(Keyword::Implies)),
            "import" => Ok(KeywordToken::build_token(Keyword::Import)),
            "incdir" => Ok(KeywordToken::build_token(Keyword::Incdir)),
            "include" => Ok(KeywordToken::build_token(Keyword::Include)),
            "initial" => Ok(KeywordToken::build_token(Keyword::Initial)),
            "inout" => Ok(KeywordToken::build_token(Keyword::Inout)),
            "input" => Ok(KeywordToken::build_token(Keyword::Input)),
            "instance" => Ok(KeywordToken::build_token(Keyword::Instance)),
            "int" => Ok(KeywordToken::build_token(Keyword::Int)),
            "integer" => Ok(KeywordToken::build_token(Keyword::Integer)),
            "interconnect" => Ok(KeywordToken::build_token(Keyword::Interconnect)),
            "interface" => Ok(KeywordToken::build_token(Keyword::Interface)),
            "intersect" => Ok(KeywordToken::build_token(Keyword::Intersect)),
            "join" => Ok(KeywordToken::build_token(Keyword::Join)),
            "join_any" => Ok(KeywordToken::build_token(Keyword::JoinAny)),
            "join_none" => Ok(KeywordToken::build_token(Keyword::JoinNone)),
            "large" => Ok(KeywordToken::build_token(Keyword::Large)),
            "let" => Ok(KeywordToken::build_token(Keyword::Let)),
            "liblist" => Ok(KeywordToken::build_token(Keyword::Liblist)),
            "library" => Ok(KeywordToken::build_token(Keyword::Library)),
            "local" => Ok(KeywordToken::build_token(Keyword::Local)),
            "localparam" => Ok(KeywordToken::build_token(Keyword::Localparam)),
            "logic" => Ok(KeywordToken::build_token(Keyword::Logic)),
            "longint" => Ok(KeywordToken::build_token(Keyword::Longint)),
            "macromodule" => Ok(KeywordToken::build_token(Keyword::Macromodule)),
            "matches" => Ok(KeywordToken::build_token(Keyword::Matches)),
            "medium" => Ok(KeywordToken::build_token(Keyword::Medium)),
            "modport" => Ok(KeywordToken::build_token(Keyword::Modport)),
            "module" => Ok(KeywordToken::build_token(Keyword::Module)),
            "nand" => Ok(KeywordToken::build_token(Keyword::Nand)),
            "negedge" => Ok(KeywordToken::build_token(Keyword::Negedge)),
            "nettype" => Ok(KeywordToken::build_token(Keyword::Nettype)),
            "new" => Ok(KeywordToken::build_token(Keyword::New)),
            "nexttime" => Ok(KeywordToken::build_token(Keyword::Nexttime)),
            "nmos" => Ok(KeywordToken::build_token(Keyword::Nmos)),
            "nor" => Ok(KeywordToken::build_token(Keyword::Nor)),
            "noshowcancelled" => Ok(KeywordToken::build_token(Keyword::Noshowcancelled)),
            "not" => Ok(KeywordToken::build_token(Keyword::Not)),
            "notif0" => Ok(KeywordToken::build_token(Keyword::Notif0)),
            "notif1" => Ok(KeywordToken::build_token(Keyword::Notif1)),
            "null" => Ok(KeywordToken::build_token(Keyword::Null)),
            "or" => Ok(KeywordToken::build_token(Keyword::Or)),
            "output" => Ok(KeywordToken::build_token(Keyword::Output)),
            "package" => Ok(KeywordToken::build_token(Keyword::Package)),
            "packed" => Ok(KeywordToken::build_token(Keyword::Packed)),
            "parameter" => Ok(KeywordToken::build_token(Keyword::Parameter)),
            "pmos" => Ok(KeywordToken::build_token(Keyword::Pmos)),
            "posedge" => Ok(KeywordToken::build_token(Keyword::Posedge)),
            "primitive" => Ok(KeywordToken::build_token(Keyword::Primitive)),
            "priority" => Ok(KeywordToken::build_token(Keyword::Priority)),
            "program" => Ok(KeywordToken::build_token(Keyword::Program)),
            "property" => Ok(KeywordToken::build_token(Keyword::Property)),
            "protected" => Ok(KeywordToken::build_token(Keyword::Protected)),
            "pull0" => Ok(KeywordToken::build_token(Keyword::Pull0)),
            "pull1" => Ok(KeywordToken::build_token(Keyword::Pull1)),
            "pulldown" => Ok(KeywordToken::build_token(Keyword::Pulldown)),
            "pullup" => Ok(KeywordToken::build_token(Keyword::Pullup)),
            "pulsestyle_ondetect" => Ok(KeywordToken::build_token(Keyword::PulsestyleOndetect)),
            "pulsestyle_onevent" => Ok(KeywordToken::build_token(Keyword::PulsestyleOnevent)),
            "pure" => Ok(KeywordToken::build_token(Keyword::Pure)),
            "rand" => Ok(KeywordToken::build_token(Keyword::Rand)),
            "randc" => Ok(KeywordToken::build_token(Keyword::Randc)),
            "randcase" => Ok(KeywordToken::build_token(Keyword::Randcase)),
            "randsequence" => Ok(KeywordToken::build_token(Keyword::Randsequence)),
            "rcmos" => Ok(KeywordToken::build_token(Keyword::Rcmos)),
            "real" => Ok(KeywordToken::build_token(Keyword::Real)),
            "realtime" => Ok(KeywordToken::build_token(Keyword::Realtime)),
            "ref" => Ok(KeywordToken::build_token(Keyword::Ref)),
            "reg" => Ok(KeywordToken::build_token(Keyword::Reg)),
            "reject_on" => Ok(KeywordToken::build_token(Keyword::RejectOn)),
            "release" => Ok(KeywordToken::build_token(Keyword::Release)),
            "repeat" => Ok(KeywordToken::build_token(Keyword::Repeat)),
            "restrict" => Ok(KeywordToken::build_token(Keyword::Restrict)),
            "return" => Ok(KeywordToken::build_token(Keyword::Return)),
            "rnmos" => Ok(KeywordToken::build_token(Keyword::Rnmos)),
            "rpmos" => Ok(KeywordToken::build_token(Keyword::Rpmos)),
            "rtran" => Ok(KeywordToken::build_token(Keyword::Rtran)),
            "rtranif0" => Ok(KeywordToken::build_token(Keyword::Rtranif0)),
            "rtranif1" => Ok(KeywordToken::build_token(Keyword::Rtranif1)),
            "s_always" => Ok(KeywordToken::build_token(Keyword::SAlways)),
            "s_eventually" => Ok(KeywordToken::build_token(Keyword::SEventually)),
            "s_nexttime" => Ok(KeywordToken::build_token(Keyword::SNexttime)),
            "s_until" => Ok(KeywordToken::build_token(Keyword::SUntil)),
            "s_until_with" => Ok(KeywordToken::build_token(Keyword::SUntilWith)),
            "scalared" => Ok(KeywordToken::build_token(Keyword::Scalared)),
            "sequence" => Ok(KeywordToken::build_token(Keyword::Sequence)),
            "shortint" => Ok(KeywordToken::build_token(Keyword::Shortint)),
            "shortreal" => Ok(KeywordToken::build_token(Keyword::Shortreal)),
            "showcancelled" => Ok(KeywordToken::build_token(Keyword::Showcancelled)),
            "signed" => Ok(KeywordToken::build_token(Keyword::Signed)),
            "small" => Ok(KeywordToken::build_token(Keyword::Small)),
            "soft" => Ok(KeywordToken::build_token(Keyword::Soft)),
            "solve" => Ok(KeywordToken::build_token(Keyword::Solve)),
            "specify" => Ok(KeywordToken::build_token(Keyword::Specify)),
            "specparam" => Ok(KeywordToken::build_token(Keyword::Specparam)),
            "static" => Ok(KeywordToken::build_token(Keyword::Static)),
            "string" => Ok(KeywordToken::build_token(Keyword::String)),
            "strong" => Ok(KeywordToken::build_token(Keyword::Strong)),
            "strong0" => Ok(KeywordToken::build_token(Keyword::Strong0)),
            "strong1" => Ok(KeywordToken::build_token(Keyword::Strong1)),
            "struct" => Ok(KeywordToken::build_token(Keyword::Struct)),
            "super" => Ok(KeywordToken::build_token(Keyword::Super)),
            "supply0" => Ok(KeywordToken::build_token(Keyword::Supply0)),
            "supply1" => Ok(KeywordToken::build_token(Keyword::Supply1)),
            "sync_accept_on" => Ok(KeywordToken::build_token(Keyword::SyncAcceptOn)),
            "sync_reject_on" => Ok(KeywordToken::build_token(Keyword::SyncRejectOn)),
            "table" => Ok(KeywordToken::build_token(Keyword::Table)),
            "tagged" => Ok(KeywordToken::build_token(Keyword::Tagged)),
            "task" => Ok(KeywordToken::build_token(Keyword::Task)),
            "this" => Ok(KeywordToken::build_token(Keyword::This)),
            "throughout" => Ok(KeywordToken::build_token(Keyword::Throughout)),
            "time" => Ok(KeywordToken::build_token(Keyword::Time)),
            "timeprecision" => Ok(KeywordToken::build_token(Keyword::Timeprecision)),
            "timeunit" => Ok(KeywordToken::build_token(Keyword::Timeunit)),
            "tran" => Ok(KeywordToken::build_token(Keyword::Tran)),
            "tranif0" => Ok(KeywordToken::build_token(Keyword::Tranif0)),
            "tranif1" => Ok(KeywordToken::build_token(Keyword::Tranif1)),
            "tri" => Ok(KeywordToken::build_token(Keyword::Tri)),
            "tri0" => Ok(KeywordToken::build_token(Keyword::Tri0)),
            "tri1" => Ok(KeywordToken::build_token(Keyword::Tri1)),
            "triand" => Ok(KeywordToken::build_token(Keyword::Triand)),
            "trior" => Ok(KeywordToken::build_token(Keyword::Trior)),
            "trireg" => Ok(KeywordToken::build_token(Keyword::Trireg)),
            "type" => Ok(KeywordToken::build_token(Keyword::Type)),
            "typedef" => Ok(KeywordToken::build_token(Keyword::Typedef)),
            "union" => Ok(KeywordToken::build_token(Keyword::Union)),
            "unique" => Ok(KeywordToken::build_token(Keyword::Unique)),
            "unique0" => Ok(KeywordToken::build_token(Keyword::Unique0)),
            "unsigned" => Ok(KeywordToken::build_token(Keyword::Unsigned)),
            "until" => Ok(KeywordToken::build_token(Keyword::Until)),
            "until_with" => Ok(KeywordToken::build_token(Keyword::UntilWith)),
            "untyped" => Ok(KeywordToken::build_token(Keyword::Untyped)),
            "use" => Ok(KeywordToken::build_token(Keyword::Use)),
            "uwire" => Ok(KeywordToken::build_token(Keyword::Uwire)),
            "var" => Ok(KeywordToken::build_token(Keyword::Var)),
            "vectored" => Ok(KeywordToken::build_token(Keyword::Vectored)),
            "virtual" => Ok(KeywordToken::build_token(Keyword::Virtual)),
            "void" => Ok(KeywordToken::build_token(Keyword::Void)),
            "wait" => Ok(KeywordToken::build_token(Keyword::Wait)),
            "wait_order" => Ok(KeywordToken::build_token(Keyword::WaitOrder)),
            "wand" => Ok(KeywordToken::build_token(Keyword::Wand)),
            "weak" => Ok(KeywordToken::build_token(Keyword::Weak)),
            "weak0" => Ok(KeywordToken::build_token(Keyword::Weak0)),
            "weak1" => Ok(KeywordToken::build_token(Keyword::Weak1)),
            "while" => Ok(KeywordToken::build_token(Keyword::While)),
            "wildcard" => Ok(KeywordToken::build_token(Keyword::Wildcard)),
            "wire" => Ok(KeywordToken::build_token(Keyword::Wire)),
            "with" => Ok(KeywordToken::build_token(Keyword::With)),
            "within" => Ok(KeywordToken::build_token(Keyword::Within)),
            "wor" => Ok(KeywordToken::build_token(Keyword::Wor)),
            "xnor" => Ok(KeywordToken::build_token(Keyword::Xnor)),
            "xor" => Ok(KeywordToken::build_token(Keyword::Xor)),
            _ => Err("Unrecognized keyword")
        }
    }
}
