use std::env;
use std::process;

use open_system_verilog::char_reader::CharReader;
use open_system_verilog::compilation_unit::CompilationUnit;
use open_system_verilog::config::Config;

fn main() {
    let config = Config::build(env::args().peekable()).unwrap_or_else(|errors| {
        for error in errors {
            eprintln!("{error}");
        }

        eprintln!("Failed to process arguments");
        process::exit(1);
    });

    let compilation_units = CompilationUnit::from_config(&config);

    for compilation_unit in compilation_units {
        evaluate(&compilation_unit);
    }
}

fn evaluate(compilation_unit: &CompilationUnit) {
    for file_path in compilation_unit.files() {
        let mut lexer = Lexer::open(file_path);
        let tokens = lexer.lex();

        if tokens.is_err() {
            dbg!(&tokens.unwrap_err());
        } else {
            dbg!(&tokens.unwrap());
        }

    }
}

#[derive(Debug)]
enum Token {
    WhiteSpace,
    Comment,
    Number(String),
    StringLiteral(String),
    CharacterSequence(String),
    Operator(Operator),
    Punctuation(Punctuation),
    Keyword(Keyword),
    EOF,
}

// Missing replication and conditional operators ( will be used in parse but not tokenization)
#[derive(Debug)]
enum Operator {
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

#[derive(Debug)]
enum Keyword {
    AcceptOn,
    Alias,
    Always,
    AlwaysComb,
    AlwaysFF,
    AlwaysLatch,
    And,
    Assert,
    Assign,
    Assume,
    Automatic,
    Before,
    Begin,
    Bind,
    Bins,
    Binsof,
    Bit,
    Break,
    Buf,
    Bufif0,
    Bufif1,
    Byte,
    Case,
    Casex,
    Casez,
    Cell,
    Chandle,
    Checker,
    Class,
    Clocking,
    Cmos,
    Config,
    Const,
    Constraint,
    Context,
    Continue,
    Cover,
    Covergroup,
    Coverpoint,
    Cross,
    Deassign,
    Default,
    Defparam,
    Design,
    Disable,
    Do,
    Edge,
    Else,
    End,
    Endcase,
    Endchecker,
    Endclass,
    Endclocking,
    Endconfig,
    Endfunction,
    Endgenerate,
    Endgroup,
    Endinterface,
    Endmodule,
    Endpackage,
    Endprimitive,
    Endprogram,
    Endproperty,
    Endspecify,
    Endsequence,
    Endtable,
    Endtask,
    Enum,
    Event,
    Eventually,
    Expect,
    Export,
    Extends,
    Extern,
    Final,
    FirstMatch,
    For,
    Force,
    Foreach,
    Forever,
    Fork,
    Forkjoin,
    Function,
    Generate,
    Genvar,
    Global,
    Highz0,
    Highz1,
    If,
    Iff,
    Ifnone,
    IgnoreBins,
    IllegalBins,
    Implements,
    Implies,
    Import,
    Incdir,
    Include,
    Initial,
    Inout,
    Input,
    Instance,
    Int,
    Integer,
    Interconnect,
    Interface,
    Intersect,
    Join,
    JoinAny,
    JoinNone,
    Large,
    Let,
    Liblist,
    Library,
    Local,
    Localparam,
    Logic,
    Longint,
    Macromodule,
    Matches,
    Medium,
    Modport,
    Module,
    Nand,
    Negedge,
    Nettype,
    New,
    Nexttime,
    Nmos,
    Nor,
    Noshowcancelled,
    Not,
    Notif0,
    Notif1,
    Null,
    Or,
    Output,
    Package,
    Packed,
    Parameter,
    Pmos,
    Posedge,
    Primitive,
    Priority,
    Program,
    Property,
    Protected,
    Pull0,
    Pull1,
    Pulldown,
    Pullup,
    PulsestyleOndetect,
    PulsestyleOnevent,
    Pure,
    Rand,
    Randc,
    Randcase,
    Randsequence,
    Rcmos,
    Real,
    Realtime,
    Ref,
    Reg,
    RejectOn,
    Release,
    Repeat,
    Restrict,
    Return,
    Rnmos,
    Rpmos,
    Rtran,
    Rtranif0,
    Rtranif1,
    SAlways,
    SEventually,
    SNexttime,
    SUntil,
    SUntilWith,
    Scalared,
    Sequence,
    Shortint,
    Shortreal,
    Showcancelled,
    Signed,
    Small,
    Soft,
    Solve,
    Specify,
    Specparam,
    Static,
    String,
    Strong,
    Strong0,
    Strong1,
    Struct,
    Super,
    Supply0,
    Supply1,
    SyncAcceptOn,
    SyncRejectOn,
    Table,
    Tagged,
    Task,
    This,
    Throughout,
    Time,
    Timeprecision,
    Timeunit,
    Tran,
    Tranif0,
    Tranif1,
    Tri,
    Tri0,
    Tri1,
    Triand,
    Trior,
    Trireg,
    Type,
    Typedef,
    Union,
    Unique,
    Unique0,
    Unsigned,
    Until,
    UntilWith,
    Untyped,
    Use,
    Uwire,
    Var,
    Vectored,
    Virtual,
    Void,
    Wait,
    WaitOrder,
    Wand,
    Weak,
    Weak0,
    Weak1,
    While,
    Wildcard,
    Wire,
    With,
    Within,
    Wor,
    Xnor,
    Xor,
}

#[derive(Debug)]
enum Punctuation {
    Asperand,
    Pound,
    Dollar,
    LeftParentheses,
    RightParentheses,
    RightBracket,
    LeftBracket,
    RightBrace,
    LeftBrace,
    BackSlash,
    Semicolon,
    Colon,
    QuestionMark,
    Backtick,
    Period,
    Comma,
    Apostrophe,
    Underscore,
}

#[derive(Debug)]
enum LexerOperator {
    WhiteSpace,
    Comment,
    Number,
    StringLiteral,
    CharacterSequence,
    Operator,
    Keyword,
    Punctuation,
}

const OPERATORS: [&'static str; 50] = [
    "+", "-", "!", "~", "&", "~&", "|", "~|", "^", "~^", "^~", "++", "--", "**", "*", "/", "%",
    ">>", "<<", ">>>", "<<<", "<", "<=", ">", ">=", "inside", "dist", "==", "!=", "===", "!==",
    "==?", "!=?", "&&", "||", "->", "<->", "=", "+=", "-=", "*=", "/=", "%=", "&=", "^=", "|=",
    "<<=", ">>=", "<<<=", ">>>=",
];

const KEYWORDS: [&'static str; 246] = [
    "accept_on",
    "alias",
    "always",
    "always_comb",
    "always_ff",
    "always_latch",
    "and",
    "assert",
    "assign",
    "assume",
    "automatic",
    "before",
    "begin",
    "bind",
    "bins",
    "binsof",
    "bit",
    "break",
    "buf",
    "bufif0",
    "bufif1",
    "byte",
    "case",
    "casex",
    "casez",
    "cell",
    "chandle",
    "checker",
    "class",
    "clocking",
    "cmos",
    "config",
    "const",
    "constraint",
    "context",
    "continue",
    "cover",
    "covergroup",
    "coverpoint",
    "cross",
    "deassign",
    "default",
    "defparam",
    "design",
    "disable",
    "do",
    "edge",
    "else",
    "end",
    "endcase",
    "endchecker",
    "endclass",
    "endclocking",
    "endconfig",
    "endfunction",
    "endgenerate",
    "endgroup",
    "endinterface",
    "endmodule",
    "endpackage",
    "endprimitive",
    "endprogram",
    "endproperty",
    "endspecify",
    "endsequence",
    "endtable",
    "endtask",
    "enum",
    "event",
    "eventually",
    "expect",
    "export",
    "extends",
    "extern",
    "final",
    "first_match",
    "for",
    "force",
    "foreach",
    "forever",
    "fork",
    "forkjoin",
    "function",
    "generate",
    "genvar",
    "global",
    "highz0",
    "highz1",
    "if",
    "iff",
    "ifnone",
    "ignore_bins",
    "illegal_bins",
    "implements",
    "implies",
    "import",
    "incdir",
    "include",
    "initial",
    "inout",
    "input",
    "instance",
    "int",
    "integer",
    "interconnect",
    "interface",
    "intersect",
    "join",
    "join_any",
    "join_none",
    "large",
    "let",
    "liblist",
    "library",
    "local",
    "localparam",
    "logic",
    "longint",
    "macromodule",
    "matches",
    "medium",
    "modport",
    "module",
    "nand",
    "negedge",
    "nettype",
    "new",
    "nexttime",
    "nmos",
    "nor",
    "noshowcancelled",
    "not",
    "notif0",
    "notif1",
    "null",
    "or",
    "output",
    "package",
    "packed",
    "parameter",
    "pmos",
    "posedge",
    "primitive",
    "priority",
    "program",
    "property",
    "protected",
    "pull0",
    "pull1",
    "pulldown",
    "pullup",
    "pulsestyle_ondetect",
    "pulsestyle_onevent",
    "pure",
    "rand",
    "randc",
    "randcase",
    "randsequence",
    "rcmos",
    "real",
    "realtime",
    "ref",
    "reg",
    "reject_on",
    "release",
    "repeat",
    "restrict",
    "return",
    "rnmos",
    "rpmos",
    "rtran",
    "rtranif0",
    "rtranif1",
    "s_always",
    "s_eventually",
    "s_nexttime",
    "s_until",
    "s_until_with",
    "scalared",
    "sequence",
    "shortint",
    "shortreal",
    "showcancelled",
    "signed",
    "small",
    "soft",
    "solve",
    "specify",
    "specparam",
    "static",
    "string",
    "strong",
    "strong0",
    "strong1",
    "struct",
    "super",
    "supply0",
    "supply1",
    "sync_accept_on",
    "sync_reject_on",
    "table",
    "tagged",
    "task",
    "this",
    "throughout",
    "time",
    "timeprecision",
    "timeunit",
    "tran",
    "tranif0",
    "tranif1",
    "tri",
    "tri0",
    "tri1",
    "triand",
    "trior",
    "trireg",
    "type",
    "typedef",
    "union",
    "unique",
    "unique0",
    "unsigned",
    "until",
    "until_with",
    "untyped",
    "use",
    "uwire",
    "var",
    "vectored",
    "virtual",
    "void",
    "wait",
    "wait_order",
    "wand",
    "weak",
    "weak0",
    "weak1",
    "while",
    "wildcard",
    "wire",
    "with",
    "within",
    "wor",
    "xnor",
    "xor",
];

struct Lexer {
    char_reader: CharReader,
    marked_position: Option<usize>,
}

#[derive(Debug)]
struct TokenScore {
    token: Token,
    position: usize,
}

#[derive(Debug)]
struct ErrorScore {
    error: String,
    position: usize,
}

impl Lexer {
    fn open(file_path: &String) -> Lexer {
        Lexer {
            char_reader: CharReader::open(file_path),
            marked_position: None,
        }
    }

    fn peek(&mut self) -> Result<char, String> {
        match self.char_reader.peek_char() {
            None => Err(String::from("End of file")),
            Some(ch) => Ok(ch),
        }
    }

    fn read(&mut self) -> Result<char, String> {
        match self.char_reader.read_char() {
            None => Err(String::from("End of file")),
            Some(ch) => Ok(ch),
        }
    }

    fn mark(&mut self) {
        self.marked_position = Some(self.char_reader.get_position());
    }

    fn go_to_mark(&mut self) {
        if self.marked_position.is_none() {
            return;
        }

        self.char_reader
            .seek_from_start(self.marked_position.unwrap());
    }

    fn lex(&mut self) -> Result<Vec<Token>, Vec<String>> {
        let mut tokens = Vec::new();
        let mut errors: Vec<String> = Vec::new();

        // TODO: probably a simpler expression exists for what I am trying to do here
        while tokens.len() == 0 || !matches!(tokens.last().unwrap(), Token::EOF) {
            let token = self.lex_token();

            match token {
                Ok(Token::WhiteSpace) | Ok(Token::Comment) => continue,
                Err(message) => errors.push(message),
                Ok(token) => tokens.push(token),
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }

        Ok(tokens)
    }

    fn execute_lexical_operation(
        &mut self,
        operation: LexerOperator,
        token_score: &mut TokenScore,
        error_score: &mut ErrorScore,
    ) {
        self.mark();
        let token = match operation {
            LexerOperator::WhiteSpace => self.lex_white_space(),
            LexerOperator::Comment => self.lex_comments(),
            LexerOperator::Number => self.lex_number(),
            LexerOperator::StringLiteral => self.lex_string_literal(),
            LexerOperator::CharacterSequence => self.lex_character_sequence(),
            LexerOperator::Operator => self.lex_operator(),
            LexerOperator::Keyword => self.lex_keyword(),
            LexerOperator::Punctuation => self.lex_punctuation(),
        };
        let position = self.char_reader.get_position();
        self.go_to_mark();

        if let Err(error) = token {
            if error_score.position < position {
                error_score.position = position;
                error_score.error = error;
            }
        } else {
            if token_score.position <= position {
                token_score.position = position;
                token_score.token = token.unwrap();
            }
        }
    }

    // TODO:
    // 2. Convert from String -> &str or &'static str
    fn lex_token(&mut self) -> Result<Token, String> {
        if self.is_at_eof() {
            return Ok(Token::EOF);
        }

        let mut token_score = TokenScore {
            position: 0,
            token: Token::EOF,
        };
        let mut error_score = ErrorScore {
            position: 0,
            error: String::new(),
        };

        self.execute_lexical_operation(
            LexerOperator::WhiteSpace,
            &mut token_score,
            &mut error_score,
        );
        self.execute_lexical_operation(LexerOperator::Comment, &mut token_score, &mut error_score);
        self.execute_lexical_operation(LexerOperator::Number, &mut token_score, &mut error_score);
        self.execute_lexical_operation(
            LexerOperator::StringLiteral,
            &mut token_score,
            &mut error_score,
        );
        self.execute_lexical_operation(
            LexerOperator::CharacterSequence,
            &mut token_score,
            &mut error_score,
        );
        self.execute_lexical_operation(LexerOperator::Operator, &mut token_score, &mut error_score);
        self.execute_lexical_operation(LexerOperator::Keyword, &mut token_score, &mut error_score);
        self.execute_lexical_operation(
            LexerOperator::Punctuation,
            &mut token_score,
            &mut error_score,
        );

        if token_score.position > 0 {
            self.char_reader.seek_from_start(token_score.position);
            return Ok(token_score.token);
        }

        if error_score.position > 0 {
            self.char_reader.seek_from_start(error_score.position);
            return Err(error_score.error);
        }

        Err(String::from("Failed to read any characters"))
    }

    fn is_at_eof(&mut self) -> bool {
        self.char_reader.peek_char().is_none()
    }

    fn lex_white_space(&mut self) -> Result<Token, String> {
        if !self.read()?.is_whitespace() {
            return Err(String::from("Not a sequence of white space characters"));
        }

        while !self.is_at_eof() && self.peek()?.is_whitespace() {
            self.read()?;
        }

        Ok(Token::WhiteSpace)
    }

    fn lex_comments(&mut self) -> Result<Token, String> {
        if self.read()? != '/' {
            return Err(String::from("Does not start with slash"));
        }

        match self.read()? {
            '/' => self.lex_line_comment(),
            '*' => self.lex_block_comment(),
            _ => Err(String::from("Slash is not followed by slash or astrix")),
        }
    }

    fn lex_line_comment(&mut self) -> Result<Token, String> {
        while self.read()? != '\n' {}

        Ok(Token::Comment)
    }

    fn lex_block_comment(&mut self) -> Result<Token, String> {
        while !(self.read()? == '*' && self.peek()? == '/') {}

        self.read()?;

        Ok(Token::Comment)
    }

    fn lex_number(&mut self) -> Result<Token, String> {
        let mut number = String::new();

        while !self.is_at_eof() && self.peek()?.is_digit(10) {
            number.push(self.read()?);
        }

        if number.is_empty() {
            return Err(String::from("Not a number"));
        }

        Ok(Token::Number(number))
    }

    fn lex_string_literal(&mut self) -> Result<Token, String> {
        let mut string_literal = String::new();

        if self.read()? != '\"' {
            return Err(String::from("String literal must start with \""));
        }

        while !self.is_at_eof() && self.peek()? != '"' {
            let ch = self.read()?;
            match ch {
                '\\' => string_literal.push(self.read_escaped_character()?),
                _ => string_literal.push(ch),
            }
        }

        if self.is_at_eof() {
            return Err(String::from("String literal is never closed"));
        }

        self.read()?;

        Ok(Token::StringLiteral(string_literal))
    }

    fn read_escaped_character(&mut self) -> Result<char, String> {
        match self.read() {
            Err(_) => return Err(String::from("String literal is never closed")),
            Ok('"') => Ok('"'),
            Ok('t') => Ok('\t'),
            Ok('n') => Ok('\n'),
            _ => Ok(' '),
        }
    }

    fn lex_character_sequence(&mut self) -> Result<Token, String> {
        return match self.peek()? {
            '\\' => self.lex_escaped_identifier(),
            _ => self.lex_simple_identifier(),
        };
    }

    fn lex_escaped_identifier(&mut self) -> Result<Token, String> {
        let mut escaped_identifier = String::new();
        escaped_identifier.push(self.read()?); // Read the \

        while !self.peek()?.is_whitespace() {
            escaped_identifier.push(self.read()?);
        }

        if escaped_identifier.len() == 1 {
            return Err(String::from("Escaped identifier must not empty"));
        }

        Ok(Token::CharacterSequence(escaped_identifier))
    }

    fn lex_simple_identifier(&mut self) -> Result<Token, String> {
        let mut character_sequence = String::from("");

        while self.peek()?.is_alphabetic() {
            character_sequence.push(self.read()?);
        }

        if character_sequence.is_empty() {
            return Err(String::from("Not a character sequence"));
        }

        Ok(Token::CharacterSequence(character_sequence))
    }

    fn lex_operator(&mut self) -> Result<Token, String> {
        match self.get_best_sequence(&OPERATORS) {
            Some("+") => Ok(Token::Operator(Operator::Addition)),
            Some("-") => Ok(Token::Operator(Operator::Subtraction)),
            Some("!") => Ok(Token::Operator(Operator::Not)),
            Some("~") => Ok(Token::Operator(Operator::Negation)),
            Some("&") => Ok(Token::Operator(Operator::BitwiseAnd)),
            Some("~&") => Ok(Token::Operator(Operator::Nand)),
            Some("|") => Ok(Token::Operator(Operator::BitwiseOr)),
            Some("~|") => Ok(Token::Operator(Operator::Nor)),
            Some("^") => Ok(Token::Operator(Operator::Xor)),
            Some("~^") => Ok(Token::Operator(Operator::Xnor)),
            Some("^~") => Ok(Token::Operator(Operator::Xnor)),
            Some("++") => Ok(Token::Operator(Operator::Increment)),
            Some("--") => Ok(Token::Operator(Operator::Decrement)),
            Some("**") => Ok(Token::Operator(Operator::Exponentiation)),
            Some("*") => Ok(Token::Operator(Operator::Multiplication)),
            Some("/") => Ok(Token::Operator(Operator::Division)),
            Some("%") => Ok(Token::Operator(Operator::Modulo)),
            Some(">>") => Ok(Token::Operator(Operator::ArithmeticRightShift)),
            Some("<<") => Ok(Token::Operator(Operator::ArithmeticLeftShift)),
            Some(">>>") => Ok(Token::Operator(Operator::LogicalRightShift)),
            Some("<<<") => Ok(Token::Operator(Operator::LogicalLeftShift)),
            Some("<") => Ok(Token::Operator(Operator::LessThan)),
            Some("<=") => Ok(Token::Operator(Operator::LessThanOrEqualTo)),
            Some(">") => Ok(Token::Operator(Operator::GreaterThan)),
            Some(">=") => Ok(Token::Operator(Operator::GreaterThanOrEqualTo)),
            Some("inside") => Ok(Token::Operator(Operator::Inside)),
            Some("dist") => Ok(Token::Operator(Operator::Distribution)),
            Some("==") => Ok(Token::Operator(Operator::LogicalEquality)),
            Some("!=") => Ok(Token::Operator(Operator::LogicalInequality)),
            Some("===") => Ok(Token::Operator(Operator::CaseEquality)),
            Some("!==") => Ok(Token::Operator(Operator::CaseInequality)),
            Some("==?") => Ok(Token::Operator(Operator::WildcardEquality)),
            Some("!=?") => Ok(Token::Operator(Operator::WildcardInequality)),
            Some("&&") => Ok(Token::Operator(Operator::LogicalAnd)),
            Some("||") => Ok(Token::Operator(Operator::LogicalOr)),
            Some("->") => Ok(Token::Operator(Operator::Implication)),
            Some("<->") => Ok(Token::Operator(Operator::Equivalence)),
            Some("=") => Ok(Token::Operator(Operator::BinaryAssignment)),
            Some("+=") => Ok(Token::Operator(Operator::AdditionAssignment)),
            Some("-=") => Ok(Token::Operator(Operator::SubtractionAssignment)),
            Some("*=") => Ok(Token::Operator(Operator::MultiplcationAssignment)),
            Some("/=") => Ok(Token::Operator(Operator::DivisionAssignment)),
            Some("%=") => Ok(Token::Operator(Operator::ModuloAssignment)),
            Some("&=") => Ok(Token::Operator(Operator::BitwiseAndAssignment)),
            Some("^=") => Ok(Token::Operator(Operator::BitwiseXorAssignment)),
            Some("|=") => Ok(Token::Operator(Operator::BitwiseOrAssignment)),
            Some("<<=") => Ok(Token::Operator(Operator::ArithmeticLeftShiftAssignment)),
            Some(">>=") => Ok(Token::Operator(Operator::ArithmeticRightShiftAssignment)),
            Some("<<<=") => Ok(Token::Operator(Operator::LogicalLeftShiftAssignment)),
            Some(">>>=") => Ok(Token::Operator(Operator::LogicalRightShiftAssignment)),
            _ => Err(String::from("Unrecognized operator")),
        }
    }

    fn get_best_sequence(&mut self, sequences: &[&'static str]) -> Option<&'static str> {
        let matched_sequences: Vec<&'static str> = sequences
            .iter()
            .map(|op| {
                self.mark();
                let sequence = self.read_sequence(op);
                self.go_to_mark();

                sequence
            })
            .filter(|seq| seq.is_ok())
            .map(|seq| seq.unwrap())
            .collect();

        if matched_sequences.is_empty() {
            return None;
        }

        let mut best_sequence = matched_sequences[0];

        for operator in matched_sequences {
            if best_sequence.len() < operator.len() {
                best_sequence = operator;
            }
        }

        let next_position = self.char_reader.get_position() + best_sequence.len();
        self.char_reader.seek_from_start(next_position);

        Some(best_sequence)
    }

    fn read_sequence(&mut self, sequence: &'static str) -> Result<&'static str, String> {
        for sequence_char in sequence.chars() {
            if self.read()? != sequence_char {
                return Err(String::from("Char did not match"));
            }
        }

        Ok(sequence)
    }

    fn lex_keyword(&mut self) -> Result<Token, String> {
        match self.get_best_sequence(&KEYWORDS) {
            Some("accept_on") => Ok(Token::Keyword(Keyword::AcceptOn)),
            Some("alias") => Ok(Token::Keyword(Keyword::Alias)),
            Some("always") => Ok(Token::Keyword(Keyword::Always)),
            Some("always_comb") => Ok(Token::Keyword(Keyword::AlwaysComb)),
            Some("always_ff") => Ok(Token::Keyword(Keyword::AlwaysFF)),
            Some("always_latch") => Ok(Token::Keyword(Keyword::AlwaysLatch)),
            Some("and") => Ok(Token::Keyword(Keyword::And)),
            Some("assert") => Ok(Token::Keyword(Keyword::Assert)),
            Some("assign") => Ok(Token::Keyword(Keyword::Assign)),
            Some("assume") => Ok(Token::Keyword(Keyword::Assume)),
            Some("automatic") => Ok(Token::Keyword(Keyword::Automatic)),
            Some("before") => Ok(Token::Keyword(Keyword::Before)),
            Some("begin") => Ok(Token::Keyword(Keyword::Begin)),
            Some("bind") => Ok(Token::Keyword(Keyword::Bind)),
            Some("bins") => Ok(Token::Keyword(Keyword::Bins)),
            Some("binsof") => Ok(Token::Keyword(Keyword::Binsof)),
            Some("bit") => Ok(Token::Keyword(Keyword::Bit)),
            Some("break") => Ok(Token::Keyword(Keyword::Break)),
            Some("buf") => Ok(Token::Keyword(Keyword::Buf)),
            Some("bufif0") => Ok(Token::Keyword(Keyword::Bufif0)),
            Some("bufif1") => Ok(Token::Keyword(Keyword::Bufif1)),
            Some("byte") => Ok(Token::Keyword(Keyword::Byte)),
            Some("case") => Ok(Token::Keyword(Keyword::Case)),
            Some("casex") => Ok(Token::Keyword(Keyword::Casex)),
            Some("casez") => Ok(Token::Keyword(Keyword::Casez)),
            Some("cell") => Ok(Token::Keyword(Keyword::Cell)),
            Some("chandle") => Ok(Token::Keyword(Keyword::Chandle)),
            Some("checker") => Ok(Token::Keyword(Keyword::Checker)),
            Some("class") => Ok(Token::Keyword(Keyword::Class)),
            Some("clocking") => Ok(Token::Keyword(Keyword::Clocking)),
            Some("cmos") => Ok(Token::Keyword(Keyword::Cmos)),
            Some("config") => Ok(Token::Keyword(Keyword::Config)),
            Some("const") => Ok(Token::Keyword(Keyword::Const)),
            Some("constraint") => Ok(Token::Keyword(Keyword::Constraint)),
            Some("context") => Ok(Token::Keyword(Keyword::Context)),
            Some("continue") => Ok(Token::Keyword(Keyword::Continue)),
            Some("cover") => Ok(Token::Keyword(Keyword::Cover)),
            Some("covergroup") => Ok(Token::Keyword(Keyword::Covergroup)),
            Some("coverpoint") => Ok(Token::Keyword(Keyword::Coverpoint)),
            Some("cross") => Ok(Token::Keyword(Keyword::Cross)),
            Some("deassign") => Ok(Token::Keyword(Keyword::Deassign)),
            Some("default") => Ok(Token::Keyword(Keyword::Default)),
            Some("defparam") => Ok(Token::Keyword(Keyword::Defparam)),
            Some("design") => Ok(Token::Keyword(Keyword::Design)),
            Some("disable") => Ok(Token::Keyword(Keyword::Disable)),
            Some("do") => Ok(Token::Keyword(Keyword::Do)),
            Some("edge") => Ok(Token::Keyword(Keyword::Edge)),
            Some("else") => Ok(Token::Keyword(Keyword::Else)),
            Some("end") => Ok(Token::Keyword(Keyword::End)),
            Some("endcase") => Ok(Token::Keyword(Keyword::Endcase)),
            Some("endchecker") => Ok(Token::Keyword(Keyword::Endchecker)),
            Some("endclass") => Ok(Token::Keyword(Keyword::Endclass)),
            Some("endclocking") => Ok(Token::Keyword(Keyword::Endclocking)),
            Some("endconfig") => Ok(Token::Keyword(Keyword::Endconfig)),
            Some("endfunction") => Ok(Token::Keyword(Keyword::Endfunction)),
            Some("endgenerate") => Ok(Token::Keyword(Keyword::Endgenerate)),
            Some("endgroup") => Ok(Token::Keyword(Keyword::Endgroup)),
            Some("endinterface") => Ok(Token::Keyword(Keyword::Endinterface)),
            Some("endmodule") => Ok(Token::Keyword(Keyword::Endmodule)),
            Some("endpackage") => Ok(Token::Keyword(Keyword::Endpackage)),
            Some("endprimitive") => Ok(Token::Keyword(Keyword::Endprimitive)),
            Some("endprogram") => Ok(Token::Keyword(Keyword::Endprogram)),
            Some("endproperty") => Ok(Token::Keyword(Keyword::Endproperty)),
            Some("endspecify") => Ok(Token::Keyword(Keyword::Endspecify)),
            Some("endsequence") => Ok(Token::Keyword(Keyword::Endsequence)),
            Some("endtable") => Ok(Token::Keyword(Keyword::Endtable)),
            Some("endtask") => Ok(Token::Keyword(Keyword::Endtask)),
            Some("enum") => Ok(Token::Keyword(Keyword::Enum)),
            Some("event") => Ok(Token::Keyword(Keyword::Event)),
            Some("eventually") => Ok(Token::Keyword(Keyword::Eventually)),
            Some("expect") => Ok(Token::Keyword(Keyword::Expect)),
            Some("export") => Ok(Token::Keyword(Keyword::Export)),
            Some("extends") => Ok(Token::Keyword(Keyword::Extends)),
            Some("extern") => Ok(Token::Keyword(Keyword::Extern)),
            Some("final") => Ok(Token::Keyword(Keyword::Final)),
            Some("first_match") => Ok(Token::Keyword(Keyword::FirstMatch)),
            Some("for") => Ok(Token::Keyword(Keyword::For)),
            Some("force") => Ok(Token::Keyword(Keyword::Force)),
            Some("foreach") => Ok(Token::Keyword(Keyword::Foreach)),
            Some("forever") => Ok(Token::Keyword(Keyword::Forever)),
            Some("fork") => Ok(Token::Keyword(Keyword::Fork)),
            Some("forkjoin") => Ok(Token::Keyword(Keyword::Forkjoin)),
            Some("function") => Ok(Token::Keyword(Keyword::Function)),
            Some("generate") => Ok(Token::Keyword(Keyword::Generate)),
            Some("genvar") => Ok(Token::Keyword(Keyword::Genvar)),
            Some("global") => Ok(Token::Keyword(Keyword::Global)),
            Some("highz0") => Ok(Token::Keyword(Keyword::Highz0)),
            Some("highz1") => Ok(Token::Keyword(Keyword::Highz1)),
            Some("if") => Ok(Token::Keyword(Keyword::If)),
            Some("iff") => Ok(Token::Keyword(Keyword::Iff)),
            Some("ifnone") => Ok(Token::Keyword(Keyword::Ifnone)),
            Some("ignore_bins") => Ok(Token::Keyword(Keyword::IgnoreBins)),
            Some("illegal_bins") => Ok(Token::Keyword(Keyword::IllegalBins)),
            Some("implements") => Ok(Token::Keyword(Keyword::Implements)),
            Some("implies") => Ok(Token::Keyword(Keyword::Implies)),
            Some("import") => Ok(Token::Keyword(Keyword::Import)),
            Some("incdir") => Ok(Token::Keyword(Keyword::Incdir)),
            Some("include") => Ok(Token::Keyword(Keyword::Include)),
            Some("initial") => Ok(Token::Keyword(Keyword::Initial)),
            Some("inout") => Ok(Token::Keyword(Keyword::Inout)),
            Some("input") => Ok(Token::Keyword(Keyword::Input)),
            Some("instance") => Ok(Token::Keyword(Keyword::Instance)),
            Some("int") => Ok(Token::Keyword(Keyword::Int)),
            Some("integer") => Ok(Token::Keyword(Keyword::Integer)),
            Some("interconnect") => Ok(Token::Keyword(Keyword::Interconnect)),
            Some("interface") => Ok(Token::Keyword(Keyword::Interface)),
            Some("intersect") => Ok(Token::Keyword(Keyword::Intersect)),
            Some("join") => Ok(Token::Keyword(Keyword::Join)),
            Some("join_any") => Ok(Token::Keyword(Keyword::JoinAny)),
            Some("join_none") => Ok(Token::Keyword(Keyword::JoinNone)),
            Some("large") => Ok(Token::Keyword(Keyword::Large)),
            Some("let") => Ok(Token::Keyword(Keyword::Let)),
            Some("liblist") => Ok(Token::Keyword(Keyword::Liblist)),
            Some("library") => Ok(Token::Keyword(Keyword::Library)),
            Some("local") => Ok(Token::Keyword(Keyword::Local)),
            Some("localparam") => Ok(Token::Keyword(Keyword::Localparam)),
            Some("logic") => Ok(Token::Keyword(Keyword::Logic)),
            Some("longint") => Ok(Token::Keyword(Keyword::Longint)),
            Some("macromodule") => Ok(Token::Keyword(Keyword::Macromodule)),
            Some("matches") => Ok(Token::Keyword(Keyword::Matches)),
            Some("medium") => Ok(Token::Keyword(Keyword::Medium)),
            Some("modport") => Ok(Token::Keyword(Keyword::Modport)),
            Some("module") => Ok(Token::Keyword(Keyword::Module)),
            Some("nand") => Ok(Token::Keyword(Keyword::Nand)),
            Some("negedge") => Ok(Token::Keyword(Keyword::Negedge)),
            Some("nettype") => Ok(Token::Keyword(Keyword::Nettype)),
            Some("new") => Ok(Token::Keyword(Keyword::New)),
            Some("nexttime") => Ok(Token::Keyword(Keyword::Nexttime)),
            Some("nmos") => Ok(Token::Keyword(Keyword::Nmos)),
            Some("nor") => Ok(Token::Keyword(Keyword::Nor)),
            Some("noshowcancelled") => Ok(Token::Keyword(Keyword::Noshowcancelled)),
            Some("not") => Ok(Token::Keyword(Keyword::Not)),
            Some("notif0") => Ok(Token::Keyword(Keyword::Notif0)),
            Some("notif1") => Ok(Token::Keyword(Keyword::Notif1)),
            Some("null") => Ok(Token::Keyword(Keyword::Null)),
            Some("or") => Ok(Token::Keyword(Keyword::Or)),
            Some("output") => Ok(Token::Keyword(Keyword::Output)),
            Some("package") => Ok(Token::Keyword(Keyword::Package)),
            Some("packed") => Ok(Token::Keyword(Keyword::Packed)),
            Some("parameter") => Ok(Token::Keyword(Keyword::Parameter)),
            Some("pmos") => Ok(Token::Keyword(Keyword::Pmos)),
            Some("posedge") => Ok(Token::Keyword(Keyword::Posedge)),
            Some("primitive") => Ok(Token::Keyword(Keyword::Primitive)),
            Some("priority") => Ok(Token::Keyword(Keyword::Priority)),
            Some("program") => Ok(Token::Keyword(Keyword::Program)),
            Some("property") => Ok(Token::Keyword(Keyword::Property)),
            Some("protected") => Ok(Token::Keyword(Keyword::Protected)),
            Some("pull0") => Ok(Token::Keyword(Keyword::Pull0)),
            Some("pull1") => Ok(Token::Keyword(Keyword::Pull1)),
            Some("pulldown") => Ok(Token::Keyword(Keyword::Pulldown)),
            Some("pullup") => Ok(Token::Keyword(Keyword::Pullup)),
            Some("pulsestyle_ondetect") => Ok(Token::Keyword(Keyword::PulsestyleOndetect)),
            Some("pulsestyle_onevent") => Ok(Token::Keyword(Keyword::PulsestyleOnevent)),
            Some("pure") => Ok(Token::Keyword(Keyword::Pure)),
            Some("rand") => Ok(Token::Keyword(Keyword::Rand)),
            Some("randc") => Ok(Token::Keyword(Keyword::Randc)),
            Some("randcase") => Ok(Token::Keyword(Keyword::Randcase)),
            Some("randsequence") => Ok(Token::Keyword(Keyword::Randsequence)),
            Some("rcmos") => Ok(Token::Keyword(Keyword::Rcmos)),
            Some("real") => Ok(Token::Keyword(Keyword::Real)),
            Some("realtime") => Ok(Token::Keyword(Keyword::Realtime)),
            Some("ref") => Ok(Token::Keyword(Keyword::Ref)),
            Some("reg") => Ok(Token::Keyword(Keyword::Reg)),
            Some("reject_on") => Ok(Token::Keyword(Keyword::RejectOn)),
            Some("release") => Ok(Token::Keyword(Keyword::Release)),
            Some("repeat") => Ok(Token::Keyword(Keyword::Repeat)),
            Some("restrict") => Ok(Token::Keyword(Keyword::Restrict)),
            Some("return") => Ok(Token::Keyword(Keyword::Return)),
            Some("rnmos") => Ok(Token::Keyword(Keyword::Rnmos)),
            Some("rpmos") => Ok(Token::Keyword(Keyword::Rpmos)),
            Some("rtran") => Ok(Token::Keyword(Keyword::Rtran)),
            Some("rtranif0") => Ok(Token::Keyword(Keyword::Rtranif0)),
            Some("rtranif1") => Ok(Token::Keyword(Keyword::Rtranif1)),
            Some("s_always") => Ok(Token::Keyword(Keyword::SAlways)),
            Some("s_eventually") => Ok(Token::Keyword(Keyword::SEventually)),
            Some("s_nexttime") => Ok(Token::Keyword(Keyword::SNexttime)),
            Some("s_until") => Ok(Token::Keyword(Keyword::SUntil)),
            Some("s_until_with") => Ok(Token::Keyword(Keyword::SUntilWith)),
            Some("scalared") => Ok(Token::Keyword(Keyword::Scalared)),
            Some("sequence") => Ok(Token::Keyword(Keyword::Sequence)),
            Some("shortint") => Ok(Token::Keyword(Keyword::Shortint)),
            Some("shortreal") => Ok(Token::Keyword(Keyword::Shortreal)),
            Some("showcancelled") => Ok(Token::Keyword(Keyword::Showcancelled)),
            Some("signed") => Ok(Token::Keyword(Keyword::Signed)),
            Some("small") => Ok(Token::Keyword(Keyword::Small)),
            Some("soft") => Ok(Token::Keyword(Keyword::Soft)),
            Some("solve") => Ok(Token::Keyword(Keyword::Solve)),
            Some("specify") => Ok(Token::Keyword(Keyword::Specify)),
            Some("specparam") => Ok(Token::Keyword(Keyword::Specparam)),
            Some("static") => Ok(Token::Keyword(Keyword::Static)),
            Some("string") => Ok(Token::Keyword(Keyword::String)),
            Some("strong") => Ok(Token::Keyword(Keyword::Strong)),
            Some("strong0") => Ok(Token::Keyword(Keyword::Strong0)),
            Some("strong1") => Ok(Token::Keyword(Keyword::Strong1)),
            Some("struct") => Ok(Token::Keyword(Keyword::Struct)),
            Some("super") => Ok(Token::Keyword(Keyword::Super)),
            Some("supply0") => Ok(Token::Keyword(Keyword::Supply0)),
            Some("supply1") => Ok(Token::Keyword(Keyword::Supply1)),
            Some("sync_accept_on") => Ok(Token::Keyword(Keyword::SyncAcceptOn)),
            Some("sync_reject_on") => Ok(Token::Keyword(Keyword::SyncRejectOn)),
            Some("table") => Ok(Token::Keyword(Keyword::Table)),
            Some("tagged") => Ok(Token::Keyword(Keyword::Tagged)),
            Some("task") => Ok(Token::Keyword(Keyword::Task)),
            Some("this") => Ok(Token::Keyword(Keyword::This)),
            Some("throughout") => Ok(Token::Keyword(Keyword::Throughout)),
            Some("time") => Ok(Token::Keyword(Keyword::Time)),
            Some("timeprecision") => Ok(Token::Keyword(Keyword::Timeprecision)),
            Some("timeunit") => Ok(Token::Keyword(Keyword::Timeunit)),
            Some("tran") => Ok(Token::Keyword(Keyword::Tran)),
            Some("tranif0") => Ok(Token::Keyword(Keyword::Tranif0)),
            Some("tranif1") => Ok(Token::Keyword(Keyword::Tranif1)),
            Some("tri") => Ok(Token::Keyword(Keyword::Tri)),
            Some("tri0") => Ok(Token::Keyword(Keyword::Tri0)),
            Some("tri1") => Ok(Token::Keyword(Keyword::Tri1)),
            Some("triand") => Ok(Token::Keyword(Keyword::Triand)),
            Some("trior") => Ok(Token::Keyword(Keyword::Trior)),
            Some("trireg") => Ok(Token::Keyword(Keyword::Trireg)),
            Some("type") => Ok(Token::Keyword(Keyword::Type)),
            Some("typedef") => Ok(Token::Keyword(Keyword::Typedef)),
            Some("union") => Ok(Token::Keyword(Keyword::Union)),
            Some("unique") => Ok(Token::Keyword(Keyword::Unique)),
            Some("unique0") => Ok(Token::Keyword(Keyword::Unique0)),
            Some("unsigned") => Ok(Token::Keyword(Keyword::Unsigned)),
            Some("until") => Ok(Token::Keyword(Keyword::Until)),
            Some("until_with") => Ok(Token::Keyword(Keyword::UntilWith)),
            Some("untyped") => Ok(Token::Keyword(Keyword::Untyped)),
            Some("use") => Ok(Token::Keyword(Keyword::Use)),
            Some("uwire") => Ok(Token::Keyword(Keyword::Uwire)),
            Some("var") => Ok(Token::Keyword(Keyword::Var)),
            Some("vectored") => Ok(Token::Keyword(Keyword::Vectored)),
            Some("virtual") => Ok(Token::Keyword(Keyword::Virtual)),
            Some("void") => Ok(Token::Keyword(Keyword::Void)),
            Some("wait") => Ok(Token::Keyword(Keyword::Wait)),
            Some("wait_order") => Ok(Token::Keyword(Keyword::WaitOrder)),
            Some("wand") => Ok(Token::Keyword(Keyword::Wand)),
            Some("weak") => Ok(Token::Keyword(Keyword::Weak)),
            Some("weak0") => Ok(Token::Keyword(Keyword::Weak0)),
            Some("weak1") => Ok(Token::Keyword(Keyword::Weak1)),
            Some("while") => Ok(Token::Keyword(Keyword::While)),
            Some("wildcard") => Ok(Token::Keyword(Keyword::Wildcard)),
            Some("wire") => Ok(Token::Keyword(Keyword::Wire)),
            Some("with") => Ok(Token::Keyword(Keyword::With)),
            Some("within") => Ok(Token::Keyword(Keyword::Within)),
            Some("wor") => Ok(Token::Keyword(Keyword::Wor)),
            Some("xnor") => Ok(Token::Keyword(Keyword::Xnor)),
            Some("xor") => Ok(Token::Keyword(Keyword::Xor)),
            _ => Err(String::from("Unrecognized keyword")),
        }
    }

    fn lex_punctuation(&mut self) -> Result<Token, String> {
        match self.read()? {
            '@' => Ok(Token::Punctuation(Punctuation::Asperand)),
            '#' => Ok(Token::Punctuation(Punctuation::Pound)),
            '$' => Ok(Token::Punctuation(Punctuation::Dollar)),
            '(' => Ok(Token::Punctuation(Punctuation::LeftParentheses)),
            ')' => Ok(Token::Punctuation(Punctuation::RightParentheses)),
            '[' => Ok(Token::Punctuation(Punctuation::LeftBracket)),
            ']' => Ok(Token::Punctuation(Punctuation::RightBracket)),
            '{' => Ok(Token::Punctuation(Punctuation::LeftBrace)),
            '}' => Ok(Token::Punctuation(Punctuation::RightBrace)),
            '\\' => Ok(Token::Punctuation(Punctuation::BackSlash)),
            ';' => Ok(Token::Punctuation(Punctuation::Semicolon)),
            ':' => Ok(Token::Punctuation(Punctuation::Colon)),
            '?' => Ok(Token::Punctuation(Punctuation::QuestionMark)),
            '`' => Ok(Token::Punctuation(Punctuation::Backtick)),
            '.' => Ok(Token::Punctuation(Punctuation::Period)),
            ',' => Ok(Token::Punctuation(Punctuation::Comma)),
            '\'' => Ok(Token::Punctuation(Punctuation::Apostrophe)),
            '_' => Ok(Token::Punctuation(Punctuation::Underscore)),
            _ => Err(String::from("Unrecognized punctuation mark")),
        }
    }
}
