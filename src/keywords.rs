use crate::{
    lexer::FilePosition,
    token::{TokenFromSequence, TokenStruct},
};

pub const KEYWORD_SYMBOLS: [&'static str; 246] = [
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

#[derive(Debug, PartialEq, Eq)]
pub enum Keyword {
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

impl TokenFromSequence for Keyword {
    fn from_sequence(sequence: &str, position: FilePosition) -> Result<TokenStruct, &'static str> {
        match sequence {
            "accept_on" => Ok(TokenStruct::build_keyword_token(
                Keyword::AcceptOn,
                position,
            )),
            "alias" => Ok(TokenStruct::build_keyword_token(Keyword::Alias, position)),
            "always" => Ok(TokenStruct::build_keyword_token(Keyword::Always, position)),
            "always_comb" => Ok(TokenStruct::build_keyword_token(
                Keyword::AlwaysComb,
                position,
            )),
            "always_ff" => Ok(TokenStruct::build_keyword_token(
                Keyword::AlwaysFF,
                position,
            )),
            "always_latch" => Ok(TokenStruct::build_keyword_token(
                Keyword::AlwaysLatch,
                position,
            )),
            "and" => Ok(TokenStruct::build_keyword_token(Keyword::And, position)),
            "assert" => Ok(TokenStruct::build_keyword_token(Keyword::Assert, position)),
            "assign" => Ok(TokenStruct::build_keyword_token(Keyword::Assign, position)),
            "assume" => Ok(TokenStruct::build_keyword_token(Keyword::Assume, position)),
            "automatic" => Ok(TokenStruct::build_keyword_token(
                Keyword::Automatic,
                position,
            )),
            "before" => Ok(TokenStruct::build_keyword_token(Keyword::Before, position)),
            "begin" => Ok(TokenStruct::build_keyword_token(Keyword::Begin, position)),
            "bind" => Ok(TokenStruct::build_keyword_token(Keyword::Bind, position)),
            "bins" => Ok(TokenStruct::build_keyword_token(Keyword::Bins, position)),
            "binsof" => Ok(TokenStruct::build_keyword_token(Keyword::Binsof, position)),
            "bit" => Ok(TokenStruct::build_keyword_token(Keyword::Bit, position)),
            "break" => Ok(TokenStruct::build_keyword_token(Keyword::Break, position)),
            "buf" => Ok(TokenStruct::build_keyword_token(Keyword::Buf, position)),
            "bufif0" => Ok(TokenStruct::build_keyword_token(Keyword::Bufif0, position)),
            "bufif1" => Ok(TokenStruct::build_keyword_token(Keyword::Bufif1, position)),
            "byte" => Ok(TokenStruct::build_keyword_token(Keyword::Byte, position)),
            "case" => Ok(TokenStruct::build_keyword_token(Keyword::Case, position)),
            "casex" => Ok(TokenStruct::build_keyword_token(Keyword::Casex, position)),
            "casez" => Ok(TokenStruct::build_keyword_token(Keyword::Casez, position)),
            "cell" => Ok(TokenStruct::build_keyword_token(Keyword::Cell, position)),
            "chandle" => Ok(TokenStruct::build_keyword_token(Keyword::Chandle, position)),
            "checker" => Ok(TokenStruct::build_keyword_token(Keyword::Checker, position)),
            "class" => Ok(TokenStruct::build_keyword_token(Keyword::Class, position)),
            "clocking" => Ok(TokenStruct::build_keyword_token(
                Keyword::Clocking,
                position,
            )),
            "cmos" => Ok(TokenStruct::build_keyword_token(Keyword::Cmos, position)),
            "config" => Ok(TokenStruct::build_keyword_token(Keyword::Config, position)),
            "const" => Ok(TokenStruct::build_keyword_token(Keyword::Const, position)),
            "constraint" => Ok(TokenStruct::build_keyword_token(
                Keyword::Constraint,
                position,
            )),
            "context" => Ok(TokenStruct::build_keyword_token(Keyword::Context, position)),
            "continue" => Ok(TokenStruct::build_keyword_token(
                Keyword::Continue,
                position,
            )),
            "cover" => Ok(TokenStruct::build_keyword_token(Keyword::Cover, position)),
            "covergroup" => Ok(TokenStruct::build_keyword_token(
                Keyword::Covergroup,
                position,
            )),
            "coverpoint" => Ok(TokenStruct::build_keyword_token(
                Keyword::Coverpoint,
                position,
            )),
            "cross" => Ok(TokenStruct::build_keyword_token(Keyword::Cross, position)),
            "deassign" => Ok(TokenStruct::build_keyword_token(
                Keyword::Deassign,
                position,
            )),
            "default" => Ok(TokenStruct::build_keyword_token(Keyword::Default, position)),
            "defparam" => Ok(TokenStruct::build_keyword_token(
                Keyword::Defparam,
                position,
            )),
            "design" => Ok(TokenStruct::build_keyword_token(Keyword::Design, position)),
            "disable" => Ok(TokenStruct::build_keyword_token(Keyword::Disable, position)),
            "do" => Ok(TokenStruct::build_keyword_token(Keyword::Do, position)),
            "edge" => Ok(TokenStruct::build_keyword_token(Keyword::Edge, position)),
            "else" => Ok(TokenStruct::build_keyword_token(Keyword::Else, position)),
            "end" => Ok(TokenStruct::build_keyword_token(Keyword::End, position)),
            "endcase" => Ok(TokenStruct::build_keyword_token(Keyword::Endcase, position)),
            "endchecker" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endchecker,
                position,
            )),
            "endclass" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endclass,
                position,
            )),
            "endclocking" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endclocking,
                position,
            )),
            "endconfig" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endconfig,
                position,
            )),
            "endfunction" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endfunction,
                position,
            )),
            "endgenerate" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endgenerate,
                position,
            )),
            "endgroup" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endgroup,
                position,
            )),
            "endinterface" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endinterface,
                position,
            )),
            "endmodule" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endmodule,
                position,
            )),
            "endpackage" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endpackage,
                position,
            )),
            "endprimitive" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endprimitive,
                position,
            )),
            "endprogram" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endprogram,
                position,
            )),
            "endproperty" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endproperty,
                position,
            )),
            "endspecify" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endspecify,
                position,
            )),
            "endsequence" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endsequence,
                position,
            )),
            "endtable" => Ok(TokenStruct::build_keyword_token(
                Keyword::Endtable,
                position,
            )),
            "endtask" => Ok(TokenStruct::build_keyword_token(Keyword::Endtask, position)),
            "enum" => Ok(TokenStruct::build_keyword_token(Keyword::Enum, position)),
            "event" => Ok(TokenStruct::build_keyword_token(Keyword::Event, position)),
            "eventually" => Ok(TokenStruct::build_keyword_token(
                Keyword::Eventually,
                position,
            )),
            "expect" => Ok(TokenStruct::build_keyword_token(Keyword::Expect, position)),
            "export" => Ok(TokenStruct::build_keyword_token(Keyword::Export, position)),
            "extends" => Ok(TokenStruct::build_keyword_token(Keyword::Extends, position)),
            "extern" => Ok(TokenStruct::build_keyword_token(Keyword::Extern, position)),
            "final" => Ok(TokenStruct::build_keyword_token(Keyword::Final, position)),
            "first_match" => Ok(TokenStruct::build_keyword_token(
                Keyword::FirstMatch,
                position,
            )),
            "for" => Ok(TokenStruct::build_keyword_token(Keyword::For, position)),
            "force" => Ok(TokenStruct::build_keyword_token(Keyword::Force, position)),
            "foreach" => Ok(TokenStruct::build_keyword_token(Keyword::Foreach, position)),
            "forever" => Ok(TokenStruct::build_keyword_token(Keyword::Forever, position)),
            "fork" => Ok(TokenStruct::build_keyword_token(Keyword::Fork, position)),
            "forkjoin" => Ok(TokenStruct::build_keyword_token(
                Keyword::Forkjoin,
                position,
            )),
            "function" => Ok(TokenStruct::build_keyword_token(
                Keyword::Function,
                position,
            )),
            "generate" => Ok(TokenStruct::build_keyword_token(
                Keyword::Generate,
                position,
            )),
            "genvar" => Ok(TokenStruct::build_keyword_token(Keyword::Genvar, position)),
            "global" => Ok(TokenStruct::build_keyword_token(Keyword::Global, position)),
            "highz0" => Ok(TokenStruct::build_keyword_token(Keyword::Highz0, position)),
            "highz1" => Ok(TokenStruct::build_keyword_token(Keyword::Highz1, position)),
            "if" => Ok(TokenStruct::build_keyword_token(Keyword::If, position)),
            "iff" => Ok(TokenStruct::build_keyword_token(Keyword::Iff, position)),
            "ifnone" => Ok(TokenStruct::build_keyword_token(Keyword::Ifnone, position)),
            "ignore_bins" => Ok(TokenStruct::build_keyword_token(
                Keyword::IgnoreBins,
                position,
            )),
            "illegal_bins" => Ok(TokenStruct::build_keyword_token(
                Keyword::IllegalBins,
                position,
            )),
            "implements" => Ok(TokenStruct::build_keyword_token(
                Keyword::Implements,
                position,
            )),
            "implies" => Ok(TokenStruct::build_keyword_token(Keyword::Implies, position)),
            "import" => Ok(TokenStruct::build_keyword_token(Keyword::Import, position)),
            "incdir" => Ok(TokenStruct::build_keyword_token(Keyword::Incdir, position)),
            "include" => Ok(TokenStruct::build_keyword_token(Keyword::Include, position)),
            "initial" => Ok(TokenStruct::build_keyword_token(Keyword::Initial, position)),
            "inout" => Ok(TokenStruct::build_keyword_token(Keyword::Inout, position)),
            "input" => Ok(TokenStruct::build_keyword_token(Keyword::Input, position)),
            "instance" => Ok(TokenStruct::build_keyword_token(
                Keyword::Instance,
                position,
            )),
            "int" => Ok(TokenStruct::build_keyword_token(Keyword::Int, position)),
            "integer" => Ok(TokenStruct::build_keyword_token(Keyword::Integer, position)),
            "interconnect" => Ok(TokenStruct::build_keyword_token(
                Keyword::Interconnect,
                position,
            )),
            "interface" => Ok(TokenStruct::build_keyword_token(
                Keyword::Interface,
                position,
            )),
            "intersect" => Ok(TokenStruct::build_keyword_token(
                Keyword::Intersect,
                position,
            )),
            "join" => Ok(TokenStruct::build_keyword_token(Keyword::Join, position)),
            "join_any" => Ok(TokenStruct::build_keyword_token(Keyword::JoinAny, position)),
            "join_none" => Ok(TokenStruct::build_keyword_token(
                Keyword::JoinNone,
                position,
            )),
            "large" => Ok(TokenStruct::build_keyword_token(Keyword::Large, position)),
            "let" => Ok(TokenStruct::build_keyword_token(Keyword::Let, position)),
            "liblist" => Ok(TokenStruct::build_keyword_token(Keyword::Liblist, position)),
            "library" => Ok(TokenStruct::build_keyword_token(Keyword::Library, position)),
            "local" => Ok(TokenStruct::build_keyword_token(Keyword::Local, position)),
            "localparam" => Ok(TokenStruct::build_keyword_token(
                Keyword::Localparam,
                position,
            )),
            "logic" => Ok(TokenStruct::build_keyword_token(Keyword::Logic, position)),
            "longint" => Ok(TokenStruct::build_keyword_token(Keyword::Longint, position)),
            "macromodule" => Ok(TokenStruct::build_keyword_token(
                Keyword::Macromodule,
                position,
            )),
            "matches" => Ok(TokenStruct::build_keyword_token(Keyword::Matches, position)),
            "medium" => Ok(TokenStruct::build_keyword_token(Keyword::Medium, position)),
            "modport" => Ok(TokenStruct::build_keyword_token(Keyword::Modport, position)),
            "module" => Ok(TokenStruct::build_keyword_token(Keyword::Module, position)),
            "nand" => Ok(TokenStruct::build_keyword_token(Keyword::Nand, position)),
            "negedge" => Ok(TokenStruct::build_keyword_token(Keyword::Negedge, position)),
            "nettype" => Ok(TokenStruct::build_keyword_token(Keyword::Nettype, position)),
            "new" => Ok(TokenStruct::build_keyword_token(Keyword::New, position)),
            "nexttime" => Ok(TokenStruct::build_keyword_token(
                Keyword::Nexttime,
                position,
            )),
            "nmos" => Ok(TokenStruct::build_keyword_token(Keyword::Nmos, position)),
            "nor" => Ok(TokenStruct::build_keyword_token(Keyword::Nor, position)),
            "noshowcancelled" => Ok(TokenStruct::build_keyword_token(
                Keyword::Noshowcancelled,
                position,
            )),
            "not" => Ok(TokenStruct::build_keyword_token(Keyword::Not, position)),
            "notif0" => Ok(TokenStruct::build_keyword_token(Keyword::Notif0, position)),
            "notif1" => Ok(TokenStruct::build_keyword_token(Keyword::Notif1, position)),
            "null" => Ok(TokenStruct::build_keyword_token(Keyword::Null, position)),
            "or" => Ok(TokenStruct::build_keyword_token(Keyword::Or, position)),
            "output" => Ok(TokenStruct::build_keyword_token(Keyword::Output, position)),
            "package" => Ok(TokenStruct::build_keyword_token(Keyword::Package, position)),
            "packed" => Ok(TokenStruct::build_keyword_token(Keyword::Packed, position)),
            "parameter" => Ok(TokenStruct::build_keyword_token(
                Keyword::Parameter,
                position,
            )),
            "pmos" => Ok(TokenStruct::build_keyword_token(Keyword::Pmos, position)),
            "posedge" => Ok(TokenStruct::build_keyword_token(Keyword::Posedge, position)),
            "primitive" => Ok(TokenStruct::build_keyword_token(
                Keyword::Primitive,
                position,
            )),
            "priority" => Ok(TokenStruct::build_keyword_token(
                Keyword::Priority,
                position,
            )),
            "program" => Ok(TokenStruct::build_keyword_token(Keyword::Program, position)),
            "property" => Ok(TokenStruct::build_keyword_token(
                Keyword::Property,
                position,
            )),
            "protected" => Ok(TokenStruct::build_keyword_token(
                Keyword::Protected,
                position,
            )),
            "pull0" => Ok(TokenStruct::build_keyword_token(Keyword::Pull0, position)),
            "pull1" => Ok(TokenStruct::build_keyword_token(Keyword::Pull1, position)),
            "pulldown" => Ok(TokenStruct::build_keyword_token(
                Keyword::Pulldown,
                position,
            )),
            "pullup" => Ok(TokenStruct::build_keyword_token(Keyword::Pullup, position)),
            "pulsestyle_ondetect" => Ok(TokenStruct::build_keyword_token(
                Keyword::PulsestyleOndetect,
                position,
            )),
            "pulsestyle_onevent" => Ok(TokenStruct::build_keyword_token(
                Keyword::PulsestyleOnevent,
                position,
            )),
            "pure" => Ok(TokenStruct::build_keyword_token(Keyword::Pure, position)),
            "rand" => Ok(TokenStruct::build_keyword_token(Keyword::Rand, position)),
            "randc" => Ok(TokenStruct::build_keyword_token(Keyword::Randc, position)),
            "randcase" => Ok(TokenStruct::build_keyword_token(
                Keyword::Randcase,
                position,
            )),
            "randsequence" => Ok(TokenStruct::build_keyword_token(
                Keyword::Randsequence,
                position,
            )),
            "rcmos" => Ok(TokenStruct::build_keyword_token(Keyword::Rcmos, position)),
            "real" => Ok(TokenStruct::build_keyword_token(Keyword::Real, position)),
            "realtime" => Ok(TokenStruct::build_keyword_token(
                Keyword::Realtime,
                position,
            )),
            "ref" => Ok(TokenStruct::build_keyword_token(Keyword::Ref, position)),
            "reg" => Ok(TokenStruct::build_keyword_token(Keyword::Reg, position)),
            "reject_on" => Ok(TokenStruct::build_keyword_token(
                Keyword::RejectOn,
                position,
            )),
            "release" => Ok(TokenStruct::build_keyword_token(Keyword::Release, position)),
            "repeat" => Ok(TokenStruct::build_keyword_token(Keyword::Repeat, position)),
            "restrict" => Ok(TokenStruct::build_keyword_token(
                Keyword::Restrict,
                position,
            )),
            "return" => Ok(TokenStruct::build_keyword_token(Keyword::Return, position)),
            "rnmos" => Ok(TokenStruct::build_keyword_token(Keyword::Rnmos, position)),
            "rpmos" => Ok(TokenStruct::build_keyword_token(Keyword::Rpmos, position)),
            "rtran" => Ok(TokenStruct::build_keyword_token(Keyword::Rtran, position)),
            "rtranif0" => Ok(TokenStruct::build_keyword_token(
                Keyword::Rtranif0,
                position,
            )),
            "rtranif1" => Ok(TokenStruct::build_keyword_token(
                Keyword::Rtranif1,
                position,
            )),
            "s_always" => Ok(TokenStruct::build_keyword_token(Keyword::SAlways, position)),
            "s_eventually" => Ok(TokenStruct::build_keyword_token(
                Keyword::SEventually,
                position,
            )),
            "s_nexttime" => Ok(TokenStruct::build_keyword_token(
                Keyword::SNexttime,
                position,
            )),
            "s_until" => Ok(TokenStruct::build_keyword_token(Keyword::SUntil, position)),
            "s_until_with" => Ok(TokenStruct::build_keyword_token(
                Keyword::SUntilWith,
                position,
            )),
            "scalared" => Ok(TokenStruct::build_keyword_token(
                Keyword::Scalared,
                position,
            )),
            "sequence" => Ok(TokenStruct::build_keyword_token(
                Keyword::Sequence,
                position,
            )),
            "shortint" => Ok(TokenStruct::build_keyword_token(
                Keyword::Shortint,
                position,
            )),
            "shortreal" => Ok(TokenStruct::build_keyword_token(
                Keyword::Shortreal,
                position,
            )),
            "showcancelled" => Ok(TokenStruct::build_keyword_token(
                Keyword::Showcancelled,
                position,
            )),
            "signed" => Ok(TokenStruct::build_keyword_token(Keyword::Signed, position)),
            "small" => Ok(TokenStruct::build_keyword_token(Keyword::Small, position)),
            "soft" => Ok(TokenStruct::build_keyword_token(Keyword::Soft, position)),
            "solve" => Ok(TokenStruct::build_keyword_token(Keyword::Solve, position)),
            "specify" => Ok(TokenStruct::build_keyword_token(Keyword::Specify, position)),
            "specparam" => Ok(TokenStruct::build_keyword_token(
                Keyword::Specparam,
                position,
            )),
            "static" => Ok(TokenStruct::build_keyword_token(Keyword::Static, position)),
            "string" => Ok(TokenStruct::build_keyword_token(Keyword::String, position)),
            "strong" => Ok(TokenStruct::build_keyword_token(Keyword::Strong, position)),
            "strong0" => Ok(TokenStruct::build_keyword_token(Keyword::Strong0, position)),
            "strong1" => Ok(TokenStruct::build_keyword_token(Keyword::Strong1, position)),
            "struct" => Ok(TokenStruct::build_keyword_token(Keyword::Struct, position)),
            "super" => Ok(TokenStruct::build_keyword_token(Keyword::Super, position)),
            "supply0" => Ok(TokenStruct::build_keyword_token(Keyword::Supply0, position)),
            "supply1" => Ok(TokenStruct::build_keyword_token(Keyword::Supply1, position)),
            "sync_accept_on" => Ok(TokenStruct::build_keyword_token(
                Keyword::SyncAcceptOn,
                position,
            )),
            "sync_reject_on" => Ok(TokenStruct::build_keyword_token(
                Keyword::SyncRejectOn,
                position,
            )),
            "table" => Ok(TokenStruct::build_keyword_token(Keyword::Table, position)),
            "tagged" => Ok(TokenStruct::build_keyword_token(Keyword::Tagged, position)),
            "task" => Ok(TokenStruct::build_keyword_token(Keyword::Task, position)),
            "this" => Ok(TokenStruct::build_keyword_token(Keyword::This, position)),
            "throughout" => Ok(TokenStruct::build_keyword_token(
                Keyword::Throughout,
                position,
            )),
            "time" => Ok(TokenStruct::build_keyword_token(Keyword::Time, position)),
            "timeprecision" => Ok(TokenStruct::build_keyword_token(
                Keyword::Timeprecision,
                position,
            )),
            "timeunit" => Ok(TokenStruct::build_keyword_token(
                Keyword::Timeunit,
                position,
            )),
            "tran" => Ok(TokenStruct::build_keyword_token(Keyword::Tran, position)),
            "tranif0" => Ok(TokenStruct::build_keyword_token(Keyword::Tranif0, position)),
            "tranif1" => Ok(TokenStruct::build_keyword_token(Keyword::Tranif1, position)),
            "tri" => Ok(TokenStruct::build_keyword_token(Keyword::Tri, position)),
            "tri0" => Ok(TokenStruct::build_keyword_token(Keyword::Tri0, position)),
            "tri1" => Ok(TokenStruct::build_keyword_token(Keyword::Tri1, position)),
            "triand" => Ok(TokenStruct::build_keyword_token(Keyword::Triand, position)),
            "trior" => Ok(TokenStruct::build_keyword_token(Keyword::Trior, position)),
            "trireg" => Ok(TokenStruct::build_keyword_token(Keyword::Trireg, position)),
            "type" => Ok(TokenStruct::build_keyword_token(Keyword::Type, position)),
            "typedef" => Ok(TokenStruct::build_keyword_token(Keyword::Typedef, position)),
            "union" => Ok(TokenStruct::build_keyword_token(Keyword::Union, position)),
            "unique" => Ok(TokenStruct::build_keyword_token(Keyword::Unique, position)),
            "unique0" => Ok(TokenStruct::build_keyword_token(Keyword::Unique0, position)),
            "unsigned" => Ok(TokenStruct::build_keyword_token(
                Keyword::Unsigned,
                position,
            )),
            "until" => Ok(TokenStruct::build_keyword_token(Keyword::Until, position)),
            "until_with" => Ok(TokenStruct::build_keyword_token(
                Keyword::UntilWith,
                position,
            )),
            "untyped" => Ok(TokenStruct::build_keyword_token(Keyword::Untyped, position)),
            "use" => Ok(TokenStruct::build_keyword_token(Keyword::Use, position)),
            "uwire" => Ok(TokenStruct::build_keyword_token(Keyword::Uwire, position)),
            "var" => Ok(TokenStruct::build_keyword_token(Keyword::Var, position)),
            "vectored" => Ok(TokenStruct::build_keyword_token(
                Keyword::Vectored,
                position,
            )),
            "virtual" => Ok(TokenStruct::build_keyword_token(Keyword::Virtual, position)),
            "void" => Ok(TokenStruct::build_keyword_token(Keyword::Void, position)),
            "wait" => Ok(TokenStruct::build_keyword_token(Keyword::Wait, position)),
            "wait_order" => Ok(TokenStruct::build_keyword_token(
                Keyword::WaitOrder,
                position,
            )),
            "wand" => Ok(TokenStruct::build_keyword_token(Keyword::Wand, position)),
            "weak" => Ok(TokenStruct::build_keyword_token(Keyword::Weak, position)),
            "weak0" => Ok(TokenStruct::build_keyword_token(Keyword::Weak0, position)),
            "weak1" => Ok(TokenStruct::build_keyword_token(Keyword::Weak1, position)),
            "while" => Ok(TokenStruct::build_keyword_token(Keyword::While, position)),
            "wildcard" => Ok(TokenStruct::build_keyword_token(
                Keyword::Wildcard,
                position,
            )),
            "wire" => Ok(TokenStruct::build_keyword_token(Keyword::Wire, position)),
            "with" => Ok(TokenStruct::build_keyword_token(Keyword::With, position)),
            "within" => Ok(TokenStruct::build_keyword_token(Keyword::Within, position)),
            "wor" => Ok(TokenStruct::build_keyword_token(Keyword::Wor, position)),
            "xnor" => Ok(TokenStruct::build_keyword_token(Keyword::Xnor, position)),
            "xor" => Ok(TokenStruct::build_keyword_token(Keyword::Xor, position)),
            _ => Err("Unrecognized keyword"),
        }
    }
}
