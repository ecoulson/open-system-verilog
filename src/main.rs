use std::env;
use std::process;

use open_system_verilog::lexer::Lexer;
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

        dbg!(tokens);
    }
}


