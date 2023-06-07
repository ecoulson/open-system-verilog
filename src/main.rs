use std::env;
use std::iter;

fn main() {
    // TODO: Add proper error handling of config errors
    let config = Config::build(env::args().peekable()).unwrap();

    dbg!(config.files);
    dbg!(config.compilation_unit_scope);
}


#[derive(Debug)]
enum CompilationUnitScope {
    All,
    Individual,
}

#[derive(Debug)]
struct Config {
    files: Vec<String>,
    compilation_unit_scope: CompilationUnitScope,
}

enum Argument {
    File(String),
    CompilationUnitScopeFlag(CompilationUnitScope),
}

impl Config {
    fn build(
        mut arguments: iter::Peekable<impl Iterator<Item = String>>,
    ) -> Result<Config, &'static str> {
        arguments.next(); // skip argument that is the path to executable

        let mut config = Config {
            files: Vec::new(),
            compilation_unit_scope: CompilationUnitScope::Individual,
        };

        while arguments.peek().is_some() {
            let argument = parse_argument(&mut arguments)?; // TODO: shouldn't hit case
                                                       // where next can be called
                                                       // but if it does we should
                                                       // gracefully handle the
                                                       // error
            match argument {
                Argument::CompilationUnitScopeFlag(scope) => config.compilation_unit_scope = scope,
                Argument::File(path) => config.files.push(path),
            }
        }

        Ok(config)
    }
}

fn parse_argument(arguments: &mut impl Iterator<Item = String>) -> Result<Argument, &'static str> {
    let argument = arguments.next().unwrap(); // TODO: shouldn't hit case
                                              // where next can be called
                                              // but if it does we should
                                              // gracefully handle the
                                              // error
    if !argument.starts_with("-") {
        return Ok(Argument::File(argument));
    }
    match argument.as_str() {
        "-CUA" => Ok(Argument::CompilationUnitScopeFlag(
            CompilationUnitScope::All,
        )),
        "--compilation-unit-scope" => parse_compilation_unit_flag(arguments),
        _ => Err("Unrecognized flag"),
    }
}

fn parse_compilation_unit_flag(arguments: &mut impl Iterator<Item = String>) -> Result<Argument, &'static str> {
    let value = arguments.next().unwrap().to_lowercase();
    match value.as_str() {
        "all" => Ok(Argument::CompilationUnitScopeFlag(CompilationUnitScope::All)),
        "individual" => Ok(Argument::CompilationUnitScopeFlag(CompilationUnitScope::Individual)),
        _ => Err("Illegal value for compilation unit")
    }
    
}

