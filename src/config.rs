use std::iter;
use super::compilation_unit::CompilationUnitScope;

#[derive(Debug)]
pub struct Config {
    files: Vec<String>,
    compilation_unit_scope: CompilationUnitScope,
}

enum Argument {
    File(String),
    CompilationUnitScopeFlag(CompilationUnitScope),
    Error(String),
}

impl Config {
    pub fn build(
        mut arguments: iter::Peekable<impl Iterator<Item = String>>,
    ) -> Result<Config, Vec<String>> {
        arguments.next(); // skip argument that is the path to executable

        let mut config = Config {
            files: Vec::new(),
            compilation_unit_scope: CompilationUnitScope::Individual,
        };
        let mut errors: Vec<String> = Vec::new();

        while arguments.peek().is_some() {
            let argument =
                parse_argument(&mut arguments).unwrap_or_else(|error| Argument::Error(error));

            match argument {
                Argument::CompilationUnitScopeFlag(scope) => config.compilation_unit_scope = scope,
                Argument::File(path) => config.files.push(path),
                Argument::Error(error) => errors.push(error),
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }

        Ok(config)
    }

    pub fn files(&self) -> &Vec<String> {
        return &self.files;
    }
    
    pub fn compilation_unit_scope(&self) -> &CompilationUnitScope {
        return &self.compilation_unit_scope;
    }
}

fn parse_argument(arguments: &mut impl Iterator<Item = String>) -> Result<Argument, String> {
    let argument = arguments.next();

    if argument.is_none() {
        return Err(String::from("No arguments to read"));
    }

    let argument = argument.unwrap();

    if !argument.starts_with("-") {
        return Ok(Argument::File(argument));
    }

    match argument.as_str() {
        "--compilation-unit-scope" => parse_compilation_unit_flag(arguments),
        _ => Err(format!("Unrecognized flag: {argument}")),
    }
}

fn parse_compilation_unit_flag(
    arguments: &mut impl Iterator<Item = String>,
) -> Result<Argument, String> {
    let value = arguments.next().unwrap().to_lowercase();
    match value.as_str() {
        "all" => Ok(Argument::CompilationUnitScopeFlag(
            CompilationUnitScope::All,
        )),
        "individual" => Ok(Argument::CompilationUnitScopeFlag(
            CompilationUnitScope::Individual,
        )),
        _ => Err(format!("Illegal compilation unit value: {value}")),
    }
}
