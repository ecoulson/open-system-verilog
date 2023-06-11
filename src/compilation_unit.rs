use crate::config::Config;

pub enum CompilationUnitScope {
    All,
    Individual,
}

pub struct CompilationUnit {
    files: Vec<String>,
}

impl CompilationUnit {
    pub fn files(&self) -> &Vec<String> {
        &self.files
    }

    pub fn from_config(config: &Config) -> Vec<CompilationUnit> {
        match config.compilation_unit_scope() {
            CompilationUnitScope::All => vec![CompilationUnit {
                files: config.files().to_owned(),
            }],
            CompilationUnitScope::Individual => config
                .files()
                .iter()
                .map(|file_path| CompilationUnit { files: vec![file_path.clone()] })
                .collect(),
        }
    }
}
