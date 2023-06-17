use std::cmp::Ordering;
use std::error::Error;
use std::num::TryFromIntError;

use crate::char_reader::{CharReader, CharReaderError};
use crate::keywords::{Keyword, KEYWORD_SYMBOLS};
use crate::operators::{Operator, OPERATOR_SYMBOLS};
use crate::punctuation::Punctuation;
use crate::token::{Token, TokenFromSequence, TokenStruct};
use crate::token_stream::TokenStream;

const LEXICAL_OPERATIONS: [LexerOperator; 9] = [
    LexerOperator::WhiteSpace,
    LexerOperator::Comment,
    LexerOperator::Operator,
    LexerOperator::Keyword,
    LexerOperator::Number,
    LexerOperator::Punctuation,
    LexerOperator::StringLiteral,
    LexerOperator::CharacterSequence,
    LexerOperator::EscapedIdentifier,
];

enum LexerOperator {
    WhiteSpace,
    Comment,
    Number,
    StringLiteral,
    CharacterSequence,
    Operator,
    Keyword,
    Punctuation,
    EscapedIdentifier,
}

#[derive(Debug)]
pub enum LexerError {
    CharReader(CharReaderError),
    SequenceMismatch,
    NoSequenceFound,
    SequenceLengthOverflow(TryFromIntError),
    EOF,
}

impl std::fmt::Display for LexerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LexerError::CharReader(error) => write!(f, "CharReaderError: {}", error),
            LexerError::SequenceMismatch => write!(
                f,
                "SequenceMismatch: Failed to read expected character in sequence"
            ),
            LexerError::SequenceLengthOverflow(error) => {
                write!(f, "SequenceLengthOverflow: {}", error)
            }
            LexerError::NoSequenceFound => write!(f, "NoSequenceFound: No best sequence found"),
            LexerError::EOF => write!(f, "EOF: Tried to peek or read from end of file"),
        }
    }
}

impl Error for LexerError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            LexerError::CharReader(error) => Some(error),
            LexerError::EOF => None,
            LexerError::SequenceLengthOverflow(error) => Some(error),
            LexerError::SequenceMismatch => None,
            LexerError::NoSequenceFound => None,
        }
    }
}

impl From<CharReaderError> for LexerError {
    fn from(error: CharReaderError) -> Self {
        LexerError::CharReader(error)
    }
}

impl From<TryFromIntError> for LexerError {
    fn from(error: TryFromIntError) -> Self {
        LexerError::SequenceLengthOverflow(error)
    }
}

#[derive(Debug, Clone, Copy)]
struct Mark {
    position: u64,
    row: u64,
    column: u64,
}

impl Mark {
    fn build(position: u64, row: u64, column: u64) -> Mark {
        Mark {
            position,
            row,
            column,
        }
    }
}

pub struct Lexer {
    char_reader: CharReader,
    column: u64,
    row: u64,
    mark: Option<Mark>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct FilePosition {
    column: u64,
    row: u64,
}

impl FilePosition {
    pub fn new(row: u64, column: u64) -> FilePosition {
        FilePosition { column, row }
    }

    pub fn column(&self) -> u64 {
        self.column
    }

    pub fn row(&self) -> u64 {
        self.row
    }
}

impl Lexer {
    pub fn open(file_path: &str) -> Result<Lexer, LexerError> {
        Ok(Lexer {
            char_reader: CharReader::open(file_path)?,
            mark: None,
            column: 1,
            row: 1,
        })
    }

    fn peek(&mut self) -> Result<char, LexerError> {
        self.char_reader
            .peek_char()?
            .map_or(Err(LexerError::EOF), |ch| Ok(ch))
    }

    fn read(&mut self) -> Result<char, LexerError> {
        self.char_reader
            .read_char()?
            .map_or(Err(LexerError::EOF), |ch| {
                if ch == '\n' {
                    self.move_to_new_line();
                } else {
                    self.column += 1;
                }

                Ok(ch)
            })
    }

    fn position(&self) -> u64 {
        self.char_reader.get_position()
    }

    fn go_to(&mut self, mark: Mark) -> Result<(), LexerError> {
        self.row = mark.row;
        self.column = mark.column;
        self.char_reader.seek_from_start(mark.position)?;

        Ok(())
    }

    fn mark(&mut self) {
        self.mark = Some(self.get_current_mark())
    }

    fn get_current_mark(&self) -> Mark {
        Mark::build(self.position(), self.row, self.column)
    }

    fn go_to_mark(&mut self) -> Result<(), LexerError> {
        self.mark.map_or(Ok(()), |mark| {
            self.go_to(mark)?;
            Ok(())
        })
    }

    pub fn lex(&mut self) -> Result<TokenStream, LexerError> {
        let mut tokens = Vec::new();

        while self.can_read()? {
            let token = self.lex_token()?;
            match token.kind() {
                Token::WhiteSpace | Token::Comment => (),
                _ => tokens.push(token),
            }
        }

        tokens.push(TokenStruct::build_eof_token(self.file_position()));

        Ok(TokenStream::new(tokens))
    }

    fn lex_token(&mut self) -> Result<TokenStruct, LexerError> {
        let mut best_token =
            TokenStruct::build_error_token("Failed to read any characters", self.file_position());
        let mut best_mark = self.get_current_mark();

        for operator in LEXICAL_OPERATIONS {
            self.mark();
            let file_position = self.file_position();
            let token = match operator {
                LexerOperator::WhiteSpace => self.lex_white_space(),
                LexerOperator::Comment => self.lex_comments(),
                LexerOperator::Number => self.lex_number(),
                LexerOperator::StringLiteral => self.lex_string_literal(),
                LexerOperator::CharacterSequence => self.lex_character_sequence(),
                LexerOperator::Operator => self.lex_operator(),
                LexerOperator::Keyword => self.lex_keyword(),
                LexerOperator::Punctuation => self.lex_punctuation(),
                LexerOperator::EscapedIdentifier => self.lex_escaped_identifier(),
            }.map_or_else(|error| {
                match error {
                    LexerError::NoSequenceFound => Ok(TokenStruct::build_error_token("No sequence found", file_position)),
                    error => Err(error)

                }
            }, |token| Ok(token))?;
            let mark = self.get_current_mark();
            self.go_to_mark()?;

            if matches!(best_token.kind(), Token::Error(_))
                && !matches!(token.kind(), Token::Error(_))
                || best_mark.position < mark.position
            {
                best_mark = mark;
                best_token = token;
            }
        }

        self.go_to(best_mark)?;

        Ok(best_token)
    }

    fn file_position(&self) -> FilePosition {
        FilePosition::new(self.row, self.column)
    }

    fn can_read(&mut self) -> Result<bool, LexerError> {
        self.char_reader
            .has_chars()
            .map_err(|error| LexerError::CharReader(error))
    }

    fn lex_white_space(&mut self) -> Result<TokenStruct, LexerError> {
        let file_position = self.file_position();

        if !self.peek()?.is_whitespace() {
            return Ok(TokenStruct::build_error_token(
                "Not a sequence of white space characters",
                file_position,
            ));
        }

        while self.can_read()? && self.peek()?.is_whitespace() {
            self.read()?;
        }

        Ok(TokenStruct::build_white_space_token(file_position))
    }

    fn move_to_new_line(&mut self) {
        self.row += 1;
        self.column = 1;
    }

    fn lex_comments(&mut self) -> Result<TokenStruct, LexerError> {
        if self.peek()? != '/' {
            return Ok(TokenStruct::build_error_token(
                "Does not start with slash",
                self.file_position(),
            ));
        }

        self.read()?;

        match self.peek()? {
            '/' => Ok(self.lex_line_comment()?),
            '*' => Ok(self.lex_block_comment()?),
            _ => Ok(TokenStruct::build_error_token(
                "Slash is not followed by slash or astrix",
                self.file_position(),
            )),
        }
    }

    fn lex_line_comment(&mut self) -> Result<TokenStruct, LexerError> {
        let file_position = self.file_position();

        while self.read()? != '\n' {}

        Ok(TokenStruct::build_comment_token(file_position))
    }

    fn lex_block_comment(&mut self) -> Result<TokenStruct, LexerError> {
        let file_position = self.file_position();

        while !(self.read()? == '*' && self.peek()? == '/') {}

        self.read()?;

        Ok(TokenStruct::build_comment_token(file_position))
    }

    fn lex_number(&mut self) -> Result<TokenStruct, LexerError> {
        let mut number = String::new();
        let file_position = self.file_position();

        while self.can_read()? && self.peek()?.is_digit(10) {
            number.push(self.read()?);
        }

        if number.is_empty() {
            return Ok(TokenStruct::build_error_token(
                "Not a number",
                file_position,
            ));
        }

        Ok(TokenStruct::build_number_token(number, file_position))
    }

    fn lex_string_literal(&mut self) -> Result<TokenStruct, LexerError> {
        let mut string_literal = String::new();
        let file_position = self.file_position();

        if self.peek()? != '\"' {
            return Ok(TokenStruct::build_error_token(
                "String literal must start with \"",
                file_position,
            ));
        }

        self.read()?;

        while self.can_read()? && self.peek()? != '"' {
            string_literal.push(match self.read()? {
                '\\' => self.read_escaped_character()?,
                ch => ch,
            });
        }

        if !self.can_read()? {
            return Ok(TokenStruct::build_error_token(
                "String literal is never closed",
                file_position,
            ));
        }

        self.read()?;

        Ok(TokenStruct::build_string_literal_token(
            string_literal,
            file_position,
        ))
    }

    fn read_escaped_character(&mut self) -> Result<char, LexerError> {
        match self.read()? {
            '"' => Ok('"'),
            't' => Ok('\t'),
            'n' => Ok('\n'),
            'r' => Ok('\r'),
            _ => Ok(' '),
        }
    }

    fn lex_character_sequence(&mut self) -> Result<TokenStruct, LexerError> {
        let mut character_sequence = String::from("");
        let file_position = self.file_position();

        while self.can_read()? && (self.peek()?.is_alphabetic() || self.peek()? == '_') {
            character_sequence.push(self.read()?);
        }

        if character_sequence.is_empty() {
            return Ok(TokenStruct::build_error_token(
                "Not a character sequence",
                file_position,
            ));
        }

        Ok(TokenStruct::build_character_sequence_token(
            character_sequence,
            file_position,
        ))
    }

    fn lex_escaped_identifier(&mut self) -> Result<TokenStruct, LexerError> {
        if self.peek()? != '\\' {
            return Ok(TokenStruct::build_error_token(
                "Escaped identifier must start with \\",
                self.file_position(),
            ));
        }

        let mut identifier = String::new();
        let file_position = self.file_position();
        identifier.push(self.read()?);

        while self.can_read()? && !self.peek()?.is_whitespace() {
            identifier.push(self.read()?);
        }

        if identifier.len() == 1 {
            return Ok(TokenStruct::build_error_token(
                "Escaped identifier must not empty",
                file_position,
            ));
        }

        Ok(TokenStruct::build_escaped_identifier_token(
            identifier,
            file_position,
        ))
    }

    fn lex_operator(&mut self) -> Result<TokenStruct, LexerError> {
        let file_position = self.file_position();

        Operator::from_sequence(self.get_best_sequence(&OPERATOR_SYMBOLS)?, file_position)
            .map_or_else(
                |message| Ok(TokenStruct::build_error_token(message, file_position)),
                |token| Ok(token),
            )
    }

    fn get_best_sequence(
        &mut self,
        sequences: &[&'static str],
    ) -> Result<&'static str, LexerError> {
        let best_sequence: &'static str = sequences
            .iter()
            .map(|op| self.read_sequence(op))
            .filter(|seq| seq.is_ok())
            .map(|seq| seq.unwrap())
            .reduce(Lexer::compare_sequences)
            .unwrap_or("");

        if best_sequence.len() == 0 {
            return Err(LexerError::NoSequenceFound);
        }

        let best_length: u64 = best_sequence.bytes().len().try_into()?;

        self.go_to(Mark::build(
            self.position() + best_length,
            self.row,
            self.column + best_length,
        ))?;

        Ok(best_sequence)
    }

    fn read_sequence(&mut self, sequence: &'static str) -> Result<&'static str, LexerError> {
        self.mark();
        for sequence_char in sequence.chars() {
            if self.read()? != sequence_char {
                self.go_to_mark()?;
                return Err(LexerError::SequenceMismatch);
            }
        }

        self.go_to_mark()?;
        Ok(sequence)
    }

    fn compare_sequences(best_sequence: &'static str, sequence: &'static str) -> &'static str {
        match sequence.chars().count().cmp(&best_sequence.chars().count()) {
            Ordering::Greater | Ordering::Equal => sequence,
            _ => best_sequence,
        }
    }

    fn lex_keyword(&mut self) -> Result<TokenStruct, LexerError> {
        let file_position = self.file_position();

        Keyword::from_sequence(self.get_best_sequence(&KEYWORD_SYMBOLS)?, file_position)
            .map_or_else(
                |message| Ok(TokenStruct::build_error_token(message, file_position)),
                |token| Ok(token),
            )
    }

    fn lex_punctuation(&mut self) -> Result<TokenStruct, LexerError> {
        let position = self.file_position();

        Punctuation::from_char(self.read()?, position).map_or_else(
            |message| Ok(TokenStruct::build_error_token(message, position)),
            |token| Ok(token),
        )
    }
}

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::io::Write;
    use std::error::Error;

    use crate::token::TokenStruct;
    use crate::token_stream::TokenStream;

    use super::{FilePosition, Lexer};
    use tempfile::{tempdir, TempDir};

    fn create_temporary_verilog_file(
        dir: &TempDir,
        content: &'static str,
    ) -> Result<String, Box<dyn Error>> {
        let file_path = dir.path().join("test.sv");
        let mut file = File::create(&file_path)?;
        file.write(content.as_bytes())?;

        let path = String::from(file_path.to_str().unwrap());

        Ok(path)
    }

    fn assert_tokens_equal(tokens: TokenStream, expected_tokens: Vec<TokenStruct>) {
        let token_iterator = tokens.enumerate();
        let mut length = 0;

        for (i, token) in token_iterator {
            assert_eq!(token, expected_tokens[i]);
            length += 1;
        }

        assert_eq!(length, expected_tokens.len());
    }

    #[test]
    fn should_lex_empty_file() -> Result<(), Box<dyn Error>> {
        let expected_tokens = vec![TokenStruct::build_eof_token(FilePosition::new(1, 1))];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(&dir, "")?;
        let mut lexer = Lexer::open(file_path.as_str())?;

        let tokens = lexer.lex()?;
        assert_tokens_equal(tokens, expected_tokens);

        dir.close()?;

        Ok(())
    }

    #[test]
    fn should_lex_white_space() -> Result<(), Box<dyn Error>> {
        let expected_tokens = vec![TokenStruct::build_eof_token(FilePosition::new(2, 4))];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(&dir, "\n\r \t")?;
        let mut lexer = Lexer::open(file_path.as_str())?;

        let tokens = lexer.lex()?;
        assert_tokens_equal(tokens, expected_tokens);

        dir.close()?;

        Ok(())
    }

    #[test]
    fn should_lex_comments() -> Result<(), Box<dyn Error>> {
        let expected_tokens = vec![TokenStruct::build_eof_token(FilePosition::new(6, 4))];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(
            &dir,
            "//A comment
// A new comment
/* 
 * A
 * BLOCK
 */",
        )?;
        let mut lexer = Lexer::open(file_path.as_str())?;

        let tokens = lexer.lex()?;
        assert_tokens_equal(tokens, expected_tokens);

        Ok(())
    }

    #[test]
    fn should_lex_number() -> Result<(), Box<dyn Error>> {
        let expected_tokens = vec![
            TokenStruct::build_number_token(String::from("42069"), FilePosition::new(1, 1)),
            TokenStruct::build_eof_token(FilePosition::new(1, 6)),
        ];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(&dir, "42069")?;
        let mut lexer = Lexer::open(file_path.as_str())?;

        let tokens = lexer.lex()?;
        assert_tokens_equal(tokens, expected_tokens);

        Ok(())
    }

    #[test]
    fn should_lex_string_literal() -> Result<(), Box<dyn Error>> {
        let expected_tokens = vec![
            TokenStruct::build_string_literal_token(String::from("Foo"), FilePosition::new(1, 1)),
            TokenStruct::build_string_literal_token(
                String::from("Bar\n\t\r"),
                FilePosition::new(1, 6),
            ),
            TokenStruct::build_string_literal_token(
                String::from("Thelonius\nMonk"),
                FilePosition::new(2, 1),
            ),
            TokenStruct::build_eof_token(FilePosition::new(3, 6)),
        ];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(
            &dir,
            "\"Foo\"\"Bar\\n\\t\\r\"
\"Thelonius
Monk\"",
        )?;
        let mut lexer = Lexer::open(file_path.as_str())?;

        let tokens = lexer.lex()?;
        assert_tokens_equal(tokens, expected_tokens);

        Ok(())
    }

    #[test]
    fn should_lex_unclosed_string_literal() -> Result<(), Box<dyn Error>> {
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(&dir, "\"Unclosed")?;
        let expected_tokens = vec![
            TokenStruct::build_error_token(
                "String literal is never closed",
                FilePosition::new(1, 1),
            ),
            TokenStruct::build_eof_token(FilePosition::new(1, 10)),
        ];
        let mut lexer = Lexer::open(file_path.as_str())?;

        let tokens = lexer.lex()?;
        assert_tokens_equal(tokens, expected_tokens);

        Ok(())
    }

    #[test]
    fn should_lex_character_sequence() -> Result<(), Box<dyn Error>> {
        let expected_tokens = vec![
            TokenStruct::build_character_sequence_token(
                String::from("abcXYZ"),
                FilePosition::new(1, 1),
            ),
            TokenStruct::build_eof_token(FilePosition::new(1, 7)),
        ];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(&dir, "abcXYZ")?;
        let mut lexer = Lexer::open(file_path.as_str())?;

        let tokens = lexer.lex()?;
        assert_tokens_equal(tokens, expected_tokens);

        Ok(())
    }

    #[test]
    fn should_lex_escaped_identifier() -> Result<(), Box<dyn Error>> {
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(&dir, "\\@#art\\()\n")?;
        let expected_tokens = vec![
            TokenStruct::build_escaped_identifier_token(
                String::from("\\@#art\\()"),
                FilePosition::new(1, 1),
            ),
            TokenStruct::build_eof_token(FilePosition::new(2, 1)),
        ];
        let mut lexer = Lexer::open(file_path.as_str())?;

        let tokens = lexer.lex()?;
        assert_tokens_equal(tokens, expected_tokens);

        Ok(())
    }

    #[test]
    fn should_lex_escaped_identifier_at_eof() -> Result<(), Box<dyn Error>> {
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(&dir, "\\@#art\\()")?;
        let expected_tokens = vec![
            TokenStruct::build_escaped_identifier_token(
                String::from("\\@#art\\()"),
                FilePosition::new(1, 1),
            ),
            TokenStruct::build_eof_token(FilePosition::new(1, 10)),
        ];
        let mut lexer = Lexer::open(file_path.as_str())?;

        let tokens = lexer.lex()?;
        assert_tokens_equal(tokens, expected_tokens);

        Ok(())
    }
}
