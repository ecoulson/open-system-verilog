use std::cmp::Ordering;

use crate::char_reader::CharReader;
use crate::keywords::KEYWORD_SYMBOLS;
use crate::operators::OPERATOR_SYMBOLS;
use crate::punctuation::Punctuation;
use crate::token::{BuildToken, ErrorToken, Token};
use crate::token::{
    CharacterSequenceToken, KeywordToken, NumberToken, OperatorToken, PunctuationToken,
    StringLiteralToken, TokenFromSequence,
};

const LEXICAL_OPERATIONS: [LexerOperator; 8] = [
    LexerOperator::WhiteSpace,
    LexerOperator::Comment,
    LexerOperator::Operator,
    LexerOperator::Keyword,
    LexerOperator::Punctuation,
    LexerOperator::Number,
    LexerOperator::StringLiteral,
    LexerOperator::CharacterSequence,
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
}

#[derive(Clone, Copy)]
struct Mark {
    position: usize,
    row: usize,
    column: usize,
}

impl Mark {
    fn build(position: usize, row: usize, column: usize) -> Mark {
        Mark {
            position,
            row,
            column,
        }
    }
}

pub struct Lexer {
    char_reader: CharReader,
    column: usize,
    row: usize,
    mark: Option<Mark>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct FilePosition {
    column: usize,
    row: usize,
}

impl FilePosition {
    fn new(row: usize, column: usize) -> FilePosition {
        FilePosition { column, row }
    }
}

impl Lexer {
    pub fn open(file_path: &str) -> Lexer {
        Lexer {
            char_reader: CharReader::open(file_path),
            mark: None,
            column: 1,
            row: 1,
        }
    }

    fn peek(&mut self) -> Result<char, &'static str> {
        match self.char_reader.peek_char() {
            None => Err("End of file"),
            Some(ch) => Ok(ch),
        }
    }

    fn read(&mut self) -> Result<char, &'static str> {
        match self.char_reader.read_char() {
            None => Err("End of file"),
            Some('\n') => {
                self.move_to_new_line();
                Ok('\n')
            }
            Some(ch) => {
                self.column += 1;
                Ok(ch)
            }
        }
    }

    fn position(&self) -> usize {
        self.char_reader.get_position()
    }

    fn go_to(&mut self, mark: Mark) {
        self.row = mark.row;
        self.column = mark.column;
        self.char_reader.seek_from_start(mark.position)
    }

    fn mark(&mut self) {
        self.mark = Some(Mark::build(self.position(), self.row, self.column));
    }

    fn go_to_mark(&mut self) {
        if self.mark.is_none() {
            return;
        }

        self.go_to(self.mark.unwrap());
    }

    pub fn lex(&mut self) -> Vec<Token> {
        let mut tokens = Vec::new();

        while self.can_read() {
            match self.lex_token() {
                Token::WhiteSpace | Token::Comment => (),
                token => tokens.push(token),
            }
        }

        tokens.push(Token::EOF(self.file_position()));

        tokens
    }

    fn execute_lexical_operation(&mut self, operation: LexerOperator) -> Token {
        let file_position = self.file_position();

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

        match token {
            Err(message) => ErrorToken::build_token(message, file_position),
            Ok(token) => token,
        }
    }

    fn lex_token(&mut self) -> Token {
        let file_position = self.file_position();
        let mut best_token =
            ErrorToken::build_token("Failed to read any characters", file_position);
        let mut best_mark = Mark::build(0, 1, 1);

        for operator in LEXICAL_OPERATIONS {
            self.mark();
            let token = self.execute_lexical_operation(operator);
            let mark = Mark::build(self.position(), self.row, self.column);
            self.go_to_mark();

            if matches!(best_token, Token::Error(_)) && !matches!(token, Token::Error(_))
                || best_mark.position < mark.position
            {
                best_mark = mark;
                best_token = token;
            }
        }

        self.go_to(best_mark);

        best_token
    }

    fn file_position(&self) -> FilePosition {
        FilePosition::new(self.row, self.column)
    }

    fn can_read(&mut self) -> bool {
        self.char_reader.has_chars()
    }

    fn lex_white_space(&mut self) -> Result<Token, &'static str> {
        if !self.peek()?.is_whitespace() {
            return Err("Not a sequence of white space characters");
        }

        while self.can_read() && self.peek()?.is_whitespace() {
            self.read()?;
        }

        Ok(Token::WhiteSpace)
    }

    fn move_to_new_line(&mut self) {
        self.row += 1;
        self.column = 1;
    }

    fn lex_comments(&mut self) -> Result<Token, &'static str> {
        if self.peek()? != '/' {
            return Err("Does not start with slash");
        }

        self.read()?;

        match self.peek()? {
            '/' => self.lex_line_comment(),
            '*' => self.lex_block_comment(),
            _ => Err("Slash is not followed by slash or astrix"),
        }
    }

    fn lex_line_comment(&mut self) -> Result<Token, &'static str> {
        while self.read()? != '\n' {}

        Ok(Token::Comment)
    }

    fn lex_block_comment(&mut self) -> Result<Token, &'static str> {
        while !(self.read()? == '*' && self.peek()? == '/') {}

        self.read()?;

        Ok(Token::Comment)
    }

    fn lex_number(&mut self) -> Result<Token, &'static str> {
        let mut number = String::new();
        let file_position = self.file_position();

        while self.can_read() && self.peek()?.is_digit(10) {
            number.push(self.read()?);
        }

        if number.is_empty() {
            return Err("Not a number");
        }

        Ok(NumberToken::build_token(number, file_position))
    }

    fn lex_string_literal(&mut self) -> Result<Token, &'static str> {
        let mut string_literal = String::new();
        let file_position = self.file_position();

        if self.peek()? != '\"' {
            return Err("String literal must start with \"");
        }

        self.read()?;

        while self.can_read() && self.peek()? != '"' {
            let ch = self.read()?;
            match ch {
                '\\' => string_literal.push(self.read_escaped_character()?),
                _ => string_literal.push(ch),
            }
        }

        if !self.can_read() {
            return Err("String literal is never closed");
        }

        self.read()?;

        Ok(StringLiteralToken::build_token(
            string_literal,
            file_position,
        ))
    }

    fn read_escaped_character(&mut self) -> Result<char, &'static str> {
        match self.read()? {
            '"' => Ok('"'),
            't' => Ok('\t'),
            'n' => Ok('\n'),
            'r' => Ok('\r'),
            _ => Ok(' '),
        }
    }

    fn lex_character_sequence(&mut self) -> Result<Token, &'static str> {
        return match self.peek()? {
            '\\' => self.lex_escaped_identifier(),
            _ => self.lex_simple_identifier(),
        };
    }

    fn lex_escaped_identifier(&mut self) -> Result<Token, &'static str> {
        let mut escaped_identifier = String::new();
        let file_position = self.file_position();
        escaped_identifier.push(self.read()?); // Read the \

        while !self.peek()?.is_whitespace() {
            escaped_identifier.push(self.read()?);
        }

        if escaped_identifier.len() == 1 {
            return Err("Escaped identifier must not empty");
        }

        Ok(CharacterSequenceToken::build_token(
            escaped_identifier,
            file_position,
        ))
    }

    fn lex_simple_identifier(&mut self) -> Result<Token, &'static str> {
        let mut character_sequence = String::from("");
        let file_position = self.file_position();

        while self.can_read() && self.peek()?.is_alphabetic() {
            character_sequence.push(self.read()?);
        }

        if character_sequence.is_empty() {
            return Err("Not a character sequence");
        }

        Ok(CharacterSequenceToken::build_token(
            character_sequence,
            file_position,
        ))
    }

    fn lex_operator(&mut self) -> Result<Token, &'static str> {
        let file_position = self.file_position();

        match self.get_best_sequence(&OPERATOR_SYMBOLS) {
            Some(sequence) => OperatorToken::from_sequence(sequence, file_position),
            _ => Err("Unrecognized operator"),
        }
    }

    fn get_best_sequence(&mut self, sequences: &[&'static str]) -> Option<&'static str> {
        let best_sequence: Option<&'static str> = sequences
            .iter()
            .map(|op| {
                self.mark();
                let sequence = self.read_sequence(op);
                self.go_to_mark();

                sequence
            })
            .filter(|seq| seq.is_ok())
            .map(|seq| seq.unwrap())
            .reduce(Lexer::compare_sequences);

        if best_sequence.is_none() {
            return None;
        }


        let best_length = best_sequence.unwrap().bytes().len();
        self.go_to(Mark::build(
            self.position() + best_length,
            self.row,
            self.column + best_length,
        ));

        best_sequence
    }

    fn read_sequence(&mut self, sequence: &'static str) -> Result<&'static str, &'static str> {
        for sequence_char in sequence.chars() {
            if self.read()? != sequence_char {
                return Err("Char did not match");
            }
        }

        Ok(sequence)
    }

    fn compare_sequences(best_sequence: &'static str, sequence: &'static str) -> &'static str {
        match sequence.chars().count().cmp(&best_sequence.chars().count()) {
            Ordering::Greater | Ordering::Equal => sequence,
            _ => best_sequence,
        }
    }

    fn lex_keyword(&mut self) -> Result<Token, &'static str> {
        let file_position = self.file_position();

        match self.get_best_sequence(&KEYWORD_SYMBOLS) {
            Some(sequence) => KeywordToken::from_sequence(sequence, file_position),
            None => Err("Unrecognized keyword"),
        }
    }

    fn lex_punctuation(&mut self) -> Result<Token, &'static str> {
        let file_position = self.file_position();

        let result = match self.peek()? {
            '@' => Ok(PunctuationToken::build_token(
                Punctuation::Asperand,
                file_position,
            )),
            '#' => Ok(PunctuationToken::build_token(
                Punctuation::Pound,
                file_position,
            )),
            '$' => Ok(PunctuationToken::build_token(
                Punctuation::Dollar,
                file_position,
            )),
            '(' => Ok(PunctuationToken::build_token(
                Punctuation::LeftParentheses,
                file_position,
            )),
            ')' => Ok(PunctuationToken::build_token(
                Punctuation::RightParentheses,
                file_position,
            )),
            '[' => Ok(PunctuationToken::build_token(
                Punctuation::LeftBracket,
                file_position,
            )),
            ']' => Ok(PunctuationToken::build_token(
                Punctuation::RightBracket,
                file_position,
            )),
            '{' => Ok(PunctuationToken::build_token(
                Punctuation::LeftBrace,
                file_position,
            )),
            '}' => Ok(PunctuationToken::build_token(
                Punctuation::RightBrace,
                file_position,
            )),
            '\\' => Ok(PunctuationToken::build_token(
                Punctuation::BackSlash,
                file_position,
            )),
            ';' => Ok(PunctuationToken::build_token(
                Punctuation::Semicolon,
                file_position,
            )),
            ':' => Ok(PunctuationToken::build_token(
                Punctuation::Colon,
                file_position,
            )),
            '?' => Ok(PunctuationToken::build_token(
                Punctuation::QuestionMark,
                file_position,
            )),
            '`' => Ok(PunctuationToken::build_token(
                Punctuation::Backtick,
                file_position,
            )),
            '.' => Ok(PunctuationToken::build_token(
                Punctuation::Period,
                file_position,
            )),
            ',' => Ok(PunctuationToken::build_token(
                Punctuation::Comma,
                file_position,
            )),
            '\'' => Ok(PunctuationToken::build_token(
                Punctuation::Apostrophe,
                file_position,
            )),
            '_' => Ok(PunctuationToken::build_token(
                Punctuation::Underscore,
                file_position,
            )),
            _ => Err("Unrecognized punctuation mark"),
        };

        self.read()?;

        result
    }
}

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::io::{Error, Write};
    use std::path::PathBuf;

    use crate::operators::Operator;
    use crate::token::{
        BuildToken, CharacterSequenceToken, ErrorToken, NumberToken, OperatorToken,
        StringLiteralToken,
    };

    use super::{FilePosition, Lexer, Token};
    use tempfile::{tempdir, TempDir};

    fn create_temporary_verilog_file(
        dir: &TempDir,
        content: &'static str,
    ) -> Result<PathBuf, Error> {
        let file_path = dir.path().join("test.sv");
        let mut file = File::create(&file_path)?;
        file.write(content.as_bytes())?;

        Ok(file_path)
    }

    #[test]
    fn should_lex_empty_file() -> Result<(), Error> {
        let expected_tokens = vec![Token::EOF(FilePosition::new(1, 1))];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(&dir, "")?;
        let mut lexer = Lexer::open(file_path.to_str().unwrap());

        let tokens = lexer.lex();

        assert_eq!(tokens.len(), expected_tokens.len());
        dir.close()?;

        Ok(())
    }

    #[test]
    fn should_lex_white_space() -> Result<(), Error> {
        let expected_tokens = vec![Token::EOF(FilePosition::new(2, 4))];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(&dir, "\n\r \t")?;
        let mut lexer = Lexer::open(file_path.to_str().unwrap());

        let tokens = lexer.lex();

        assert_eq!(tokens.len(), expected_tokens.len());
        for i in 0..tokens.len() {
            assert_eq!(tokens[i], expected_tokens[i]);
        }
        dir.close()?;

        Ok(())
    }

    #[test]
    fn should_lex_comments() -> Result<(), Error> {
        let expected_tokens = vec![Token::EOF(FilePosition::new(6, 3))];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(
            &dir,
            "// A comment
/*
* A
* Block
* Comment
*/",
        )?;
        let mut lexer = Lexer::open(file_path.to_str().unwrap());

        let tokens = lexer.lex();

        assert_eq!(tokens.len(), expected_tokens.len());
        for i in 0..tokens.len() {
            assert_eq!(tokens[i], expected_tokens[i]);
        }
        dir.close()?;

        Ok(())
    }

    #[test]
    fn should_lex_number() -> Result<(), Error> {
        let expected_tokens = vec![
            NumberToken::build_token(String::from("42069"), FilePosition::new(1, 1)),
            Token::EOF(FilePosition::new(1, 6)),
        ];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(&dir, "42069")?;
        let mut lexer = Lexer::open(file_path.to_str().unwrap());

        let tokens = lexer.lex();

        assert_eq!(tokens.len(), expected_tokens.len());
        for i in 0..tokens.len() {
            assert_eq!(tokens[i], expected_tokens[i]);
        }
        dir.close()?;

        Ok(())
    }

    #[test]
    fn should_lex_string_literal() -> Result<(), Error> {
        let expected_tokens = vec![
            StringLiteralToken::build_token(String::from("Foo"), FilePosition::new(1, 1)),
            StringLiteralToken::build_token(String::from("Bar\n\t\r"), FilePosition::new(1, 6)),
            StringLiteralToken::build_token(
                String::from("Thelonius\nMonk"),
                FilePosition::new(2, 1),
            ),
            Token::EOF(FilePosition::new(3, 6)),
        ];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(
            &dir,
            "\"Foo\"\"Bar\\n\\t\\r\"
\"Thelonius
Monk\"",
        )?;
        let mut lexer = Lexer::open(file_path.to_str().unwrap());

        let tokens = lexer.lex();

        assert_eq!(tokens.len(), expected_tokens.len());
        for i in 0..tokens.len() {
            assert_eq!(tokens[i], expected_tokens[i]);
        }
        dir.close()?;

        Ok(())
    }

    #[test]
    fn should_lex_unclosed_string_literal() -> Result<(), Error> {
        let expected_tokens = vec![
            ErrorToken::build_token("String literal is never closed", FilePosition::new(1, 1)),
            Token::EOF(FilePosition::new(1, 10)),
        ];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(&dir, "\"Unclosed")?;
        let mut lexer = Lexer::open(file_path.to_str().unwrap());

        let tokens = lexer.lex();

        assert_eq!(tokens.len(), expected_tokens.len());
        for i in 0..tokens.len() {
            assert_eq!(tokens[i], expected_tokens[i]);
        }
        dir.close()?;

        Ok(())
    }

    #[test]
    fn should_lex_character_sequence() -> Result<(), Error> {
        let expected_tokens = vec![
            CharacterSequenceToken::build_token(String::from("abcXYZ"), FilePosition::new(1, 1)),
            CharacterSequenceToken::build_token(
                String::from("\\@#art\\()"),
                FilePosition::new(1, 8),
            ),
            Token::EOF(FilePosition::new(2, 1)),
        ];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(&dir, "abcXYZ \\@#art\\()\n")?;
        let mut lexer = Lexer::open(file_path.to_str().unwrap());

        let tokens = lexer.lex();

        assert_eq!(tokens.len(), expected_tokens.len());
        for i in 0..tokens.len() {
            assert_eq!(tokens[i], expected_tokens[i]);
        }
        dir.close()?;

        Ok(())
    }

    #[test]
    fn should_lex_operators() -> Result<(), Error> {
        let expected_tokens = vec![
            OperatorToken::build_token(Operator::Addition, FilePosition::new(1, 1)),
            OperatorToken::build_token(Operator::Subtraction, FilePosition::new(1, 3)),
            OperatorToken::build_token(Operator::Not, FilePosition::new(1, 5)),
            OperatorToken::build_token(Operator::Negation, FilePosition::new(1, 7)),
            OperatorToken::build_token(Operator::BitwiseAnd, FilePosition::new(1, 9)),
            OperatorToken::build_token(Operator::Nand, FilePosition::new(1, 11)),
            OperatorToken::build_token(Operator::BitwiseOr, FilePosition::new(1, 14)),
            OperatorToken::build_token(Operator::Nor, FilePosition::new(1, 16)),
            OperatorToken::build_token(Operator::Xor, FilePosition::new(1, 19)),
            OperatorToken::build_token(Operator::Xnor, FilePosition::new(1, 21)),
            OperatorToken::build_token(Operator::Xnor, FilePosition::new(1, 24)),
            OperatorToken::build_token(Operator::Increment, FilePosition::new(1, 27)),
            OperatorToken::build_token(Operator::Decrement, FilePosition::new(1, 30)),
            OperatorToken::build_token(Operator::Exponentiation, FilePosition::new(1, 33)),
            OperatorToken::build_token(Operator::Multiplication, FilePosition::new(1, 36)),
            OperatorToken::build_token(Operator::Division, FilePosition::new(1, 38)),
            OperatorToken::build_token(Operator::Modulo, FilePosition::new(1, 40)),
            OperatorToken::build_token(Operator::LogicalRightShift, FilePosition::new(2, 1)),
            OperatorToken::build_token(Operator::LogicalLeftShift, FilePosition::new(2, 4)),
            OperatorToken::build_token(Operator::ArithmeticRightShift, FilePosition::new(2, 7)),
            OperatorToken::build_token(Operator::ArithmeticLeftShift, FilePosition::new(2, 11)),
            OperatorToken::build_token(Operator::LessThan, FilePosition::new(2, 15)),
            OperatorToken::build_token(Operator::LessThanOrEqualTo, FilePosition::new(2, 17)),
            OperatorToken::build_token(Operator::GreaterThan, FilePosition::new(2, 20)),
            OperatorToken::build_token(Operator::GreaterThanOrEqualTo, FilePosition::new(2, 22)),
            OperatorToken::build_token(Operator::Inside, FilePosition::new(2, 25)),
            OperatorToken::build_token(Operator::Distribution, FilePosition::new(2, 32)),
            OperatorToken::build_token(Operator::LogicalEquality, FilePosition::new(2, 37)),
            OperatorToken::build_token(Operator::LogicalInequality, FilePosition::new(2, 40)),
            OperatorToken::build_token(Operator::CaseEquality, FilePosition::new(2, 43)),
            OperatorToken::build_token(Operator::CaseInequality, FilePosition::new(2, 47)),
            OperatorToken::build_token(Operator::WildcardEquality, FilePosition::new(3, 1)),
            OperatorToken::build_token(Operator::WildcardInequality, FilePosition::new(3, 5)),
            OperatorToken::build_token(Operator::LogicalAnd, FilePosition::new(3, 9)),
            OperatorToken::build_token(Operator::LogicalOr, FilePosition::new(3, 12)),
            OperatorToken::build_token(Operator::Implication, FilePosition::new(3, 15)),
            OperatorToken::build_token(Operator::Equivalence, FilePosition::new(3, 18)),
            OperatorToken::build_token(Operator::BinaryAssignment, FilePosition::new(3, 22)),
            OperatorToken::build_token(Operator::AdditionAssignment, FilePosition::new(3, 24)),
            OperatorToken::build_token(Operator::SubtractionAssignment, FilePosition::new(3, 27)),
            OperatorToken::build_token(
                Operator::MultiplicationAssignment,
                FilePosition::new(3, 30),
            ),
            OperatorToken::build_token(Operator::DivisionAssignment, FilePosition::new(3, 33)),
            OperatorToken::build_token(Operator::ModuloAssignment, FilePosition::new(3, 36)),
            OperatorToken::build_token(Operator::BitwiseAndAssignment, FilePosition::new(3, 39)),
            OperatorToken::build_token(Operator::BitwiseXorAssignment, FilePosition::new(3, 42)),
            OperatorToken::build_token(Operator::BitwiseOrAssignment, FilePosition::new(3, 45)),
            OperatorToken::build_token(
                Operator::LogicalLeftShiftAssignment,
                FilePosition::new(4, 1),
            ),
            OperatorToken::build_token(
                Operator::LogicalRightShiftAssignment,
                FilePosition::new(4, 5),
            ),
            OperatorToken::build_token(
                Operator::ArithmeticLeftShiftAssignment,
                FilePosition::new(4, 9),
            ),
            OperatorToken::build_token(
                Operator::ArithmeticRightShiftAssignment,
                FilePosition::new(4, 14),
            ),
            Token::EOF(FilePosition::new(4, 18)),
        ];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(
            &dir,
            "+ - ! ~ & ~& | ~| ^ ~^ ^~ ++ -- ** * / %
>> << >>> <<< < <= > >= inside dist == != === !==
==? !=? && || -> <-> = += -= *= /= %= &= ^= |=
<<= >>= <<<= >>>=",
        )?;
        let mut lexer = Lexer::open(file_path.to_str().unwrap());

        let tokens = lexer.lex();

        assert_eq!(tokens.len(), expected_tokens.len());
        for i in 0..tokens.len() {
            assert_eq!(tokens[i], expected_tokens[i]);
        }
        dir.close()?;

        Ok(())
    }
}
