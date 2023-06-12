use std::cmp::Ordering;

use crate::char_reader::CharReader;
use crate::keywords::KEYWORD_SYMBOLS;
use crate::operators::OPERATOR_SYMBOLS;
use crate::punctuation::Punctuation;
use crate::token::{BuildToken, ErrorToken, Token, EscapedIdentifierToken};
use crate::token::{
    CharacterSequenceToken, KeywordToken, NumberToken, OperatorToken, PunctuationToken,
    StringLiteralToken, TokenFromSequence,
};
use crate::token_stream::TokenStream;

const LEXICAL_OPERATIONS: [LexerOperator; 9] = [
    LexerOperator::WhiteSpace,
    LexerOperator::Comment,
    LexerOperator::Operator,
    LexerOperator::Keyword,
    LexerOperator::Punctuation,
    LexerOperator::Number,
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
    pub fn new(row: usize, column: usize) -> FilePosition {
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

    pub fn lex(&mut self) -> TokenStream {
        let mut tokens = Vec::new();

        while self.can_read() {
            match self.lex_token() {
                Token::WhiteSpace | Token::Comment => (),
                token => tokens.push(token),
            }
        }

        tokens.push(Token::EOF(self.file_position()));

        TokenStream::new(tokens)
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
            LexerOperator::EscapedIdentifier => self.lex_escaped_identifier(),
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

    fn lex_escaped_identifier(&mut self) -> Result<Token, &'static str> {
        if self.peek()? != '\\' {
            return Err(
                "Escaped identifier must start with \\",
            );
        }

        let mut identifier = String::new();
        let file_position = self.file_position();
        identifier.push(self.read()?); // Read the \

        while self.can_read() && !self.peek()?.is_whitespace() {
            identifier.push(self.read()?);
        }

        if identifier.len() == 1 {
            return Err("Escaped identifier must not empty");
        }

        Ok(EscapedIdentifierToken::build_token(
            identifier,
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

    use crate::keywords::Keyword;
    use crate::operators::Operator;
    use crate::punctuation::Punctuation;
    use crate::token::{
        BuildToken, CharacterSequenceToken, ErrorToken, EscapedIdentifierToken, KeywordToken,
        NumberToken, OperatorToken, PunctuationToken, StringLiteralToken,
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
            Token::EOF(FilePosition::new(1, 7)),
        ];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(&dir, "abcXYZ")?;
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
    fn should_lex_escaped_identifier() -> Result<(), Error> {
        let expected_tokens = vec![
            EscapedIdentifierToken::build_token(
                String::from("\\@#art\\()"),
                FilePosition::new(1, 1),
            ),
            Token::EOF(FilePosition::new(2, 1)),
        ];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(&dir, "\\@#art\\()\n")?;
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
    fn should_lex_escaped_identifier_at_eof() -> Result<(), Error> {
        let expected_tokens = vec![
            EscapedIdentifierToken::build_token(
                String::from("\\@#art\\()"),
                FilePosition::new(1, 1),
            ),
            Token::EOF(FilePosition::new(1, 10)),
        ];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(&dir, "\\@#art\\()")?;
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

    #[test]
    fn should_lex_keywords() -> Result<(), Error> {
        let expected_tokens = vec![
            KeywordToken::build_token(Keyword::AcceptOn, FilePosition::new(1, 1)),
            KeywordToken::build_token(Keyword::Alias, FilePosition::new(2, 1)),
            KeywordToken::build_token(Keyword::Always, FilePosition::new(3, 1)),
            KeywordToken::build_token(Keyword::AlwaysComb, FilePosition::new(4, 1)),
            KeywordToken::build_token(Keyword::AlwaysFF, FilePosition::new(5, 1)),
            KeywordToken::build_token(Keyword::AlwaysLatch, FilePosition::new(6, 1)),
            KeywordToken::build_token(Keyword::And, FilePosition::new(7, 1)),
            KeywordToken::build_token(Keyword::Assert, FilePosition::new(8, 1)),
            KeywordToken::build_token(Keyword::Assign, FilePosition::new(9, 1)),
            KeywordToken::build_token(Keyword::Assume, FilePosition::new(10, 1)),
            KeywordToken::build_token(Keyword::Automatic, FilePosition::new(11, 1)),
            KeywordToken::build_token(Keyword::Before, FilePosition::new(12, 1)),
            KeywordToken::build_token(Keyword::Begin, FilePosition::new(13, 1)),
            KeywordToken::build_token(Keyword::Bind, FilePosition::new(14, 1)),
            KeywordToken::build_token(Keyword::Bins, FilePosition::new(15, 1)),
            KeywordToken::build_token(Keyword::Binsof, FilePosition::new(16, 1)),
            KeywordToken::build_token(Keyword::Bit, FilePosition::new(17, 1)),
            KeywordToken::build_token(Keyword::Break, FilePosition::new(18, 1)),
            KeywordToken::build_token(Keyword::Buf, FilePosition::new(19, 1)),
            KeywordToken::build_token(Keyword::Bufif0, FilePosition::new(20, 1)),
            KeywordToken::build_token(Keyword::Bufif1, FilePosition::new(21, 1)),
            KeywordToken::build_token(Keyword::Byte, FilePosition::new(22, 1)),
            KeywordToken::build_token(Keyword::Case, FilePosition::new(23, 1)),
            KeywordToken::build_token(Keyword::Casex, FilePosition::new(24, 1)),
            KeywordToken::build_token(Keyword::Casez, FilePosition::new(25, 1)),
            KeywordToken::build_token(Keyword::Cell, FilePosition::new(26, 1)),
            KeywordToken::build_token(Keyword::Chandle, FilePosition::new(27, 1)),
            KeywordToken::build_token(Keyword::Checker, FilePosition::new(28, 1)),
            KeywordToken::build_token(Keyword::Class, FilePosition::new(29, 1)),
            KeywordToken::build_token(Keyword::Clocking, FilePosition::new(30, 1)),
            KeywordToken::build_token(Keyword::Cmos, FilePosition::new(31, 1)),
            KeywordToken::build_token(Keyword::Config, FilePosition::new(32, 1)),
            KeywordToken::build_token(Keyword::Const, FilePosition::new(33, 1)),
            KeywordToken::build_token(Keyword::Constraint, FilePosition::new(34, 1)),
            KeywordToken::build_token(Keyword::Context, FilePosition::new(35, 1)),
            KeywordToken::build_token(Keyword::Continue, FilePosition::new(36, 1)),
            KeywordToken::build_token(Keyword::Cover, FilePosition::new(37, 1)),
            KeywordToken::build_token(Keyword::Covergroup, FilePosition::new(38, 1)),
            KeywordToken::build_token(Keyword::Coverpoint, FilePosition::new(39, 1)),
            KeywordToken::build_token(Keyword::Cross, FilePosition::new(40, 1)),
            KeywordToken::build_token(Keyword::Deassign, FilePosition::new(41, 1)),
            KeywordToken::build_token(Keyword::Default, FilePosition::new(42, 1)),
            KeywordToken::build_token(Keyword::Defparam, FilePosition::new(43, 1)),
            KeywordToken::build_token(Keyword::Design, FilePosition::new(44, 1)),
            KeywordToken::build_token(Keyword::Disable, FilePosition::new(45, 1)),
            KeywordToken::build_token(Keyword::Do, FilePosition::new(46, 1)),
            KeywordToken::build_token(Keyword::Edge, FilePosition::new(47, 1)),
            KeywordToken::build_token(Keyword::Else, FilePosition::new(48, 1)),
            KeywordToken::build_token(Keyword::End, FilePosition::new(49, 1)),
            KeywordToken::build_token(Keyword::Endcase, FilePosition::new(50, 1)),
            KeywordToken::build_token(Keyword::Endchecker, FilePosition::new(51, 1)),
            KeywordToken::build_token(Keyword::Endclass, FilePosition::new(52, 1)),
            KeywordToken::build_token(Keyword::Endclocking, FilePosition::new(53, 1)),
            KeywordToken::build_token(Keyword::Endconfig, FilePosition::new(54, 1)),
            KeywordToken::build_token(Keyword::Endfunction, FilePosition::new(55, 1)),
            KeywordToken::build_token(Keyword::Endgenerate, FilePosition::new(56, 1)),
            KeywordToken::build_token(Keyword::Endgroup, FilePosition::new(57, 1)),
            KeywordToken::build_token(Keyword::Endinterface, FilePosition::new(58, 1)),
            KeywordToken::build_token(Keyword::Endmodule, FilePosition::new(59, 1)),
            KeywordToken::build_token(Keyword::Endpackage, FilePosition::new(60, 1)),
            KeywordToken::build_token(Keyword::Endprimitive, FilePosition::new(61, 1)),
            KeywordToken::build_token(Keyword::Endprogram, FilePosition::new(62, 1)),
            KeywordToken::build_token(Keyword::Endproperty, FilePosition::new(63, 1)),
            KeywordToken::build_token(Keyword::Endspecify, FilePosition::new(64, 1)),
            KeywordToken::build_token(Keyword::Endsequence, FilePosition::new(65, 1)),
            KeywordToken::build_token(Keyword::Endtable, FilePosition::new(66, 1)),
            KeywordToken::build_token(Keyword::Endtask, FilePosition::new(67, 1)),
            KeywordToken::build_token(Keyword::Enum, FilePosition::new(68, 1)),
            KeywordToken::build_token(Keyword::Event, FilePosition::new(69, 1)),
            KeywordToken::build_token(Keyword::Eventually, FilePosition::new(70, 1)),
            KeywordToken::build_token(Keyword::Expect, FilePosition::new(71, 1)),
            KeywordToken::build_token(Keyword::Export, FilePosition::new(72, 1)),
            KeywordToken::build_token(Keyword::Extends, FilePosition::new(73, 1)),
            KeywordToken::build_token(Keyword::Extern, FilePosition::new(74, 1)),
            KeywordToken::build_token(Keyword::Final, FilePosition::new(75, 1)),
            KeywordToken::build_token(Keyword::FirstMatch, FilePosition::new(76, 1)),
            KeywordToken::build_token(Keyword::For, FilePosition::new(77, 1)),
            KeywordToken::build_token(Keyword::Force, FilePosition::new(78, 1)),
            KeywordToken::build_token(Keyword::Foreach, FilePosition::new(79, 1)),
            KeywordToken::build_token(Keyword::Forever, FilePosition::new(80, 1)),
            KeywordToken::build_token(Keyword::Fork, FilePosition::new(81, 1)),
            KeywordToken::build_token(Keyword::Forkjoin, FilePosition::new(82, 1)),
            KeywordToken::build_token(Keyword::Function, FilePosition::new(83, 1)),
            KeywordToken::build_token(Keyword::Generate, FilePosition::new(84, 1)),
            KeywordToken::build_token(Keyword::Genvar, FilePosition::new(85, 1)),
            KeywordToken::build_token(Keyword::Global, FilePosition::new(86, 1)),
            KeywordToken::build_token(Keyword::Highz0, FilePosition::new(87, 1)),
            KeywordToken::build_token(Keyword::Highz1, FilePosition::new(88, 1)),
            KeywordToken::build_token(Keyword::If, FilePosition::new(89, 1)),
            KeywordToken::build_token(Keyword::Iff, FilePosition::new(90, 1)),
            KeywordToken::build_token(Keyword::Ifnone, FilePosition::new(91, 1)),
            KeywordToken::build_token(Keyword::IgnoreBins, FilePosition::new(92, 1)),
            KeywordToken::build_token(Keyword::IllegalBins, FilePosition::new(93, 1)),
            KeywordToken::build_token(Keyword::Implements, FilePosition::new(94, 1)),
            KeywordToken::build_token(Keyword::Implies, FilePosition::new(95, 1)),
            KeywordToken::build_token(Keyword::Import, FilePosition::new(96, 1)),
            KeywordToken::build_token(Keyword::Incdir, FilePosition::new(97, 1)),
            KeywordToken::build_token(Keyword::Include, FilePosition::new(98, 1)),
            KeywordToken::build_token(Keyword::Initial, FilePosition::new(99, 1)),
            KeywordToken::build_token(Keyword::Inout, FilePosition::new(100, 1)),
            KeywordToken::build_token(Keyword::Input, FilePosition::new(101, 1)),
            KeywordToken::build_token(Keyword::Instance, FilePosition::new(102, 1)),
            KeywordToken::build_token(Keyword::Int, FilePosition::new(103, 1)),
            KeywordToken::build_token(Keyword::Integer, FilePosition::new(104, 1)),
            KeywordToken::build_token(Keyword::Interconnect, FilePosition::new(105, 1)),
            KeywordToken::build_token(Keyword::Interface, FilePosition::new(106, 1)),
            KeywordToken::build_token(Keyword::Intersect, FilePosition::new(107, 1)),
            KeywordToken::build_token(Keyword::Join, FilePosition::new(108, 1)),
            KeywordToken::build_token(Keyword::JoinAny, FilePosition::new(109, 1)),
            KeywordToken::build_token(Keyword::JoinNone, FilePosition::new(110, 1)),
            KeywordToken::build_token(Keyword::Large, FilePosition::new(111, 1)),
            KeywordToken::build_token(Keyword::Let, FilePosition::new(112, 1)),
            KeywordToken::build_token(Keyword::Liblist, FilePosition::new(113, 1)),
            KeywordToken::build_token(Keyword::Library, FilePosition::new(114, 1)),
            KeywordToken::build_token(Keyword::Local, FilePosition::new(115, 1)),
            KeywordToken::build_token(Keyword::Localparam, FilePosition::new(116, 1)),
            KeywordToken::build_token(Keyword::Logic, FilePosition::new(117, 1)),
            KeywordToken::build_token(Keyword::Longint, FilePosition::new(118, 1)),
            KeywordToken::build_token(Keyword::Macromodule, FilePosition::new(119, 1)),
            KeywordToken::build_token(Keyword::Matches, FilePosition::new(120, 1)),
            KeywordToken::build_token(Keyword::Medium, FilePosition::new(121, 1)),
            KeywordToken::build_token(Keyword::Modport, FilePosition::new(122, 1)),
            KeywordToken::build_token(Keyword::Module, FilePosition::new(123, 1)),
            KeywordToken::build_token(Keyword::Nand, FilePosition::new(124, 1)),
            KeywordToken::build_token(Keyword::Negedge, FilePosition::new(125, 1)),
            KeywordToken::build_token(Keyword::Nettype, FilePosition::new(126, 1)),
            KeywordToken::build_token(Keyword::New, FilePosition::new(127, 1)),
            KeywordToken::build_token(Keyword::Nexttime, FilePosition::new(128, 1)),
            KeywordToken::build_token(Keyword::Nmos, FilePosition::new(129, 1)),
            KeywordToken::build_token(Keyword::Nor, FilePosition::new(130, 1)),
            KeywordToken::build_token(Keyword::Noshowcancelled, FilePosition::new(131, 1)),
            KeywordToken::build_token(Keyword::Not, FilePosition::new(132, 1)),
            KeywordToken::build_token(Keyword::Notif0, FilePosition::new(133, 1)),
            KeywordToken::build_token(Keyword::Notif1, FilePosition::new(134, 1)),
            KeywordToken::build_token(Keyword::Null, FilePosition::new(135, 1)),
            KeywordToken::build_token(Keyword::Or, FilePosition::new(136, 1)),
            KeywordToken::build_token(Keyword::Output, FilePosition::new(137, 1)),
            KeywordToken::build_token(Keyword::Package, FilePosition::new(138, 1)),
            KeywordToken::build_token(Keyword::Packed, FilePosition::new(139, 1)),
            KeywordToken::build_token(Keyword::Parameter, FilePosition::new(140, 1)),
            KeywordToken::build_token(Keyword::Pmos, FilePosition::new(141, 1)),
            KeywordToken::build_token(Keyword::Posedge, FilePosition::new(142, 1)),
            KeywordToken::build_token(Keyword::Primitive, FilePosition::new(143, 1)),
            KeywordToken::build_token(Keyword::Priority, FilePosition::new(144, 1)),
            KeywordToken::build_token(Keyword::Program, FilePosition::new(145, 1)),
            KeywordToken::build_token(Keyword::Property, FilePosition::new(146, 1)),
            KeywordToken::build_token(Keyword::Protected, FilePosition::new(147, 1)),
            KeywordToken::build_token(Keyword::Pull0, FilePosition::new(148, 1)),
            KeywordToken::build_token(Keyword::Pull1, FilePosition::new(149, 1)),
            KeywordToken::build_token(Keyword::Pulldown, FilePosition::new(150, 1)),
            KeywordToken::build_token(Keyword::Pullup, FilePosition::new(151, 1)),
            KeywordToken::build_token(Keyword::PulsestyleOndetect, FilePosition::new(152, 1)),
            KeywordToken::build_token(Keyword::PulsestyleOnevent, FilePosition::new(153, 1)),
            KeywordToken::build_token(Keyword::Pure, FilePosition::new(154, 1)),
            KeywordToken::build_token(Keyword::Rand, FilePosition::new(155, 1)),
            KeywordToken::build_token(Keyword::Randc, FilePosition::new(156, 1)),
            KeywordToken::build_token(Keyword::Randcase, FilePosition::new(157, 1)),
            KeywordToken::build_token(Keyword::Randsequence, FilePosition::new(158, 1)),
            KeywordToken::build_token(Keyword::Rcmos, FilePosition::new(159, 1)),
            KeywordToken::build_token(Keyword::Real, FilePosition::new(160, 1)),
            KeywordToken::build_token(Keyword::Realtime, FilePosition::new(161, 1)),
            KeywordToken::build_token(Keyword::Ref, FilePosition::new(162, 1)),
            KeywordToken::build_token(Keyword::Reg, FilePosition::new(163, 1)),
            KeywordToken::build_token(Keyword::RejectOn, FilePosition::new(164, 1)),
            KeywordToken::build_token(Keyword::Release, FilePosition::new(165, 1)),
            KeywordToken::build_token(Keyword::Repeat, FilePosition::new(166, 1)),
            KeywordToken::build_token(Keyword::Restrict, FilePosition::new(167, 1)),
            KeywordToken::build_token(Keyword::Return, FilePosition::new(168, 1)),
            KeywordToken::build_token(Keyword::Rnmos, FilePosition::new(169, 1)),
            KeywordToken::build_token(Keyword::Rpmos, FilePosition::new(170, 1)),
            KeywordToken::build_token(Keyword::Rtran, FilePosition::new(171, 1)),
            KeywordToken::build_token(Keyword::Rtranif0, FilePosition::new(172, 1)),
            KeywordToken::build_token(Keyword::Rtranif1, FilePosition::new(173, 1)),
            KeywordToken::build_token(Keyword::SAlways, FilePosition::new(174, 1)),
            KeywordToken::build_token(Keyword::SEventually, FilePosition::new(175, 1)),
            KeywordToken::build_token(Keyword::SNexttime, FilePosition::new(176, 1)),
            KeywordToken::build_token(Keyword::SUntil, FilePosition::new(177, 1)),
            KeywordToken::build_token(Keyword::SUntilWith, FilePosition::new(178, 1)),
            KeywordToken::build_token(Keyword::Scalared, FilePosition::new(179, 1)),
            KeywordToken::build_token(Keyword::Sequence, FilePosition::new(180, 1)),
            KeywordToken::build_token(Keyword::Shortint, FilePosition::new(181, 1)),
            KeywordToken::build_token(Keyword::Shortreal, FilePosition::new(182, 1)),
            KeywordToken::build_token(Keyword::Showcancelled, FilePosition::new(183, 1)),
            KeywordToken::build_token(Keyword::Signed, FilePosition::new(184, 1)),
            KeywordToken::build_token(Keyword::Small, FilePosition::new(185, 1)),
            KeywordToken::build_token(Keyword::Soft, FilePosition::new(186, 1)),
            KeywordToken::build_token(Keyword::Solve, FilePosition::new(187, 1)),
            KeywordToken::build_token(Keyword::Specify, FilePosition::new(188, 1)),
            KeywordToken::build_token(Keyword::Specparam, FilePosition::new(189, 1)),
            KeywordToken::build_token(Keyword::Static, FilePosition::new(190, 1)),
            KeywordToken::build_token(Keyword::String, FilePosition::new(191, 1)),
            KeywordToken::build_token(Keyword::Strong, FilePosition::new(192, 1)),
            KeywordToken::build_token(Keyword::Strong0, FilePosition::new(193, 1)),
            KeywordToken::build_token(Keyword::Strong1, FilePosition::new(194, 1)),
            KeywordToken::build_token(Keyword::Struct, FilePosition::new(195, 1)),
            KeywordToken::build_token(Keyword::Super, FilePosition::new(196, 1)),
            KeywordToken::build_token(Keyword::Supply0, FilePosition::new(197, 1)),
            KeywordToken::build_token(Keyword::Supply1, FilePosition::new(198, 1)),
            KeywordToken::build_token(Keyword::SyncAcceptOn, FilePosition::new(199, 1)),
            KeywordToken::build_token(Keyword::SyncRejectOn, FilePosition::new(200, 1)),
            KeywordToken::build_token(Keyword::Table, FilePosition::new(201, 1)),
            KeywordToken::build_token(Keyword::Tagged, FilePosition::new(202, 1)),
            KeywordToken::build_token(Keyword::Task, FilePosition::new(203, 1)),
            KeywordToken::build_token(Keyword::This, FilePosition::new(204, 1)),
            KeywordToken::build_token(Keyword::Throughout, FilePosition::new(205, 1)),
            KeywordToken::build_token(Keyword::Time, FilePosition::new(206, 1)),
            KeywordToken::build_token(Keyword::Timeprecision, FilePosition::new(207, 1)),
            KeywordToken::build_token(Keyword::Timeunit, FilePosition::new(208, 1)),
            KeywordToken::build_token(Keyword::Tran, FilePosition::new(209, 1)),
            KeywordToken::build_token(Keyword::Tranif0, FilePosition::new(210, 1)),
            KeywordToken::build_token(Keyword::Tranif1, FilePosition::new(211, 1)),
            KeywordToken::build_token(Keyword::Tri, FilePosition::new(212, 1)),
            KeywordToken::build_token(Keyword::Tri0, FilePosition::new(213, 1)),
            KeywordToken::build_token(Keyword::Tri1, FilePosition::new(214, 1)),
            KeywordToken::build_token(Keyword::Triand, FilePosition::new(215, 1)),
            KeywordToken::build_token(Keyword::Trior, FilePosition::new(216, 1)),
            KeywordToken::build_token(Keyword::Trireg, FilePosition::new(217, 1)),
            KeywordToken::build_token(Keyword::Type, FilePosition::new(218, 1)),
            KeywordToken::build_token(Keyword::Typedef, FilePosition::new(219, 1)),
            KeywordToken::build_token(Keyword::Union, FilePosition::new(220, 1)),
            KeywordToken::build_token(Keyword::Unique, FilePosition::new(221, 1)),
            KeywordToken::build_token(Keyword::Unique0, FilePosition::new(222, 1)),
            KeywordToken::build_token(Keyword::Unsigned, FilePosition::new(223, 1)),
            KeywordToken::build_token(Keyword::Until, FilePosition::new(224, 1)),
            KeywordToken::build_token(Keyword::UntilWith, FilePosition::new(225, 1)),
            KeywordToken::build_token(Keyword::Untyped, FilePosition::new(226, 1)),
            KeywordToken::build_token(Keyword::Use, FilePosition::new(227, 1)),
            KeywordToken::build_token(Keyword::Uwire, FilePosition::new(228, 1)),
            KeywordToken::build_token(Keyword::Var, FilePosition::new(229, 1)),
            KeywordToken::build_token(Keyword::Vectored, FilePosition::new(230, 1)),
            KeywordToken::build_token(Keyword::Virtual, FilePosition::new(231, 1)),
            KeywordToken::build_token(Keyword::Void, FilePosition::new(232, 1)),
            KeywordToken::build_token(Keyword::Wait, FilePosition::new(233, 1)),
            KeywordToken::build_token(Keyword::WaitOrder, FilePosition::new(234, 1)),
            KeywordToken::build_token(Keyword::Wand, FilePosition::new(235, 1)),
            KeywordToken::build_token(Keyword::Weak, FilePosition::new(236, 1)),
            KeywordToken::build_token(Keyword::Weak0, FilePosition::new(237, 1)),
            KeywordToken::build_token(Keyword::Weak1, FilePosition::new(238, 1)),
            KeywordToken::build_token(Keyword::While, FilePosition::new(239, 1)),
            KeywordToken::build_token(Keyword::Wildcard, FilePosition::new(240, 1)),
            KeywordToken::build_token(Keyword::Wire, FilePosition::new(241, 1)),
            KeywordToken::build_token(Keyword::With, FilePosition::new(242, 1)),
            KeywordToken::build_token(Keyword::Within, FilePosition::new(243, 1)),
            KeywordToken::build_token(Keyword::Wor, FilePosition::new(244, 1)),
            KeywordToken::build_token(Keyword::Xnor, FilePosition::new(245, 1)),
            KeywordToken::build_token(Keyword::Xor, FilePosition::new(246, 1)),
            Token::EOF(FilePosition::new(246, 4)),
        ];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(
            &dir,
            "accept_on
alias
always
always_comb
always_ff
always_latch
and
assert
assign
assume
automatic
before
begin
bind
bins
binsof
bit
break
buf
bufif0
bufif1
byte
case
casex
casez
cell
chandle
checker
class
clocking
cmos
config
const
constraint
context
continue
cover
covergroup
coverpoint
cross
deassign
default
defparam
design
disable
do
edge
else
end
endcase
endchecker
endclass
endclocking
endconfig
endfunction
endgenerate
endgroup
endinterface
endmodule
endpackage
endprimitive
endprogram
endproperty
endspecify
endsequence
endtable
endtask
enum
event
eventually
expect
export
extends
extern
final
first_match
for
force
foreach
forever
fork
forkjoin
function
generate
genvar
global
highz0
highz1
if
iff
ifnone
ignore_bins
illegal_bins
implements
implies
import
incdir
include
initial
inout
input
instance
int
integer
interconnect
interface
intersect
join
join_any
join_none
large
let
liblist
library
local
localparam
logic
longint
macromodule
matches
medium
modport
module
nand
negedge
nettype
new
nexttime
nmos
nor
noshowcancelled
not
notif0
notif1
null
or
output
package
packed
parameter
pmos
posedge
primitive
priority
program
property
protected
pull0
pull1
pulldown
pullup
pulsestyle_ondetect
pulsestyle_onevent
pure
rand
randc
randcase
randsequence
rcmos
real
realtime
ref
reg
reject_on
release
repeat
restrict
return
rnmos
rpmos
rtran
rtranif0
rtranif1
s_always
s_eventually
s_nexttime
s_until
s_until_with
scalared
sequence
shortint
shortreal
showcancelled
signed
small
soft
solve
specify
specparam
static
string
strong
strong0
strong1
struct
super
supply0
supply1
sync_accept_on
sync_reject_on
table
tagged
task
this
throughout
time
timeprecision
timeunit
tran
tranif0
tranif1
tri
tri0
tri1
triand
trior
trireg
type
typedef
union
unique
unique0
unsigned
until
until_with
untyped
use
uwire
var
vectored
virtual
void
wait
wait_order
wand
weak
weak0
weak1
while
wildcard
wire
with
within
wor
xnor
xor",
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
    fn should_lex_punctuation() -> Result<(), Error> {
        let expected_tokens = vec![
            PunctuationToken::build_token(Punctuation::Asperand, FilePosition::new(1, 1)),
            PunctuationToken::build_token(Punctuation::Pound, FilePosition::new(2, 1)),
            PunctuationToken::build_token(Punctuation::Dollar, FilePosition::new(3, 1)),
            PunctuationToken::build_token(Punctuation::LeftParentheses, FilePosition::new(4, 1)),
            PunctuationToken::build_token(Punctuation::RightParentheses, FilePosition::new(5, 1)),
            PunctuationToken::build_token(Punctuation::LeftBracket, FilePosition::new(6, 1)),
            PunctuationToken::build_token(Punctuation::RightBracket, FilePosition::new(7, 1)),
            PunctuationToken::build_token(Punctuation::LeftBrace, FilePosition::new(8, 1)),
            PunctuationToken::build_token(Punctuation::RightBrace, FilePosition::new(9, 1)),
            PunctuationToken::build_token(Punctuation::BackSlash, FilePosition::new(10, 1)),
            PunctuationToken::build_token(Punctuation::Semicolon, FilePosition::new(11, 1)),
            PunctuationToken::build_token(Punctuation::Colon, FilePosition::new(12, 1)),
            PunctuationToken::build_token(Punctuation::QuestionMark, FilePosition::new(13, 1)),
            PunctuationToken::build_token(Punctuation::Backtick, FilePosition::new(14, 1)),
            PunctuationToken::build_token(Punctuation::Period, FilePosition::new(15, 1)),
            PunctuationToken::build_token(Punctuation::Comma, FilePosition::new(16, 1)),
            PunctuationToken::build_token(Punctuation::Apostrophe, FilePosition::new(17, 1)),
            PunctuationToken::build_token(Punctuation::Underscore, FilePosition::new(18, 1)),
            Token::EOF(FilePosition::new(18, 2)),
        ];
        let dir = tempdir()?;
        let file_path = create_temporary_verilog_file(
            &dir,
            "@
#
$
(
)
[
]
{
}
\\
;
:
?
`
.
,
'
_",
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
