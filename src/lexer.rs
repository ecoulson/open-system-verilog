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
    LexerOperator::Number,
    LexerOperator::StringLiteral,
    LexerOperator::CharacterSequence,
    LexerOperator::Operator,
    LexerOperator::Keyword,
    LexerOperator::Punctuation,
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


#[derive(Debug)]
pub struct FilePosition {
    column: usize,
    row: usize,
}

impl Lexer {
    pub fn open(file_path: &String) -> Lexer {
        Lexer {
            char_reader: CharReader::open(file_path),
            mark: None,
            column: 0,
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

        while !self.can_read() {
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
        let mut best_mark = Mark::build(0, 1, 0);

        for operator in LEXICAL_OPERATIONS {
            self.mark();
            let token = self.execute_lexical_operation(operator);
            let mark = Mark::build(self.position(), self.row, self.column);
            self.go_to_mark();

            if best_mark.position < mark.position {
                best_mark = mark;
                best_token = token;
            }
        }

        self.go_to(best_mark);

        best_token
    }

    fn file_position(&self) -> FilePosition {
        FilePosition {
            row: self.row,
            column: self.column,
        }
    }

    fn can_read(&mut self) -> bool {
        self.char_reader.has_chars()
    }

    fn lex_white_space(&mut self) -> Result<Token, &'static str> {
        if !self.peek()?.is_whitespace() {
            return Err("Not a sequence of white space characters");
        }

        while !self.can_read() && self.peek()?.is_whitespace() {
            self.read()?;
        }

        Ok(Token::WhiteSpace)
    }

    fn move_to_new_line(&mut self) {
        self.row += 1;
        self.column = 0;
    }

    fn lex_comments(&mut self) -> Result<Token, &'static str> {
        if self.read()? != '/' {
            return Err("Does not start with slash");
        }

        match self.read()? {
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

        while self.peek()?.is_digit(10) {
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

        if self.read()? != '\"' {
            return Err("String literal must start with \"");
        }

        while !self.can_read() && self.peek()? != '"' {
            let ch = self.read()?;
            match ch {
                '\\' => string_literal.push(self.read_escaped_character()?),
                _ => string_literal.push(ch),
            }
        }

        if self.can_read() {
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

        while !self.can_read() && self.peek()?.is_alphabetic() {
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

        let best_length = best_sequence.unwrap().len();
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
        match sequence.chars().count().cmp(&sequence.chars().count()) {
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

        match self.read()? {
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
        }
    }
}
