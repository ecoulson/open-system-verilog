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

pub struct Lexer {
    char_reader: CharReader,
    marked_position: Option<usize>,
}

impl Lexer {
    pub fn open(file_path: &String) -> Lexer {
        Lexer {
            char_reader: CharReader::open(file_path),
            marked_position: None,
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
            Some(ch) => Ok(ch),
        }
    }

    fn position(&self) -> usize {
        self.char_reader.get_position()
    }

    fn go_to(&mut self, position: usize) {
        self.char_reader.seek_from_start(position)
    }

    fn mark(&mut self) {
        self.marked_position = Some(self.position());
    }

    fn go_to_mark(&mut self) {
        if self.marked_position.is_none() {
            return;
        }

        self.go_to(self.marked_position.unwrap());
    }

    pub fn lex(&mut self) -> Vec<Token> {
        let mut tokens = Vec::new();

        while !self.is_at_eof() {
            match self.lex_token() {
                Token::WhiteSpace | Token::Comment => (),
                token => tokens.push(token),
            }
        }

        tokens.push(Token::EOF);

        tokens
    }

    fn execute_lexical_operation(&mut self, operation: LexerOperator) -> Token {
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
            Err(message) => ErrorToken::build_token(message),
            Ok(token) => token,
        }
    }

    fn lex_token(&mut self) -> Token {
        let mut best_token = ErrorToken::build_token("Failed to read any characters");
        let mut best_position = 0;

        for operator in LEXICAL_OPERATIONS {
            self.mark();
            let token = self.execute_lexical_operation(operator);
            let position = self.position();
            self.go_to_mark();

            if best_position < position {
                best_position = position;
                best_token = token;
            }
        }

        self.go_to(best_position);

        best_token
    }

    fn is_at_eof(&mut self) -> bool {
        self.char_reader.peek_char().is_none()
    }

    fn lex_white_space(&mut self) -> Result<Token, &'static str> {
        if !self.read()?.is_whitespace() {
            return Err(
                "Not a sequence of white space characters",
            );
        }

        while !self.is_at_eof() && self.peek()?.is_whitespace() {
            self.read()?;
        }

        Ok(Token::WhiteSpace)
    }

    fn lex_comments(&mut self) -> Result<Token, &'static str> {
        if self.read()? != '/' {
            return Err("Does not start with slash");
        }

        match self.read()? {
            '/' => self.lex_line_comment(),
            '*' => self.lex_block_comment(),
            _ => Err(
                "Slash is not followed by slash or astrix",
            ),
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

        while self.peek()?.is_digit(10) {
            number.push(self.read()?);
        }

        if number.is_empty() {
            return Err("Not a number");
        }

        Ok(NumberToken::build_token(number))
    }

    fn lex_string_literal(&mut self) -> Result<Token, &'static str> {
        let mut string_literal = String::new();

        if self.read()? != '\"' {
            return Err("String literal must start with \"");
        }

        while !self.is_at_eof() && self.peek()? != '"' {
            let ch = self.read()?;
            match ch {
                '\\' => string_literal.push(self.read_escaped_character()?),
                _ => string_literal.push(ch),
            }
        }

        if self.is_at_eof() {
            return Err("String literal is never closed");
        }

        self.read()?;

        Ok(StringLiteralToken::build_token(string_literal))
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
        escaped_identifier.push(self.read()?); // Read the \

        while !self.peek()?.is_whitespace() {
            escaped_identifier.push(self.read()?);
        }

        if escaped_identifier.len() == 1 {
            return Err("Escaped identifier must not empty");
        }

        Ok(CharacterSequenceToken::build_token(escaped_identifier))
    }

    fn lex_simple_identifier(&mut self) -> Result<Token, &'static str> {
        let mut character_sequence = String::from("");

        while !self.is_at_eof() && self.peek()?.is_alphabetic() {
            character_sequence.push(self.read()?);
        }

        if character_sequence.is_empty() {
            return Err("Not a character sequence");
        }

        Ok(CharacterSequenceToken::build_token(character_sequence))
    }

    fn lex_operator(&mut self) -> Result<Token, &'static str> {
        match self.get_best_sequence(&OPERATOR_SYMBOLS) {
            Some(sequence) => OperatorToken::from_sequence(sequence),
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

        self.go_to(self.position() + best_sequence.unwrap().len());

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
        match self.get_best_sequence(&KEYWORD_SYMBOLS) {
            Some(sequence) => KeywordToken::from_sequence(sequence),
            None => Err("Unrecognized keyword"),
        }
    }

    fn lex_punctuation(&mut self) -> Result<Token, &'static str> {
        match self.read()? {
            '@' => Ok(PunctuationToken::build_token(Punctuation::Asperand)),
            '#' => Ok(PunctuationToken::build_token(Punctuation::Pound)),
            '$' => Ok(PunctuationToken::build_token(Punctuation::Dollar)),
            '(' => Ok(PunctuationToken::build_token(Punctuation::LeftParentheses)),
            ')' => Ok(PunctuationToken::build_token(Punctuation::RightParentheses)),
            '[' => Ok(PunctuationToken::build_token(Punctuation::LeftBracket)),
            ']' => Ok(PunctuationToken::build_token(Punctuation::RightBracket)),
            '{' => Ok(PunctuationToken::build_token(Punctuation::LeftBrace)),
            '}' => Ok(PunctuationToken::build_token(Punctuation::RightBrace)),
            '\\' => Ok(PunctuationToken::build_token(Punctuation::BackSlash)),
            ';' => Ok(PunctuationToken::build_token(Punctuation::Semicolon)),
            ':' => Ok(PunctuationToken::build_token(Punctuation::Colon)),
            '?' => Ok(PunctuationToken::build_token(Punctuation::QuestionMark)),
            '`' => Ok(PunctuationToken::build_token(Punctuation::Backtick)),
            '.' => Ok(PunctuationToken::build_token(Punctuation::Period)),
            ',' => Ok(PunctuationToken::build_token(Punctuation::Comma)),
            '\'' => Ok(PunctuationToken::build_token(Punctuation::Apostrophe)),
            '_' => Ok(PunctuationToken::build_token(Punctuation::Underscore)),
            _ => Err("Unrecognized punctuation mark"),
        }
    }
}
