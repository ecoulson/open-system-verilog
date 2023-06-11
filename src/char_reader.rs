use std::fs::File;
use std::io::prelude::Seek;
use std::io::ErrorKind;
use std::io::Read;
use std::io::SeekFrom;
use std::process;

const BUFFER_SIZE: usize = 8192;
const BUFFER_SEEK_BACK: i64 = -8192;

#[derive(Debug)]
pub struct CharReader {
    block: usize,
    seek_position: usize,
    buffer: [u8; BUFFER_SIZE],
    file: File,
}
//
// TODO: If a file is larger than usize::MAX this will cause issues for reading
// the file. Should really just rely on modular arithmetic
impl CharReader {
    pub fn open(file_path: &String) -> CharReader {
        let file = File::open(file_path).unwrap_or_else(|error| {
            match error.kind() {
                ErrorKind::NotFound => eprintln!("File not found at path {}", file_path),
                ErrorKind::PermissionDenied => eprintln!(
                    "Do not have permission to access file at path {}",
                    file_path
                ),
                _ => eprintln!(
                    "Something went wrong opening the file at path {}",
                    file_path
                ),
            }
            process::exit(1)
        });

        let mut char_reader = CharReader {
            seek_position: 0,
            block: 0,
            buffer: [0; BUFFER_SIZE],
            file,
        };

        char_reader.read_into_buffer();

        char_reader
    }

    pub fn get_position(&self) -> usize {
        self.seek_position
    }

    pub fn peek_char(&mut self) -> Option<char> {
        let current_block = self.get_current_block();

        if self.seek_position % self.buffer.len() == 0 && self.block != current_block {
            self.read_into_buffer();
            self.block = current_block;
        }

        let peeked_char = self.get_current_char();

        match peeked_char {
            0 => None,
            _ => Some(char::from(peeked_char)),
        }
    }

    fn get_current_block(&self) -> usize {
        self.seek_position / self.buffer.len()
    }

    fn get_current_char(&self) -> u8 {
        self.buffer[self.seek_position % self.buffer.len()]
    }

    pub fn read_char(&mut self) -> Option<char> {
        let current_char = self.peek_char();
        self.seek_position += 1;

        current_char
    }

    pub fn seek_from_start(&mut self, n: usize) {
        if n == self.seek_position {
            return;
        }

        self.seek_position = n;
        let current_block = self.seek_position / self.buffer.len();

        if current_block == self.block {
            return;
        }

        if let Err(_) = self.file.seek(SeekFrom::Current(BUFFER_SEEK_BACK)) {
            eprintln!("Failed to seek back a buffered block");
            process::exit(1);
        }

        self.read_into_buffer();
    }

    fn read_into_buffer(&mut self) {
        self.file.read(&mut self.buffer).unwrap_or_else(|error| {
            match error.kind() {
                ErrorKind::Interrupted => {
                    eprintln!("IO Operation interrupted, consider implementing read retries")
                }
                _ => eprintln!("An error occured reading bytes into the buffer"),
            }
            process::exit(1)
        });
    }
}
