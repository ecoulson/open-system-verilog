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

// TODO: If a file is larger than usize::MAX this will cause issues for reading
// the file. Should really just rely on modular arithmetic
impl CharReader {
    pub fn open(file_path: &str) -> CharReader {
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

    pub fn has_chars(&mut self) -> bool {
        !self.peek_char().is_none()
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
        self.buffer.fill(0);
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

#[cfg(test)]
mod tests {
    use super::{CharReader, BUFFER_SIZE};
    use std::io::prelude::Write;
    use std::io::Error;
    use std::path::PathBuf;
    use std::fs::File;
    use tempfile::{tempdir, TempDir};

    fn create_test_file(
        dir: &TempDir,
        file_name: &str,
        block_count: usize,
    ) -> Result<PathBuf, Error> {
        let file_path = dir.path().join(file_name);
        let mut file = File::create(&file_path)?;
        let mut content: [u8; BUFFER_SIZE] = [b'6'; BUFFER_SIZE];

        for i in 0..block_count {
            let block_symbol = i as u8 + b'0';
            content.fill(block_symbol);
            file.write(&content)?;
        }

        dbg!(File::open(file_path.to_str().unwrap())?);
        Ok(file_path)
    }

    #[test]
    fn read_one_buffer() -> Result<(), Error> {
        let dir = tempdir()?;
        let file_path = create_test_file(&dir, "single_block.txt", 1)?;
        let file_path = file_path.to_str().unwrap();

        let mut reader = CharReader::open(file_path);

        while reader.has_chars() {
            let char = (reader.get_position() / BUFFER_SIZE) as u8 + b'0';
            assert_eq!(reader.read_char().unwrap(), char::from(char));
        }

        assert_eq!(reader.get_position(), BUFFER_SIZE);
        assert_eq!(reader.block, 1);

        Ok(())
    }

    #[test]
    fn read_multiple_buffers() -> Result<(), Error> {
        const BLOCKS: usize = 5;
        const FILE_SIZE: usize = BUFFER_SIZE * BLOCKS;

        let dir = tempdir()?;
        let file_path = create_test_file(&dir, "multiple_blocks.txt", BLOCKS)?;
        let file_path = file_path.to_str().unwrap();

        let mut reader = CharReader::open(file_path);

        while reader.has_chars() {
            let char = (reader.get_position() / BUFFER_SIZE) as u8 + b'0';
            assert_eq!(reader.read_char().unwrap(), char::from(char));
        }

        assert_eq!(reader.get_position(), FILE_SIZE);
        assert_eq!(reader.block, BLOCKS);

        Ok(())
    }

    #[test]
    fn read_and_seek_across_block() -> Result<(), Error> {
        const BLOCKS: usize = 5;
        const FILE_SIZE: usize = BUFFER_SIZE * BLOCKS;

        let dir = tempdir()?;
        let file_path = create_test_file(&dir, "multiple_blocks.txt", BLOCKS)?;
        let file_path = file_path.to_str().unwrap();

        let mut reader = CharReader::open(file_path);

        while reader.has_chars() {
            let char = (reader.get_position() / BUFFER_SIZE) as u8 + b'0';
            assert_eq!(reader.read_char().unwrap(), char::from(char));
        }

        let mut reader = CharReader::open(file_path);
        reader.seek_from_start(BUFFER_SIZE);
        reader.seek_from_start(BUFFER_SIZE - 1);

        while reader.has_chars() {
            let char = (reader.get_position() / BUFFER_SIZE) as u8 + b'0';
            assert_eq!(reader.read_char().unwrap(), char::from(char));
        }

        assert_eq!(reader.get_position(), FILE_SIZE);
        assert_eq!(reader.block, BLOCKS);

        Ok(())
    }
}
