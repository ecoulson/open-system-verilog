use std::fs::File;
use std::io::prelude::Seek;
use std::io::ErrorKind;
use std::io::Read;
use std::io::SeekFrom;
use std::process;

const BUFFER_SIZE: usize = 8192;

#[derive(Debug)]
pub struct CharReader {
    block: usize,
    seek_position: u64,
    initialized: bool,
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
            initialized: false,
            buffer: [0; BUFFER_SIZE],
            file,
        };

        char_reader.read_into_buffer();

        char_reader
    }

    pub fn has_chars(&mut self) -> bool {
        !self.peek_char().is_none()
    }

    pub fn get_position(&self) -> u64 {
        self.seek_position
    }

    pub fn peek_char(&mut self) -> Option<char> {
        self.read_into_buffer();
        let peeked_char = self.get_current_char();

        match peeked_char {
            0 => None,
            _ => Some(char::from(peeked_char)),
        }
    }

    fn get_current_block(&self) -> usize {
        self.seek_position as usize / self.buffer.len()
    }

    fn get_current_char(&self) -> u8 {
        self.buffer[self.seek_position as usize % self.buffer.len()]
    }

    pub fn read_char(&mut self) -> Option<char> {
        let current_char = self.peek_char();
        self.seek_position += 1;

        current_char
    }

    pub fn seek_from_start(&mut self, n: u64) {
        if n == self.seek_position {
            return;
        }

        self.seek_position = n;
        let buffer_seek_position = self.get_current_block() * BUFFER_SIZE;
        let buffer_seek_position: u64 = buffer_seek_position.try_into().unwrap_or_else(|_| {
            eprintln!("Current seek position will overflow a u64");
            process::exit(1);
        });

        if let Err(_) = self.file.seek(SeekFrom::Start(buffer_seek_position)) {
            eprintln!("Failed to seek back a buffered block");
            process::exit(1);
        }

        self.read_into_buffer();
    }

    fn read_into_buffer(&mut self) {
        if self.initialized && self.get_current_block() == self.block {
            return;
        }

        self.buffer.fill(0);
        self.initialized = true;
        self.block = self.get_current_block();
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
    use std::fs::File;
    use std::io::prelude::Write;
    use std::io::Error;
    use std::path::PathBuf;
    use tempfile::{tempdir, TempDir};

    fn create_test_file(dir: &TempDir, file_name: &str, block_count: u8) -> Result<PathBuf, Error> {
        let file_path = dir.path().join(file_name);
        let mut file = File::create(&file_path)?;
        let mut content: [u8; BUFFER_SIZE] = [b'6'; BUFFER_SIZE];

        for i in 0..block_count {
            let block_symbol = i + b'0';
            content.fill(block_symbol);
            file.write(&content)?;
        }

        Ok(file_path)
    }

    fn get_expected_char(reader: &CharReader) -> char {
        let i: u8 = reader
            .get_current_block()
            .try_into()
            .expect("For the test cases avoid having more than 2^8 blocks");
        char::from(i + b'0')
    }

    #[test]
    fn read_one_buffer() -> Result<(), Error> {
        let dir = tempdir()?;
        let file_path = create_test_file(&dir, "single_block.txt", 1)?;
        let file_path = file_path.to_str().unwrap();

        let mut reader = CharReader::open(file_path);

        while reader.has_chars() {
            assert_eq!(reader.peek_char().unwrap(), get_expected_char(&reader));
            reader.read_char().unwrap();
        }

        assert_eq!(reader.get_position() as usize, BUFFER_SIZE);
        assert_eq!(reader.block, 1);
        dir.close()?;

        Ok(())
    }

    #[test]
    fn read_multiple_buffers() -> Result<(), Error> {
        const BLOCKS: u8 = 5;
        const FILE_SIZE: usize = BUFFER_SIZE * BLOCKS as usize;

        let dir = tempdir()?;
        let file_path = create_test_file(&dir, "multiple_blocks.txt", BLOCKS)?;
        let file_path = file_path.to_str().unwrap();

        let mut reader = CharReader::open(file_path);

        while reader.has_chars() {
            let expected_char = get_expected_char(&reader);
            assert_eq!(reader.read_char().unwrap(), expected_char);
        }

        assert_eq!(reader.get_position() as usize, FILE_SIZE);
        assert_eq!(reader.block, BLOCKS as usize);
        dir.close()?;

        Ok(())
    }

    #[test]
    fn read_and_seek_across_block() -> Result<(), Error> {
        const BLOCKS: u8 = 5;
        const FILE_SIZE: usize = BUFFER_SIZE * BLOCKS as usize;

        let dir = tempdir()?;
        let file_path = create_test_file(&dir, "multiple_blocks.txt", BLOCKS)?;
        let file_path = file_path.to_str().unwrap();

        let mut reader = CharReader::open(file_path);
        let new_seek_position: u64 = BUFFER_SIZE
            .try_into()
            .expect("Buffer size should fit in a u64");
        reader.seek_from_start(new_seek_position);
        reader.seek_from_start(new_seek_position - 1);

        while reader.has_chars() {
            let expected_char = get_expected_char(&reader);
            assert_eq!(reader.read_char().unwrap(), expected_char);
        }

        assert_eq!(reader.get_position() as usize, FILE_SIZE);
        assert_eq!(reader.block, BLOCKS as usize);
        dir.close()?;

        Ok(())
    }
}
