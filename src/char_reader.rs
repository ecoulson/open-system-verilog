use std::error::Error;
use std::fs::File;
use std::io::prelude::Seek;
use std::io::Read;
use std::io::SeekFrom;
use std::num::TryFromIntError;

const BUFFER_SIZE: usize = 8192;

#[derive(Debug)]
pub struct CharReader {
    block: usize,
    seek_position: u64,
    initialized: bool,
    buffer: [u8; BUFFER_SIZE],
    file: File,
}

#[derive(Debug)]
pub enum CharReaderError {
    IO(std::io::Error),
    Overflow(TryFromIntError),
}

impl std::fmt::Display for CharReaderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CharReaderError::IO(error) => write!(f, "IO Error: {}", error),
            CharReaderError::Overflow(error) => write!(f, "Overflow Error: {}", error),
        }
    }
}

impl Error for CharReaderError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            CharReaderError::IO(error) => Some(error),
            CharReaderError::Overflow(_) => None,
        }
    }
}

impl From<std::io::Error> for CharReaderError {
    fn from(e: std::io::Error) -> Self {
        CharReaderError::IO(e)
    }
}

impl From<TryFromIntError> for CharReaderError {
    fn from(error: TryFromIntError) -> Self {
        CharReaderError::Overflow(error)
    }
}

impl CharReader {
    pub fn open(file_path: &str) -> Result<CharReader, CharReaderError> {
        let mut char_reader = CharReader {
            seek_position: 0,
            block: 0,
            initialized: false,
            buffer: [0; BUFFER_SIZE],
            file: File::open(file_path)?,
        };

        char_reader.read_into_buffer()?;

        Ok(char_reader)
    }

    pub fn has_chars(&mut self) -> Result<bool, CharReaderError> {
        Ok(!self.peek_char()?.is_none())
    }

    pub fn get_position(&self) -> u64 {
        self.seek_position
    }

    pub fn peek_char(&mut self) -> Result<Option<char>, CharReaderError> {
        self.read_into_buffer()?;
        let peeked_char = self.get_current_char();

        Ok(match peeked_char {
            0 => None,
            _ => Some(char::from(peeked_char)),
        })
    }

    fn get_current_block(&self) -> usize {
        self.seek_position as usize / self.buffer.len()
    }

    fn get_current_char(&self) -> u8 {
        self.buffer[self.seek_position as usize % self.buffer.len()]
    }

    pub fn read_char(&mut self) -> Result<Option<char>, CharReaderError> {
        let current_char = self.peek_char()?;
        self.seek_position += 1;

        Ok(current_char)
    }

    pub fn seek_from_start(&mut self, n: u64) -> Result<(), CharReaderError> {
        if n == self.seek_position {
            return Ok(());
        }

        self.seek_position = n;
        let buffer_seek_position = self.get_current_block() * BUFFER_SIZE;
        self.file
            .seek(SeekFrom::Start(buffer_seek_position.try_into()?))?;
        self.read_into_buffer()?;

        Ok(())
    }

    fn read_into_buffer(&mut self) -> Result<(), CharReaderError> {
        if self.initialized && self.get_current_block() == self.block {
            return Ok(());
        }

        self.buffer.fill(0);
        self.file.read(&mut self.buffer)?;
        self.initialized = true;
        self.block = self.get_current_block();

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{CharReader, CharReaderError, BUFFER_SIZE};
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

    fn assert_reader_has_read_file(
        reader: &mut CharReader,
        file_size: usize,
        blocks: u8,
    ) -> Result<(), CharReaderError> {
        while reader.has_chars()? {
            assert_eq!(reader.peek_char()?.unwrap(), get_expected_char(&reader));
            reader.read_char().unwrap();
        }

        assert_eq!(reader.get_position() as usize, file_size);
        assert_eq!(reader.block, blocks as usize);

        Ok(())
    }

    #[test]
    fn read_one_buffer() -> Result<(), CharReaderError> {
        let dir = tempdir()?;
        let file_path = create_test_file(&dir, "single_block.txt", 1)?;
        let file_path = file_path.to_str().unwrap();

        let mut reader = CharReader::open(file_path)?;
        assert_reader_has_read_file(&mut reader, BUFFER_SIZE, 1)?;

        dir.close()?;

        Ok(())
    }

    #[test]
    fn read_multiple_buffers() -> Result<(), CharReaderError> {
        const BLOCKS: u8 = 5;
        const FILE_SIZE: usize = BUFFER_SIZE * BLOCKS as usize;

        let dir = tempdir()?;
        let file_path = create_test_file(&dir, "multiple_blocks.txt", BLOCKS)?;
        let file_path = file_path.to_str().unwrap();

        let mut reader = CharReader::open(file_path)?;
        assert_reader_has_read_file(&mut reader, FILE_SIZE, BLOCKS)?;

        dir.close()?;

        Ok(())
    }

    #[test]
    fn read_and_seek_across_block() -> Result<(), CharReaderError> {
        const BLOCKS: u8 = 5;
        const FILE_SIZE: usize = BUFFER_SIZE * BLOCKS as usize;

        let dir = tempdir()?;
        let file_path = create_test_file(&dir, "multiple_blocks.txt", BLOCKS)?;
        let file_path = file_path.to_str().unwrap();

        let mut reader = CharReader::open(file_path)?;
        let new_seek_position: u64 = BUFFER_SIZE
            .try_into()
            .expect("Buffer size should fit in a u64");
        reader.seek_from_start(new_seek_position)?;
        reader.seek_from_start(new_seek_position - 1)?;
        assert_reader_has_read_file(&mut reader, FILE_SIZE, BLOCKS)?;

        dir.close()?;

        Ok(())
    }
}
