use kernel::KernelEnvironment;
use parser::{SourceFile, SourceFromFileError};
use std::convert::Infallible;
use std::path::PathBuf;

fn main() {
    let args = std::env::args();
    let Some(file) = args.skip(1).next() else {
        println!("Expected filename argument");
        return;
    };
    let path = match PathBuf::try_from(&file) {
        Ok(path) => path,
        Err(e) => {
            println!("Expected '{file}' to be a path: {e}");
            return;
        }
    };

    let source = match SourceFile::from_file(path) {
        Ok(source) => source,
        Err(e) => {
            println!("Error loading '{file}': {e}");
            return;
        }
    };
    let mut env = KernelEnvironment::new();

    match env.load(&source) {
        Ok(()) => {
            env.pretty_print();
        }
        Err(e) => {
            env.pretty_print();
            println!();
            env.pretty_println_error(&e)
        }
    }
}
