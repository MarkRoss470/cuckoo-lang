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
    env.config_mut().check_terms = true;

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

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;
    use test_each_file::test_each_path;

    /// Tests that all the code snippets in `readme.md` compile
    #[test]
    fn test_readme_examples() {
        let readme_text = std::fs::read("../readme.md").unwrap();
        let readme_text = String::from_utf8(readme_text).unwrap();

        let mut env = KernelEnvironment::new();

        for chunk in readme_text.split("```Cuckoo").skip(1) {
            let code = chunk.split("```").next().unwrap();

            match env.check_str(&code) {
                Ok(()) => {}
                Err(e) => {
                    println!("{code}");
                    println!();
                    env.pretty_println_error(&e);
                    println!();
                    panic!("Code block in readme.md did not type-check");
                }
            }
        }
    }

    fn test_example(path: &Path) {
        let mut env = KernelEnvironment::new();
        let source = SourceFile::from_file(path.to_path_buf()).expect("File should have loaded");

        match env.load(&source) {
            Ok(()) => {}
            Err(e) => {
                env.pretty_println_error(&e);

                panic!("Example file failed to type check")
            }
        }
    }
    
    test_each_path!{ in "examples" => test_example }
}
