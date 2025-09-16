use crate::parser::PrettyPrint;
use crate::parser::ast::parse_file;
use crate::typeck::{TypeError, TypingEnvironment};

mod parser;
mod typeck;

fn main() {
    let content = std::fs::read("examples/test").unwrap();
    let content = String::from_utf8(content).unwrap();
    let parse_res = parse_file(&content);

    println!("errors : {:#?}", parse_res.errors);
    println!("warnings : {:#?}", parse_res.warnings);
    let ast = parse_res.value;

    ast.pretty_print();

    let mut env = TypingEnvironment::new(&ast);
    match env.resolve_file(&ast) {
        Ok(()) => {}
        Err(e) => {
            env.pretty_println_val(&e);
            println!();
            println!();
        }
    };

    // println!("{env:#?}")
    env.pretty_print()
}
