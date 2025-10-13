use crate::parser::ast::parse_file;
use crate::typeck::TypingEnvironment;

mod parser;
mod typeck;

fn main() {
    let content = std::fs::read("examples/test").unwrap();
    let content = String::from_utf8(content).unwrap();
    let parse_res = parse_file(&content);

    println!("errors : {:#?}", parse_res.errors);
    println!("warnings : {:#?}", parse_res.warnings);
    let (interner, ast) = parse_res.value;

    let mut env = TypingEnvironment::new(interner);
    let res = env.resolve_file(&ast);
    env.pretty_print();
    println!();
    match res {
        Ok(()) => {
            println!("Success!")
        }
        Err(e) => {
            env.pretty_println_val(&e);
        }
    };
}
