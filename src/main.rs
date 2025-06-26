use crate::parser::ast::parse_file;

mod parser;
mod typeck;

fn main() {
    let content = std::fs::read("examples/test").unwrap();
    let content = String::from_utf8(content).unwrap();
    let parse_res = parse_file(&content);

    println!("errors : {:#?}", parse_res.errors);
    println!("warnings : {:#?}", parse_res.warnings);
    parse_res.value.pretty_print();
}

