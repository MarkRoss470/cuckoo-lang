
fn main() {
    let content = std::fs::read("examples/test").unwrap();
    let content = String::from_utf8(content).unwrap();

    let env = kernel::TypingEnvironment::from_str(&content);

    dbg!(&env.diagnostics);
    env.value.pretty_print();
}