use kernel::KernelEnvironment;

fn main() {
    let content = std::fs::read("examples/test").unwrap();
    let content = String::from_utf8(content).unwrap();

    let mut env = KernelEnvironment::new();
    match env.check_str(&content) {
        Ok(()) => {}
        Err(e) => {
            env.pretty_println_error(&e)
        }
    }

    env.pretty_print();
}