#[link(name = "compiled_code", kind = "static")]
extern "sysv64" {
    #[link_name = "\u{1}entry"]
    fn entry(param: i64) -> i64;
}

static mut PARSE_STATE: usize = 0;
static INPUT_STR: [u8; 22] = *b"[[[]]][][[]][[[[[]]]]]";
// static INPUT_STR: [u8; 0] = *b"";

#[export_name = "\u{1}peek"]
extern "sysv64" fn peek() -> i64 {
    let x = match unsafe { INPUT_STR.get(PARSE_STATE) } {
        None => 2,
        Some(b'[') => 0,
        Some(b']') => 1,
        Some(c) => panic!("peek error, unexpected char {}", c),
    };
    println!("peeked at {}", x);
    x
}

#[export_name = "\u{1}pop"]
extern "sysv64" fn pop() -> i64 {
    let v = peek();
    println!("popped");
    unsafe { PARSE_STATE += 1 };
    v
}

#[export_name = "\u{1}print"]
extern "sysv64" fn print(x: i64) -> i64 {
    println!("{}", x);
    x
}

#[export_name = "\u{1}read"]
extern "sysv64" fn read() -> i64 {
    let mut buf = String::new();
    std::io::stdin().read_line(&mut buf).unwrap();
    buf.trim().parse().unwrap()
}

#[export_name = "\u{1}big_fun_nine"]
extern "sysv64" fn big_fun_nine(
    x1: i64, x2: i64, x3: i64, x4: i64, x5: i64, x6: i64, x7: i64, x8: i64, x9: i64,
) -> i64 {
    println!(
        "x1: {}\nx2: {}\nx3: {}\nx4: {}\nx5: {}\nx6: {}\nx7: {}\nx8: {}\nx9: {}",
        x1, x2, x3, x4, x5, x6, x7, x8, x9
    );
    x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9
}

#[export_name = "\u{1}big_fun_ten"]
extern "sysv64" fn big_fun_ten(
    x1: i64, x2: i64, x3: i64, x4: i64, x5: i64, x6: i64, x7: i64, x8: i64, x9: i64, x10: i64,
) -> i64 {
    println!(
        "x1: {}\nx2: {}\nx3: {}\nx4: {}\nx5: {}\nx6: {}\nx7: {}\nx8: {}\nx9: {}\nx10: {}",
        x1, x2, x3, x4, x5, x6, x7, x8, x9, x10
    );
    x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10
}

fn main() {
    let arg = std::env::args()
        .nth(1)
        .expect("no argument provided")
        .parse::<i64>()
        .expect("invalid argument for i64");
    let output = unsafe { entry(arg) };
    println!("{}", output);
}
