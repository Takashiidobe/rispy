use man::prelude::*;
use std::fs::File;
use std::io::{Error, Write};

fn main() -> Result<(), Error> {
    let path = "rvim.1";
    let mut output = File::create(path)?;

    let msg = Manual::new("rvim")
        .about("A text editor in rust.")
        .arg(Arg::new("path"))
        .example(
            Example::new()
                .text("Running the program")
                .command("rvim [FILE]...")
                .output("TODO"),
        )
        .custom(Section::new("Features").paragraph(
            r#"Syntax Highlighting:
    - Bash (.sh)
    - C (.c, .h)
    - C++ (.cc, .cpp, .C, .h, .hh, .hpp)
    - C# (.cs)
    - Java (.java)
    - Javascript (.js)
    - JSON (.json)
    - Go (.go)
    - Python (.py)
    - R (.r)
    - Ruby (.rb)
    - Rust (.rs)"#,
        ))
        .author(Author::new("Takashi I").email("mail@takashiidobe.com"))
        .render();

    write!(output, "{}", msg)
}
