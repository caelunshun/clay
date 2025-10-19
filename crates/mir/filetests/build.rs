//! Generates a `#[test]` case for each filetest
//! in subdirectories of `tests`.
//!
//! Each filetest can contain an arbitrary string (but
//! which is usually parsed as an S-expression MIR module).
//! The top of the filetest contains test directives.
//! A `// @harness <harness_name>` directive is mandatory
//! and indicates the function in `tests/harnesses.rs` that
//! will be used to drive the test case.
//! If a file name ends with ".expected", it is passed
//! as the "expected" output to the harness function for
//! the test case having the file name minus ".expected."

use quote::{format_ident, quote};
use std::{env, error::Error, fs};

fn main() -> Result<(), Box<dyn Error + Send + Sync>> {
    println!("cargo:rerun-if-changed=tests");

    let mut code = Vec::new();

    for entry in fs::read_dir("tests")? {
        let entry = entry?;
        if !entry.file_type()?.is_dir() {
            continue;
        }

        let dir_name = entry.file_name().to_str().unwrap().to_owned();

        let mut tests = Vec::new();

        for entry in fs::read_dir(entry.path())? {
            let entry = entry?;

            let file_name = entry.file_name().to_str().unwrap().to_owned();
            if file_name.ends_with(".expected") {
                continue;
            }

            let test_case_name = &file_name[..file_name.find('.').unwrap_or(file_name.len())];
            let test_case_ident = format_ident!("{test_case_name}");

            let file_contents = fs::read_to_string(entry.path())?;
            let harness_start = file_contents.find("// @harness").unwrap();
            let harness_end = file_contents[harness_start..].find("\n").unwrap();
            let harness = file_contents[harness_start + "// @harness".len()..]
                [..harness_end - "// @harness".len()]
                .trim();
            let harness = format_ident!("{harness}");

            let expected_path = entry.path().with_file_name(format!("{file_name}.expected"));
            let expected_code = if expected_path.exists() {
                let s = fs::read_to_string(expected_path)?;
                quote! {
                    , #s
                }
            } else {
                quote! {}
            };

            tests.push(quote! {
                #[test]
                fn #test_case_ident() {
                    super::harnesses::#harness(#file_contents #expected_code);
                }
            });
        }

        let module_name = format_ident!("{dir_name}");
        code.push(quote! {
            mod #module_name {
                #(#tests)*
            }
        });
    }

    let code = quote! { #(#code)* };

    let out_path = format!("{}/generated.rs", env::var("OUT_DIR")?);
    fs::write(out_path, code.to_string().as_bytes())?;

    Ok(())
}
