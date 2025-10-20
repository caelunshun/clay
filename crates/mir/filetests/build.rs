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

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::{collections::HashMap, env, error::Error, fs};

fn main() -> Result<(), Box<dyn Error + Send + Sync>> {
    println!("cargo:rerun-if-changed=tests");

    let mut modules = HashMap::<String, HashMap<String, Vec<TokenStream>>>::new();

    for entry in fs::read_dir("tests")? {
        let entry = entry?;
        if !entry.file_type()?.is_dir() {
            continue;
        }

        let dir_name = entry.file_name().to_str().unwrap().to_owned();

        for entry in fs::read_dir(entry.path())? {
            let entry = entry?;

            let file_name = entry.file_name().to_str().unwrap().to_owned();
            if file_name.ends_with(".expected") {
                continue;
            }

            let test_case_name = &file_name[..file_name.find('.').unwrap_or(file_name.len())];
            let test_case_ident = format_ident!("{test_case_name}");

            let file_contents = fs::read_to_string(entry.path())?;
            let harnesses = list_harnesses(&file_contents);
            if harnesses.is_empty() {
                panic!("no @harness statements found in filetest");
            }

            let expected_path = entry.path().with_file_name(format!("{file_name}.expected"));
            let expected_code = if expected_path.exists() {
                let s = fs::read_to_string(expected_path)?;
                quote! {
                    , #s
                }
            } else {
                quote! {}
            };

            for harness in harnesses {
                let module = modules
                    .entry(harness.clone())
                    .or_default()
                    .entry(dir_name.clone())
                    .or_default();
                let harness = format_ident!("{harness}");
                module.push(quote! {
                    #[test]
                    fn #test_case_ident() {
                        super::super::harnesses::#harness(#file_contents #expected_code);
                    }
                });
            }
        }
    }

    let mut code = Vec::new();
    for (supermodule, submodules) in modules {
        let supermodule = format_ident!("{supermodule}");
        let mut module_code = Vec::new();
        for (submodule, tokens) in submodules {
            let submodule = format_ident!("{submodule}");
            module_code.push(quote! {
                mod #submodule {
                    #(#tokens)*
                }
            });
        }
        code.push(quote! {
            mod #supermodule {
                #(#module_code)*
            }
        });
    }

    let code = quote! { #(#code)* };

    let out_path = format!("{}/generated.rs", env::var("OUT_DIR")?);
    fs::write(out_path, code.to_string().as_bytes())?;

    Ok(())
}

fn list_harnesses(mut file_contents: &str) -> Vec<String> {
    let pattern = "// @harness";
    let mut harnesses = Vec::new();
    while let Some(pos) = file_contents.find(pattern) {
        let new_line = file_contents[pos..]
            .find('\n')
            .unwrap_or(file_contents.len());
        let harness = &file_contents[pos + pattern.len()..new_line].trim();
        harnesses.push(harness.to_string());
        file_contents = &file_contents[new_line..];
    }
    harnesses
}
