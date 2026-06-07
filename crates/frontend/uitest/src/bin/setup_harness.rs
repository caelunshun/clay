use std::{env, fs::OpenOptions, io::Write as _, path::Path, process::Command};

fn main() {
    // Ensure the binary is build.
    println!("Building fir-frontend for ui-tests!");

    Command::new("cargo")
        .arg("build")
        .arg("-p")
        .arg("fir-frontend")
        .spawn()
        .unwrap()
        .wait()
        .unwrap();

    // Tell nextest about it.
    let mut nextest_env = OpenOptions::new()
        .append(true)
        .open(env::var("NEXTEST_ENV").unwrap())
        .unwrap();

    writeln!(
        &mut nextest_env,
        "FIR_FRONTEND_UI_TEST_BIN={}",
        Path::new("target/debug/fir-frontend")
            .canonicalize()
            .unwrap()
            .display(),
    )
    .unwrap();
}
