use libtest_mimic::Trial;
use similar::TextDiff;
use std::{
    env,
    ffi::OsStr,
    fs, io,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

fn main() {
    let mut trials = Vec::new();
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("res");

    collect_trials(&mut String::new(), &mut path, &mut trials);

    libtest_mimic::run(&libtest_mimic::Arguments::from_args(), trials).exit();
}

fn collect_trials(name: &mut String, path: &mut PathBuf, trials: &mut Vec<Trial>) {
    for entry in path.read_dir().unwrap() {
        let entry = entry.unwrap().file_name();
        path.push(&entry);

        let old_name_len = name.len();

        if !name.is_empty() {
            name.push_str("::");
        }

        if path.is_dir() {
            name.push_str(entry.to_str().unwrap());

            collect_trials(name, path, trials);
        } else if path.is_file() && path.extension() == Some(OsStr::new("fir")) {
            name.push_str(Path::new(&entry).file_prefix().unwrap().to_str().unwrap());

            trials.push(Trial::test(name.clone(), {
                let path = path.clone();

                move || run_trial_with_paths(&path, &path.with_extension("out"))
            }));
        }

        name.truncate(old_name_len);
        path.pop();
    }
}

fn run_trial_with_paths(
    input_path: &Path,
    expected_output_path: &Path,
) -> Result<(), libtest_mimic::Failed> {
    let compiler_path = PathBuf::from(expect_env("FIR_FRONTEND_UI_TEST_BIN"));

    let mut child = Command::new(&compiler_path)
        .current_dir(input_path.parent().unwrap())
        .arg(Path::new(input_path.file_name().unwrap()))
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .env("NO_COLOR", "1")
        .spawn()
        .unwrap_or_else(|err| {
            panic!(
                "failed to spawn compiler executable at {}:\n{err:?}",
                compiler_path.display(),
            )
        });

    let actual_output =
        capture_and_pipe(child.stdout.as_mut().unwrap(), io::stdout().lock()).unwrap();

    if !child.wait().unwrap().success() {
        bunt::println!("{$yellow}Compiler ICEd!{/$}");
        return Err(libtest_mimic::Failed::without_message());
    }

    let actual_output = String::from_utf8(actual_output).unwrap();

    let expected_output = match fs::read_to_string(expected_output_path) {
        Ok(output) => Some(output),
        Err(err) if err.kind() == io::ErrorKind::NotFound => None,
        Err(err) => {
            panic!(
                "failed to read expected stdout file at {}:\n{err:?}",
                expected_output_path.display()
            )
        }
    };

    if let Some(expected_output) = expected_output {
        if expected_output == actual_output {
            return Ok(());
        }

        bunt::println!("{$yellow}Differences found in standard output!{/$}");

        for change in TextDiff::from_lines(&expected_output, &actual_output).iter_all_changes() {
            match change.tag() {
                similar::ChangeTag::Equal => {
                    bunt::print!("{[cyan]}", change.value_ref());
                }
                similar::ChangeTag::Delete => {
                    bunt::print!("{[red]}", change.value_ref());
                }
                similar::ChangeTag::Insert => {
                    bunt::print!("{[green]}", change.value_ref());
                }
            }
        }
    } else {
        bunt::println!(
            "{$yellow}Expected output not found at {}!{/$}",
            expected_output_path.display()
        );
    }

    if env::var("FIR_FRONTEND_UI_TEST_BLESS").is_ok() {
        fs::write(expected_output_path, &actual_output).unwrap_or_else(|err| {
            panic!(
                "failed to bless expected stdout file at {}:\n{err:?}",
                expected_output_path.display()
            )
        });

        bunt::println!(
            "{$yellow}Blessed output at {}!{/$}",
            expected_output_path.display()
        );

        return Ok(());
    }

    Err(libtest_mimic::Failed::without_message())
}

fn capture_and_pipe(mut source: impl io::Read, mut target: impl io::Write) -> io::Result<Vec<u8>> {
    let mut output = Vec::new();
    let mut read_position = 0usize;

    loop {
        if output[read_position..].len() < 1024 {
            output.resize(output.len() + 1024, 0);
        }

        let read_count = source.read(&mut output[read_position..])?;

        if read_count == 0 {
            break;
        }

        target.write_all(&output[read_position..][..read_count])?;

        read_position += read_count;
    }

    output.truncate(read_position);

    Ok(output)
}

fn expect_env(var: &str) -> String {
    env::var(var).unwrap_or_else(|_| panic!("missing `{var}`"))
}
