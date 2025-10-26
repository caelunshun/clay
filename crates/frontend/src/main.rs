use fir_frontend::{
    base::{
        Session,
        syntax::{NaiveSegmenter, SourceFileOrigin},
    },
    parse::{ast::parse_file, token::tokenize},
};
use std::{env, fs, path::Path, rc::Rc, time::Instant};

fn main() {
    let args = env::args().collect::<Vec<String>>();
    let args = args.iter().map(|v| v.as_str()).collect::<Vec<&str>>();
    let args = &args[..];

    let [_bin_name, entrypoint] = args else {
        panic!("bad usage");
    };

    let session = Session::new();
    let _guard = session.bind();

    let path = Path::new(entrypoint);

    let span = Session::fetch().source_map.create(
        &mut NaiveSegmenter,
        SourceFileOrigin::Fs(path.to_path_buf()),
        Rc::new(String::from_utf8(fs::read(path).unwrap()).unwrap()),
    );

    let start = Instant::now();
    let tokens = tokenize(span);
    let ast = parse_file(&tokens);

    dbg!(start.elapsed());
    dbg!(&ast);
}
