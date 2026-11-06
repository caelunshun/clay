use clay_frontend::{
    base::{NaiveSegmenter, Session, SourceFileOrigin},
    parse::{ast::parse_file, token::tokenize},
    semantic::{
        analysis::TyCtxt,
        infer::ImplCache,
        lower::{bootstrap::synthesize_bootstrap_crate, entry::lower_full_ast},
        syntax::LangItems,
    },
    symbol,
};
use std::{env, fs, path::Path, rc::Rc};

fn main() {
    color_eyre::install().unwrap();

    let args = env::args().collect::<Vec<String>>();
    let args = args.iter().map(|v| v.as_str()).collect::<Vec<&str>>();
    let args = &args[..];

    let [_bin_name, std_entrypoint, app_entrypoint] = args else {
        panic!("bad usage");
    };

    let session = Session::new();
    let _guard = session.clone().bind();
    let s = &session;

    let std_entrypoint = Path::new(std_entrypoint);
    let app_entrypoint = Path::new(app_entrypoint);

    let std_span = Session::fetch().source_map.create(
        &mut NaiveSegmenter,
        SourceFileOrigin::Fs(std_entrypoint.to_path_buf()),
        Rc::new(String::from_utf8(fs::read(std_entrypoint).unwrap()).unwrap()),
    );

    let app_span = Session::fetch().source_map.create(
        &mut NaiveSegmenter,
        SourceFileOrigin::Fs(app_entrypoint.to_path_buf()),
        Rc::new(String::from_utf8(fs::read(app_entrypoint).unwrap()).unwrap()),
    );

    // Compile standard library
    let std_tokens = tokenize(std_span);
    let std_ast = parse_file(&std_tokens);
    let std_krate = lower_full_ast(s, symbol!("std"), &std_ast, |ctxt| {
        ctxt.push_prelude_glob(*synthesize_bootstrap_crate(s).r(s).root);
    });

    let mut impl_cache = ImplCache::default();
    impl_cache.populate(s, std_krate);

    let mut lang_items = LangItems::default();
    lang_items.populate(s, std_krate);

    TyCtxt {
        session: s,
        impl_cache: &impl_cache,
        lang_items: &lang_items,
        krate: std_krate,
    }
    .check_crate();

    _ = session.diag.finish();

    // Compile app
    let app_tokens = tokenize(app_span);
    let app_ast = parse_file(&app_tokens);
    let app_krate = lower_full_ast(s, symbol!("app"), &app_ast, |ctxt| {
        ctxt.push_prelude_use(symbol!("std"), *std_krate.r(s).root);
        ctxt.push_prelude_glob(lang_items.std_prelude().unwrap().r(s).item);
    });

    impl_cache.populate(s, app_krate);
    lang_items.populate(s, app_krate);

    TyCtxt {
        session: s,
        impl_cache: &impl_cache,
        lang_items: &lang_items,
        krate: app_krate,
    }
    .check_crate();

    _ = session.diag.finish();
}
