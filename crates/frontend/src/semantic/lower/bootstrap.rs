use crate::{
    base::{
        Session,
        analysis::Spanned,
        arena::{HasInterner, LateInit, Obj},
        syntax::Span,
    },
    parse::{
        ast::{AstVisibility, AstVisibilityKind},
        token::Ident,
    },
    semantic::{
        analysis::TyCtxt,
        lower::modules::{BuilderItemId, BuilderModuleTree, ItemCategory},
        syntax::{
            Crate, FloatKind, GenericBinder, IntKind, Item, ItemKind, LangItems, ModuleItem,
            SimpleTyKind, TyKind, TypeAliasItem,
        },
    },
    symbol,
};

pub fn synthesize_bootstrap_prelude(tcx: &TyCtxt) -> Obj<Crate> {
    let s = &tcx.session;

    // Prepare crate data
    let name = symbol!("primitives");
    let types = [
        (
            symbol!("u8"),
            tcx.intern(TyKind::Simple(SimpleTyKind::Uint(IntKind::S8))),
        ),
        (
            symbol!("u16"),
            tcx.intern(TyKind::Simple(SimpleTyKind::Uint(IntKind::S16))),
        ),
        (
            symbol!("u32"),
            tcx.intern(TyKind::Simple(SimpleTyKind::Uint(IntKind::S32))),
        ),
        (
            symbol!("u64"),
            tcx.intern(TyKind::Simple(SimpleTyKind::Uint(IntKind::S64))),
        ),
        (
            symbol!("i8"),
            tcx.intern(TyKind::Simple(SimpleTyKind::Int(IntKind::S8))),
        ),
        (
            symbol!("i16"),
            tcx.intern(TyKind::Simple(SimpleTyKind::Int(IntKind::S16))),
        ),
        (
            symbol!("i32"),
            tcx.intern(TyKind::Simple(SimpleTyKind::Int(IntKind::S32))),
        ),
        (
            symbol!("i64"),
            tcx.intern(TyKind::Simple(SimpleTyKind::Int(IntKind::S64))),
        ),
        (
            symbol!("f32"),
            tcx.intern(TyKind::Simple(SimpleTyKind::Float(FloatKind::S32))),
        ),
        (
            symbol!("f64"),
            tcx.intern(TyKind::Simple(SimpleTyKind::Float(FloatKind::S64))),
        ),
        (
            symbol!("bool"),
            tcx.intern(TyKind::Simple(SimpleTyKind::Bool)),
        ),
        (
            symbol!("char"),
            tcx.intern(TyKind::Simple(SimpleTyKind::Char)),
        ),
        (
            symbol!("str"),
            tcx.intern(TyKind::Simple(SimpleTyKind::Str)),
        ),
        (
            symbol!("Never"),
            tcx.intern(TyKind::Simple(SimpleTyKind::Never)),
        ),
    ];

    // Build crate
    let mut builder = BuilderModuleTree::new(s.clone());

    let type_alias_items = types
        .iter()
        .map(|&(name, _ty)| {
            builder.push_named_item(
                BuilderItemId::ROOT,
                AstVisibility {
                    span: Span::DUMMY,
                    kind: AstVisibilityKind::Pub,
                },
                ItemCategory::TypeAlias,
                Ident::new(Span::DUMMY, name),
            )
        })
        .collect::<Vec<_>>();

    let krate = Obj::new(
        Crate {
            name,
            is_local: false,
            root: LateInit::uninit(),
            prelude: LateInit::uninit(),
            items: LateInit::uninit(),
            lang_items: LangItems::default(),
        },
        s,
    );

    let items = builder.freeze_and_check(krate, s);

    lower_synthetic_module(items[BuilderItemId::ROOT], s);
    lower_synthetic_module(items[BuilderItemId::PRELUDE], s);

    for (&item, &(_name, resolves_to)) in type_alias_items.iter().zip(&types) {
        let item = items[item];

        LateInit::init(&item.r(s).attrs, Vec::new());

        LateInit::init(
            &item.r(s).kind,
            ItemKind::TypeAlias(Obj::new(
                TypeAliasItem {
                    item,
                    generics: tcx.seal_generic_binder(GenericBinder::default()),
                    body: LateInit::new(Spanned::new_unspanned(resolves_to)),
                },
                s,
            )),
        );
    }

    krate
}

pub fn lower_synthetic_module(item: Obj<Item>, s: &Session) {
    LateInit::init(
        &item.r(s).kind,
        ItemKind::Module(Obj::new(ModuleItem { item }, s)),
    );

    LateInit::init(&item.r(s).attrs, Vec::new());
}
