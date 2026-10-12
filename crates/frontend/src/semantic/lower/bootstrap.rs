use crate::{
    base::{
        Session,
        arena::{LateInit, Obj},
        syntax::Span,
    },
    parse::{
        ast::{AstVisibility, AstVisibilityKind},
        token::Ident,
    },
    semantic::{
        lower::modules::{BuilderItemId, BuilderModuleTree, ItemCategory},
        syntax::{
            Crate, FloatKind, GenericBinder, IntKind, Item, ItemKind, LangItems, ModuleItem,
            SigTyKind, SimpleTyKind, TyCtxt, TypeAliasItem,
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
            SigTyKind::Simple(SimpleTyKind::Uint(IntKind::S8)).wrap(Span::DUMMY, s),
        ),
        (
            symbol!("u16"),
            SigTyKind::Simple(SimpleTyKind::Uint(IntKind::S16)).wrap(Span::DUMMY, s),
        ),
        (
            symbol!("u32"),
            SigTyKind::Simple(SimpleTyKind::Uint(IntKind::S32)).wrap(Span::DUMMY, s),
        ),
        (
            symbol!("u64"),
            SigTyKind::Simple(SimpleTyKind::Uint(IntKind::S64)).wrap(Span::DUMMY, s),
        ),
        (
            symbol!("i8"),
            SigTyKind::Simple(SimpleTyKind::Int(IntKind::S8)).wrap(Span::DUMMY, s),
        ),
        (
            symbol!("i16"),
            SigTyKind::Simple(SimpleTyKind::Int(IntKind::S16)).wrap(Span::DUMMY, s),
        ),
        (
            symbol!("i32"),
            SigTyKind::Simple(SimpleTyKind::Int(IntKind::S32)).wrap(Span::DUMMY, s),
        ),
        (
            symbol!("i64"),
            SigTyKind::Simple(SimpleTyKind::Int(IntKind::S64)).wrap(Span::DUMMY, s),
        ),
        (
            symbol!("f32"),
            SigTyKind::Simple(SimpleTyKind::Float(FloatKind::S32)).wrap(Span::DUMMY, s),
        ),
        (
            symbol!("f64"),
            SigTyKind::Simple(SimpleTyKind::Float(FloatKind::S64)).wrap(Span::DUMMY, s),
        ),
        (
            symbol!("bool"),
            SigTyKind::Simple(SimpleTyKind::Bool).wrap(Span::DUMMY, s),
        ),
        (
            symbol!("char"),
            SigTyKind::Simple(SimpleTyKind::Char).wrap(Span::DUMMY, s),
        ),
        (
            symbol!("str"),
            SigTyKind::Simple(SimpleTyKind::Str).wrap(Span::DUMMY, s),
        ),
        (
            symbol!("Never"),
            SigTyKind::Simple(SimpleTyKind::Never).wrap(Span::DUMMY, s),
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
                    generics: GenericBinder::default().seal(s),
                    body: LateInit::new(resolves_to),
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
