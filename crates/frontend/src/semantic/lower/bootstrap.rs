use crate::{
    base::{Obj, ObjAllocExt, Session, Span},
    parse::{
        ast::{AstVisibility, AstVisibilityKind},
        token::Ident,
    },
    semantic::{
        lower::modules::{BuilderItemId, BuilderModuleTree, ItemCategory},
        syntax::{
            Crate, FloatKind, GenericBinder, IntKind, Item, ItemKind, ModuleItem, SigTyKind,
            SimpleTyKind, TypeAliasItem,
        },
    },
    symbol,
    utils::mem::LateInit,
};

pub fn synthesize_bootstrap_crate(s: &Session) -> Obj<Crate> {
    // Prepare crate data
    let name = symbol!("bootstrap");
    let types = [
        (
            symbol!("u8"),
            SigTyKind::Simple(SimpleTyKind::Uint(IntKind::S8)).wrap(s, Span::DUMMY),
        ),
        (
            symbol!("u16"),
            SigTyKind::Simple(SimpleTyKind::Uint(IntKind::S16)).wrap(s, Span::DUMMY),
        ),
        (
            symbol!("u32"),
            SigTyKind::Simple(SimpleTyKind::Uint(IntKind::S32)).wrap(s, Span::DUMMY),
        ),
        (
            symbol!("u64"),
            SigTyKind::Simple(SimpleTyKind::Uint(IntKind::S64)).wrap(s, Span::DUMMY),
        ),
        (
            symbol!("i8"),
            SigTyKind::Simple(SimpleTyKind::Int(IntKind::S8)).wrap(s, Span::DUMMY),
        ),
        (
            symbol!("i16"),
            SigTyKind::Simple(SimpleTyKind::Int(IntKind::S16)).wrap(s, Span::DUMMY),
        ),
        (
            symbol!("i32"),
            SigTyKind::Simple(SimpleTyKind::Int(IntKind::S32)).wrap(s, Span::DUMMY),
        ),
        (
            symbol!("i64"),
            SigTyKind::Simple(SimpleTyKind::Int(IntKind::S64)).wrap(s, Span::DUMMY),
        ),
        (
            symbol!("f32"),
            SigTyKind::Simple(SimpleTyKind::Float(FloatKind::S32)).wrap(s, Span::DUMMY),
        ),
        (
            symbol!("f64"),
            SigTyKind::Simple(SimpleTyKind::Float(FloatKind::S64)).wrap(s, Span::DUMMY),
        ),
        (
            symbol!("bool"),
            SigTyKind::Simple(SimpleTyKind::Bool).wrap(s, Span::DUMMY),
        ),
        (
            symbol!("char"),
            SigTyKind::Simple(SimpleTyKind::Char).wrap(s, Span::DUMMY),
        ),
        (
            symbol!("str"),
            SigTyKind::Simple(SimpleTyKind::Str).wrap(s, Span::DUMMY),
        ),
        (
            symbol!("Never"),
            SigTyKind::Simple(SimpleTyKind::Never).wrap(s, Span::DUMMY),
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

    let krate = Crate {
        name,
        root: LateInit::uninit(),
        prelude: LateInit::uninit(),
        items: LateInit::uninit(),
    }
    .alloc_obj(s);

    let items = builder.freeze_and_check(s, krate);

    lower_synthetic_module(s, items[BuilderItemId::ROOT]);
    lower_synthetic_module(s, items[BuilderItemId::PRELUDE]);

    for (&item, &(_name, resolves_to)) in type_alias_items.iter().zip(&types) {
        let item = items[item];

        LateInit::init(&item.r(s).attrs, Vec::new());

        LateInit::init(
            &item.r(s).kind,
            ItemKind::TypeAlias(
                TypeAliasItem {
                    item,
                    generics: GenericBinder::default().seal(s),
                    body: LateInit::new(resolves_to),
                }
                .alloc_obj(s),
            ),
        );
    }

    krate
}

pub fn lower_synthetic_module(s: &Session, item: Obj<Item>) {
    LateInit::init(
        &item.r(s).kind,
        ItemKind::Module(ModuleItem { item }.alloc_obj(s)),
    );

    LateInit::init(&item.r(s).attrs, Vec::new());
}
