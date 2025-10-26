use crate::{
    TypeKind,
    ir::{Context, ContextLike, TraitImpl, TraitInstance, Type, TypeParams},
};
use salsa::Database;

pub fn does_impl_trait<'db>(
    db: &'db dyn Database,
    cx: Context<'db>,
    typ: Type<'db>,
    trait_instance: TraitInstance<'db>,
    type_scope_type_params: TypeParams<'db>,
    trait_instance_scope_type_params: TypeParams<'db>,
) -> bool {
    find_trait_impl(
        db,
        cx,
        typ,
        trait_instance,
        type_scope_type_params,
        trait_instance_scope_type_params,
    )
    .is_some()
}

/// Finds a TraitImpl in the given Context satisfying the following constraints:
/// 1. The given `Type` is _covered_ by the trait impl (meaning the impl
/// is either for that specific type or for a generic type whose bounds match
/// the given type)
/// 2. The impl is for the given `TraitInstance`. Note that in the `TraitInstance`,
/// entries in type_args set to `None` correspond to "wildcards." This means that any
/// trait impl that satisfies everything else will match, regardless of the specific
/// type parameter (or associated type equivalent).
///
/// Parameters:
/// `typ`: the type to search for an impl for.
/// `trait_instance`: the trait instance to search for an impl of.
/// `current_scope_type_params`: encodes knowledge about TypeParams
/// in the current scope, e.g. which traits each type parameter is known
/// to implement.
#[salsa::tracked]
pub fn find_trait_impl<'db>(
    db: &'db dyn Database,
    cx: Context<'db>,
    typ: Type<'db>,
    trait_instance: TraitInstance<'db>,
    type_scope_type_params: TypeParams<'db>,
    trait_instance_scope_type_params: TypeParams<'db>,
) -> Option<TraitImpl<'db>> {
    let trait_ = trait_instance.trait_(db).resolve(db, cx);
    let trait_data = trait_.data(db);
    for candidate_impl in cx
        .trait_impls_for_trait(db, trait_instance.trait_(db))
        .iter()
    {}

    todo!()
}

#[salsa::interned]
pub struct CanTypeSatisfyArgs<'db> {
    pub cx: Context<'db>,
    pub t1: Type<'db>,
    #[returns(ref)]
    pub p1: TypeParams<'db>,
    pub t2: Type<'db>,
    #[returns(ref)]
    pub p2: TypeParams<'db>,
}

/// Given a type `t1` in scope `S1`, a type `t2` in scope `S2`,
/// and the type parameter constraints of each scope (`P1` and `P2` resp.):
///
/// Determines whether there exists some TypeArgs `A`
/// that is valid under the constraints of `P2`, and
/// such that substituting `A` into `t2` results in a type
/// equal to `t1`.
#[salsa::tracked]
pub fn can_type_satisfy<'db>(db: &'db dyn Database, args: CanTypeSatisfyArgs<'db>) -> bool {
    let cx = args.cx(db);
    let t1 = args.t1(db);
    let t2 = args.t2(db);
    let p1 = args.p1(db);
    let p2 = args.p2(db);

    match (t1.kind(db), t2.kind(db)) {
        (_, TypeKind::TypeParam(t2_param_id)) => {
            let t2_param = &p2[*t2_param_id];

            // t1_kind must satisfy the trait bounds of t2_param.
            let mut satisfies = true;
            for trait_bound in &t2_param.trait_bounds {
                if !does_impl_trait(db, cx, t1, trait_bound.clone(), p1.clone(), p2.clone()) {
                    satisfies = false;
                    break;
                }
            }
            satisfies
        }
        ((TypeKind::MRef(inner1), TypeKind::MRef(inner2))) => can_type_satisfy(
            db,
            CanTypeSatisfyArgs::new(db, cx, *inner1, p1.clone(), *inner2, p2.clone()),
        ),
        (TypeKind::Prim(prim1), TypeKind::Prim(prim2)) => prim1 == prim2,
        _ => false,
    }
}
