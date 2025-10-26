use crate::{
    TypeKind,
    ir::{Context, ContextLike, TraitImpl, TraitInstance, Type},
};
use salsa::Database;

pub fn does_impl_trait<'db>(
    db: &'db dyn Database,
    cx: Context<'db>,
    typ: Type<'db>,
    trait_instance: TraitInstance<'db>,
) -> bool {
    find_trait_impl(db, cx, typ, trait_instance).is_some()
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
) -> Option<TraitImpl<'db>> {
    for candidate_impl in cx
        .trait_impls_for_trait(db, trait_instance.trait_(db))
        .iter()
    {
        // Check that trait instance matches
        let mut trait_instance_match = true;
        for (type_param_id, arg) in trait_instance.type_args(db).iter() {
            let impl_arg = candidate_impl.data(db).trait_.type_args(db)[type_param_id];
            if !can_type_satisfy(
                db,
                CanTypeSatisfyArgs::new(db, cx, arg, impl_arg.substitute_self_type(db, typ)),
            ) {
                trait_instance_match = false;
                break;
            }
        }
        if !trait_instance_match {
            continue;
        }

        // Check that type implemented for matches
        if !can_type_satisfy(
            db,
            CanTypeSatisfyArgs::new(
                db,
                cx,
                typ,
                candidate_impl
                    .data(db)
                    .impl_for_type
                    .substitute_self_type(db, typ),
            ),
        ) {
            continue;
        }

        return Some(*candidate_impl);
    }

    None
}

#[salsa::interned]
pub struct CanTypeSatisfyArgs<'db> {
    pub cx: Context<'db>,
    pub t1: Type<'db>,
    pub t2: Type<'db>,
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

    match (t1.kind(db), t2.kind(db)) {
        (_, TypeKind::TypeParam(t2_param_id)) => {
            let t2_param = t2_param_id.resolve(db, &cx);

            // t1_kind must satisfy the trait bounds of t2_param.
            let mut satisfies = true;
            for trait_bound in &t2_param.trait_bounds {
                if !does_impl_trait(db, cx, t1, *trait_bound) {
                    satisfies = false;
                    break;
                }
            }
            satisfies
        }
        (TypeKind::MRef(inner1), TypeKind::MRef(inner2))
        | (TypeKind::List(inner1), TypeKind::List(inner2)) => {
            can_type_satisfy(db, CanTypeSatisfyArgs::new(db, cx, *inner1, *inner2))
        }
        (TypeKind::Algebraic(a1), TypeKind::Algebraic(a2)) => {
            // Must be same ADT and parameters must be satisfiable
            if a1.adt == a2.adt {
                let mut satisfies = true;
                for (type_param_id, a1_arg) in a1.type_args.iter() {
                    if let Some(a2_arg) = a2.type_args.get(type_param_id) {
                        satisfies |=
                            can_type_satisfy(db, CanTypeSatisfyArgs::new(db, cx, *a1_arg, a2_arg));
                    }
                }
                satisfies
            } else {
                false
            }
        }
        (TypeKind::Prim(prim1), TypeKind::Prim(prim2)) => prim1 == prim2,
        _ => false,
    }
}
