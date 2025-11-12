// Currently, we're generating the obligation...
//
// ```
// {Self: Foo<Bar = {Bar: Foo<Bar = {Self: ...}>}>}: Foo<Bar = {Self: ...}>
// ```
//
// This is rejected because `{Bar: Foo<Bar = {Self: ...}>}` does not equal `{Self: ...}` and yet
// this should compile.
//
// Here's how `rustc` solves this exact input...
//
// ```
// rustc_hir_analysis::check::wfcheck::check_trait 
//     rustc_trait_selection::traits::wf::clause_obligations
//         param_env=ParamEnv {
//             caller_bounds: [
//                 Binder {
//                     value: TraitPredicate(<Self as Foo>, polarity:Positive),
//                     bound_vars: []
//                 },
//                 Binder {
//                     value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive),
//                     bound_vars: []
//                 }
//             ]
//         },
//         body_id=DefId(0:3 ~ test7[2f6f]::Foo),
//         clause=Binder {
//             value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive),
//             bound_vars: []
//         },
//         span=./crates/frontend/samples/test7.fir:10:1: 12:2 (#0)
//     rustc_trait_selection::traits::wf return=[
//         Obligation(
//             predicate=Binder {
//                 value: TraitPredicate(
//                     <Self as std::marker::MetaSized>,
//                     polarity:Positive
//                 ),
//                 bound_vars: []
//             },
//             depth=0
//         ),
//         Obligation(
//             predicate=Binder {
//                 value: WellFormed(Term::Ty(Self/#0)),
//                 bound_vars: []
//             },
//             depth=0
//         )
//     ]
//
//     rustc_trait_selection::traits::wf::clause_obligations
//         param_env=ParamEnv {
//             caller_bounds: [
//                 Binder {
//                     value: TraitPredicate(<Self as Foo>, polarity:Positive),
//                     bound_vars: []
//                 },
//                 Binder {
//                     value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive),
//                     bound_vars: []
//                 }
//             ]
//         },
//         body_id=DefId(0:3 ~ test7[2f6f]::Foo),
//         clause=Binder {
//             value: TraitPredicate(<Self as Foo>, polarity:Positive),
//             bound_vars: []
//         },
//         span=no-location (#0)
//     rustc_trait_selection::traits::wf return=[
//         Obligation(
//             predicate=Binder {
//                 value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive),
//                 bound_vars: []
//             },
//             depth=0
//         ),
//         Obligation(
//             predicate=Binder {
//                 value: TraitPredicate(<Self as Foo>, polarity:Positive),
//                 bound_vars: []
//             },
//             depth=0
//         ),
//         Obligation(
//             predicate=Binder {
//                 value: WellFormed(Term::Ty(Self/#0)),
//                 bound_vars: []
//             },
//             depth=0
//         )
//     ]
//
// ---
//
//     rustc_trait_selection::traits::wf::clause_obligations
//         param_env=ParamEnv {
//             caller_bounds: [
//                 Binder {
//                     value: TraitPredicate(<Self as Foo>, polarity:Positive),
//                     bound_vars: []
//                 },
//                 Binder {
//                     value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive),
//                     bound_vars: []
//                 }
//             ]
//         },
//         body_id=DefId(0:4 ~ test7[2f6f]::Foo::Bar),
//         clause=Binder {
//             value: TraitPredicate(<<Self as Foo>::Bar as std::marker::Sized>, polarity:Positive),
//             bound_vars: []
//         },
//         span=./crates/frontend/samples/test7.fir:11:5: 11:31 (#0)
//     rustc_trait_selection::traits::wf return=[
//         Obligation(
//             predicate=Binder {
//                 value: WellFormed(
//                     Term::Ty(
//                         Alias(Projection, AliasTy { args: [Self/#0], def_id: DefId(0:4 ~ test7[2f6f]::Foo::Bar), .. })
//                     )
//                 ),
//                 bound_vars: []
//             },
//             depth=0
//         )
//     ]
//
//     rustc_trait_selection::traits::wf::clause_obligations
//         param_env=ParamEnv {
//             caller_bounds: [
//                 Binder {
//                     value: TraitPredicate(<Self as Foo>, polarity:Positive),
//                     bound_vars: []
//                 },
//                 Binder {
//                     value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive),
//                     bound_vars: []
//                 }
//             ]
//         },
//         body_id=DefId(0:4 ~ test7[2f6f]::Foo::Bar),
//         clause=Binder {
//             value: TraitPredicate(<<Self as Foo>::Bar as Foo>, polarity:Positive),
//             bound_vars: []
//         },
//         span=./crates/frontend/samples/test7.fir:11:15: 11:30 (#0)
//     rustc_trait_selection::traits::wf return=[
//         Obligation(
//             predicate=Binder {
//                 value: TraitPredicate(<<Self as Foo>::Bar as std::marker::MetaSized>, polarity:Positive),
//                 bound_vars: []
//             },
//             depth=0
//         ),
//         Obligation(
//             predicate=Binder {
//                 value: TraitPredicate(<<Self as Foo>::Bar as Foo>, polarity:Positive),
//                 bound_vars: []
//             },
//             depth=0
//         ),
//         Obligation(
//             predicate=Binder {
//                 value: WellFormed(Term::Ty(
//                     Alias(Projection, AliasTy { args: [Self/#0], def_id: DefId(0:4 ~ test7[2f6f]::Foo::Bar), .. })
//                 )),
//                 bound_vars: []
//             },
//             depth=0
//         )
//     ]
//
//     rustc_trait_selection::traits::wf::clause_obligations
//         param_env=ParamEnv {
//             caller_bounds: [
//                 Binder {
//                     value: TraitPredicate(<Self as Foo>, polarity:Positive),
//                     bound_vars: []
//                 },
//                 Binder {
//                     value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive),
//                     bound_vars: []
//                 }
//             ]
//         },
//         body_id=DefId(0:4 ~ test7[2f6f]::Foo::Bar),
//         clause=Binder {
//             value: ProjectionPredicate(
//                 AliasTerm {
//                     args: [
//                         Alias(Projection, AliasTy { args: [Self/#0], def_id: DefId(0:4 ~ test7[2f6f]::Foo::Bar), .. })
//                     ],
//                     def_id: DefId(0:4 ~ test7[2f6f]::Foo::Bar), ..
//                 },
//                 Term::Ty(Self/#0)
//             ),
//             bound_vars: []
//         },
//         span=./crates/frontend/samples/test7.fir:11:19: 11:29 (#0)
//     rustc_trait_selection::traits::wf return=[
//         Obligation(
//             predicate=Binder {
//                 value: TraitPredicate(<<Self as Foo>::Bar as std::marker::MetaSized>, polarity:Positive),
//                 bound_vars: []
//             },
//             depth=0
//         ),
//         Obligation(
//             predicate=Binder {
//                 value: TraitPredicate(<<Self as Foo>::Bar as Foo>, polarity:Positive),
//                 bound_vars: [] 
//             },
//             depth=0
//         ),
//         Obligation(
//             predicate=Binder {
//                 value: WellFormed(
//                     Term::Ty(Alias(
//                         Projection,
//                         AliasTy { args: [Self/#0], def_id: DefId(0:4 ~ test7[2f6f]::Foo::Bar), .. }
//                     ))
//                 ),
//                 bound_vars: []
//             },
//             depth=0
//         )
//     ]
// ```
//
// On one hand, the presence of...
//
// ```
// value: ProjectionPredicate(
//     AliasTerm {
//         args: [
//             Alias(Projection, AliasTy { args: [Self/#0], def_id: DefId(0:4 ~ test7[2f6f]::Foo::Bar), .. })
//         ],
//         def_id: DefId(0:4 ~ test7[2f6f]::Foo::Bar), ..
//     },
//     Term::Ty(Self/#0)
// ),
// ```
//
// ...seems to suggest that `Bar = Self` is being properly proven. On the other hand, `rustc`
// accepts...
//
// ```rust
// pub trait Foo {
//     type Bar: Foo<Bar = (Self,)>;
// }
// ```
//
// ...even if there isn't an `impl` in scope to prove that `for<T: Foo> (T,): Foo`.
//
// Indeed, it will even accept...
//
// ```rust
// pub trait Foo {
//     type Bar: Foo<Bar = ()>;
// }
// ```
//
// ...but it will reject...
//
// ```rust
// pub trait Foo<T: Foo<()>> {}
// ```
//
// Hmm... what about...
//
// ```rust
// pub trait Foo<T: ?Sized + Foo<Self>> {}
// ```
//
// Looks like it accepts that. How does it reason about *that*? Our solver chokes on that too.
//
// ```
// rustc_hir_analysis::check::wfcheck::check_trait 
//     rustc_trait_selection::traits::normalize::normalize_with_depth_to
//         depth=0,
//         value=Binder {
//             value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive),
//             bound_vars: []
//         }
//
//     rustc_trait_selection::traits::wf::clause_obligations
//         param_env=ParamEnv {
//             caller_bounds: [
//                 Binder { value: TraitPredicate(<Self as Foo<T>>, polarity:Positive), bound_vars: [] },
//                 Binder { value: TraitPredicate(<T as Foo<Self>>, polarity:Positive), bound_vars: [] },
//                 Binder { value: TraitPredicate(<T as std::marker::MetaSized>, polarity:Positive), bound_vars: [] },
//                 Binder { value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive), bound_vars: [] }
//             ]
//         },
//         body_id=DefId(0:3 ~ whee[5dd0]::Foo),
//         clause=Binder {
//             value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive),
//             bound_vars: []
//         },
//         span=whee.rs:1:1: 1:40 (#0)
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder {
//                 value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive),
//                 bound_vars: []
//             }
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder {
//                 value: WellFormed(Term::Ty(Self/#0)),
//                 bound_vars: []
//             }
//         1ms  INFO rustc_trait_selection::traits::wf return=[
//             Obligation(
//                 predicate=Binder {
//                     value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive),
//                     bound_vars: []
//                 },
//                 depth=0
//             ),
//             Obligation(
//                 predicate=Binder {
//                     value: WellFormed(Term::Ty(Self/#0)),
//                     bound_vars: []
//                 },
//                 depth=0
//             )
//         ]
//
//     rustc_trait_selection::traits::normalize::normalize_with_depth_to
//         depth=0,
//         value=Binder {
//             value: TraitPredicate(<T as std::marker::MetaSized>, polarity:Positive),
//             bound_vars: []
//         }
//     rustc_trait_selection::traits::wf::clause_obligations
//         param_env=ParamEnv {
//             caller_bounds: [
//                 Binder { value: TraitPredicate(<Self as Foo<T>>, polarity:Positive), bound_vars: [] },
//                 Binder { value: TraitPredicate(<T as Foo<Self>>, polarity:Positive), bound_vars: [] },
//                 Binder { value: TraitPredicate(<T as std::marker::MetaSized>, polarity:Positive), bound_vars: [] },
//                 Binder { value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive), bound_vars: [] }
//             ]
//         },
//         body_id=DefId(0:3 ~ whee[5dd0]::Foo),
//         clause=Binder {
//             value: TraitPredicate(<T as std::marker::MetaSized>, polarity:Positive),
//             bound_vars: []
//         },
//         span=whee.rs:1:15: 1:16 (#0)
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder { value: TraitPredicate(<T as std::marker::MetaSized>, polarity:Positive), bound_vars: [] }
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder { value: WellFormed(Term::Ty(T/#1)), bound_vars: [] }
//
//         0ms  INFO rustc_trait_selection::traits::wf
//             return=[
//                 Obligation(
//                     predicate=Binder { value: TraitPredicate(<T as std::marker::MetaSized>, polarity:Positive), bound_vars: [] },
//                     depth=0
//                 ),
//                 Obligation(
//                     predicate=Binder { value: WellFormed(Term::Ty(T/#1)), bound_vars: [] },
//                     depth=0
//                 )
//             ]
//
//     rustc_trait_selection::traits::normalize::normalize_with_depth_to
//         depth=0,
//         value=Binder { value: TraitPredicate(<T as Foo<Self>>, polarity:Positive), bound_vars: [] }
//
//     rustc_trait_selection::traits::wf::clause_obligations
//         param_env=ParamEnv {
//             caller_bounds: [
//                 Binder { value: TraitPredicate(<Self as Foo<T>>, polarity:Positive), bound_vars: [] },
//                 Binder { value: TraitPredicate(<T as Foo<Self>>, polarity:Positive), bound_vars: [] },
//                 Binder { value: TraitPredicate(<T as std::marker::MetaSized>, polarity:Positive), bound_vars: [] },
//                 Binder { value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive), bound_vars: [] }
//             ]
//         },
//         body_id=DefId(0:3 ~ whee[5dd0]::Foo),
//         clause=Binder {
//             value: TraitPredicate(<T as Foo<Self>>, polarity:Positive),
//             bound_vars: []
//         },
//         span=whee.rs:1:27: 1:36 (#0)
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder { value: TraitPredicate(<T as std::marker::MetaSized>, polarity:Positive), bound_vars: [] }
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder { value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive), bound_vars: [] }
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder { value: TraitPredicate(<Self as Foo<T>>, polarity:Positive), bound_vars: [] }
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder { value: TraitPredicate(<T as Foo<Self>>, polarity:Positive), bound_vars: [] }
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder { value: WellFormed(Term::Ty(T/#1)), bound_vars: [] }
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder { value: WellFormed(Term::Ty(Self/#0)), bound_vars: [] }
//
//         0ms  INFO rustc_trait_selection::traits::wf return=[
//             Obligation(predicate=Binder { value: TraitPredicate(<T as std::marker::MetaSized>, polarity:Positive), bound_vars: [] }, depth=0),
//             Obligation(predicate=Binder { value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive), bound_vars: [] }, depth=0),
//             Obligation(predicate=Binder { value: TraitPredicate(<Self as Foo<T>>, polarity:Positive), bound_vars: [] }, depth=0),
//             Obligation(predicate=Binder { value: TraitPredicate(<T as Foo<Self>>, polarity:Positive), bound_vars: [] }, depth=0),
//             Obligation(predicate=Binder { value: WellFormed(Term::Ty(T/#1)), bound_vars: [] }, depth=0),
//             Obligation(predicate=Binder { value: WellFormed(Term::Ty(Self/#0)), bound_vars: [] }, depth=0)
//         ]
//
//     rustc_trait_selection::traits::normalize::normalize_with_depth_to
//         depth=0,
//         value=Binder {
//             value: TraitPredicate(<Self as Foo<T>>, polarity:Positive),
//             bound_vars: []
//         }
//
//     rustc_trait_selection::traits::wf::clause_obligations
//         param_env=ParamEnv {
//             caller_bounds: [
//                 Binder { value: TraitPredicate(<Self as Foo<T>>, polarity:Positive), bound_vars: [] },
//                 Binder { value: TraitPredicate(<T as Foo<Self>>, polarity:Positive), bound_vars: [] },
//                 Binder { value: TraitPredicate(<T as std::marker::MetaSized>, polarity:Positive), bound_vars: [] },
//                 Binder { value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive), bound_vars: [] }
//             ]
//         },
//         body_id=DefId(0:3 ~ whee[5dd0]::Foo),
//         clause=Binder {
//             value: TraitPredicate(<Self as Foo<T>>, polarity:Positive),
//             bound_vars: []
//         },
//         span=no-location (#0)
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder { value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive), bound_vars: [] }
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder { value: TraitPredicate(<T as std::marker::MetaSized>, polarity:Positive), bound_vars: [] }
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder { value: TraitPredicate(<T as Foo<Self>>, polarity:Positive), bound_vars: [] }
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder { value: TraitPredicate(<Self as Foo<T>>, polarity:Positive), bound_vars: [] }
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder { value: WellFormed(Term::Ty(Self/#0)), bound_vars: [] }
//
//         rustc_trait_selection::traits::normalize::normalize_with_depth_to
//             depth=0,
//             value=Binder { value: WellFormed(Term::Ty(T/#1)), bound_vars: [] }
//
//         0ms  INFO rustc_trait_selection::traits::wf return=[
//             Obligation(predicate=Binder { value: TraitPredicate(<Self as std::marker::MetaSized>, polarity:Positive), bound_vars: [] }, depth=0),
//             Obligation(predicate=Binder { value: TraitPredicate(<T as std::marker::MetaSized>, polarity:Positive), bound_vars: [] }, depth=0),
//             Obligation(predicate=Binder { value: TraitPredicate(<T as Foo<Self>>, polarity:Positive), bound_vars: [] }, depth=0),
//             Obligation(predicate=Binder { value: TraitPredicate(<Self as Foo<T>>, polarity:Positive), bound_vars: [] }, depth=0),
//             Obligation(predicate=Binder { value: WellFormed(Term::Ty(Self/#0)), bound_vars: [] }, depth=0),
//             Obligation(predicate=Binder { value: WellFormed(Term::Ty(T/#1)), bound_vars: [] }, depth=0)
//         ]
// ```
//
// TODO: Figure out this nightmare.

pub trait Foo {
    type Bar: Foo<Bar = Self>;
}

pub trait Meow<T: Meow<Self>> {}
