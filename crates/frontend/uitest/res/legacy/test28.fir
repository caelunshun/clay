// Here's how our borrow-checker reasons about this code.
//
// MIR:
//
// ```
// _0: ()
// _1: i32
// _2: i32
// _3: &'?0 i32
// _4: &'?1 i32
//
// _1 = Literal(1)
// _2 = Move(_1)
// _3 = Ref(Not, _2)
// _4 = Move(_3)
// discard(_2)
// discard(_4)
// _0 = Tuple([])
// return
// ```
//
// Type-check:
//
// ```
// constrain '?0: '?1
// => (_4 :: &'?1 i32) = Move(_3 :: &'?0 i32)
//
// constrain 'u2: '?0
// => (_3 :: &'?0 i32) = (Ref(Not, _2) :: &'u2)
//
// constrain '?1: 'u4
// => WF _4: &'?1 i32
//
// constrain '?0: 'u3
// => WF _3: &'?0 i32
// ```
//
// The universal relationships are...
//
// ```
// 'u2: '?0: '?1: 'u4
// 'u2: '?0: 'u3
// ```
//
// Is it sound to let `'u2` outlive `'u4`? This would require `_2`, the pointee of `_4`, to be
// occupied whenever `_4` is live. This is where dataflow gets its `live('rhs) => occupied('lhs)`
// condition from. We note, however, that `_4` is live at the data-flow point between `discard(_2)`
// and `discard(_4)` but that `_2` is not occupied, causing the outlives constraint to be rejected.
//
// This is exactly what the permission set reports...
//
// ```
// permit 'u0: 'u0
// permit 'u0: 'u1
// permit 'u0: 'u2
// permit 'u0: 'u3
// permit 'u0: 'u4
// permit 'u1: 'u1
// permit 'u2: 'u2
// permit 'u3: 'u2
// permit 'u3: 'u3
// permit 'u4: 'u4
// ```
//
// ...and so, the program is rejected.
fn main() {
    let x = 1;
    let y = &x;
    x;
    y;
}
