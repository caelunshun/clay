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
// Is it sound to let `'u2` outlive `'u4`? Well, does `live('u2)` imply `occupied('u4)`?
//
// TODO
fn main() {
    let x = 1;
    let y = &x;
    x;
    y;
}
