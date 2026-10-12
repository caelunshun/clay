fn demo1(v: i32) {
    // FIXME: should be rejected as non-exhaustive
    match v {
        0 => {}
        ref mut v if { *v = 0; false } => {}
        1.. => {}
    }
}

fn demo2(v: &mut i32) {
    // FIXME: should be rejected as non-exhaustive
    match v {
        0 => {}
        _ if { *v = 0; false } => {}
        1.. => {}
    }
}
