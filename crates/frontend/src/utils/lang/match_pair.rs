#[macro_export]
macro_rules! match_pair {
    ($tuple:expr => {
        $(($lhs:pat, $rhs:pat $(,)?) $(| ($lhs_alt:pat, $rhs_alt:pat $(,)?))* => { $($body:tt)* } $(,)? )*
        _ => { $($fallback:tt)* }
    }) => {{
        #[allow(unused)]
        if 0u32 != 0u32 {
            match $tuple {
                $(($lhs, _) $(| ($lhs_alt, _))* => {})*
                $((_, $rhs) $(| (_, $rhs_alt))* => {})*
            }

            loop {}
        } else {
            match $tuple {
                $(($lhs, $rhs) $(| ($lhs_alt, $rhs_alt))* => { $($body)* },)*
                _ => { $($fallback)* },
            }
        }
    }};
}

pub use match_pair;
