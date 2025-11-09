mod baz {
    mod foo {
        mod a {
            pub trait A {}
        }

        mod b {
            pub trait A {}
        }

        pub use a::*;
        pub use b::*;
    }

    mod bar {
        pub trait A {}
    }

    pub use foo::*;
    pub use bar::*;
}

// This should result in an ambiguity.
use baz::A;
