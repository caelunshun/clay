mod case1 {
    trait Meow<T: Thump<Other>> {
        type Other;
    }

    trait Thump<T> {}

    impl Thump<i32> for u32 {}
    impl Thump<u32> for u32 {}

    trait Funny {
        // error[E0277]: the trait bound `u32: Thump<<<Self as Funny>::Hehe as Meow<u32>>::Other>` is not satisfied
        type Hehe: Meow<u32>;
    }
}

mod case2 {
    trait Meow<T: Thump<Other>> {
        type Other;
    }

    trait Thump<T> {}

    impl Thump<u32> for u32 {}

    trait Funny {
        // error[E0277]: the trait bound `u32: Thump<<<Self as Funny>::Hehe as Meow<u32>>::Other>` is not satisfied
        type Hehe: Meow<u32>;
    }
}

mod case3 {
    trait Meow<T: Thump<Other>> {
        type Other;
    }

    trait Thump<T> {}

    impl Thump<i32> for u32 {}
    impl Thump<u32> for u32 {}

    trait Funny {
        // OK
        type Hehe: Meow<u32> + Meow<u32, Other = u32>;
    }
}

mod case4 {
    trait Meow<T: Thump<Other>> {
        type Other;
    }

    trait Thump<T> {}

    impl<T> Thump<(T,)> for T {}
    impl<T> Thump<T> for T {}

    trait Funny {
        // OK
        type Hehe: for<T> Meow<T> + for<T> Meow<T, Other = T>;
    }
}
