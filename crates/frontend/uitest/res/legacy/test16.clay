pub trait Meow<'a> {}

struct LivesForAll<'b>(&'b ());
struct LivesForSome1<'b>(&'b ());
struct LivesForSome2<'b>(&'b ());

impl<'a, 'b> Meow<'a> for LivesForAll<'b> {}
impl<'a: &longer 'b, 'b> Meow<'a> for LivesForSome1<'b> {}
impl<'a, 'b: &longer 'a> Meow<'a> for LivesForSome2<'b> {}

struct Foo<T: for<'a> Meow<'a>>(T);

struct Test1<'b>(Foo<LivesForAll<'b>>);
struct Test2<'b>(Foo<LivesForSome1<'b>>);
struct Test3<'b>(Foo<LivesForSome2<'b>>);
struct Test4(Foo<LivesForSome2<'gc>>);
struct Test5<'a, T: Meow<'a>>(Foo<T>);
struct Test6<T: for<'h> Meow<'h>>(Foo<T>);
struct Test7<'i, T: for<'h: &longer 'i> Meow<'h>>(Foo<T>);

trait Fn<I, O> {}
struct Test8<T: for<'a, V> Fn<&'a V, &'a V>>;
struct Test9<T: for<'a, V: &longer 'a> Fn<&'a V, &'a V>>;
struct Test10(Test8<MyFunc>, Test9<MyFunc>);

struct MyFunc;

impl<'a, V: &longer 'a, W> Fn<&'a V, W> for MyFunc {}
