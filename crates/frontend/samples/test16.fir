pub trait Meow<'a> {}

struct LivesForAll<'b>(&'b ());
struct LivesForSome1<'b>(&'b ());
struct LivesForSome2<'b>(&'b ());

impl<'a, 'b> Meow<'a> for LivesForAll<'b> {}
impl<'a: 'b, 'b> Meow<'a> for LivesForSome1<'b> {}
impl<'a, 'b: 'a> Meow<'a> for LivesForSome2<'b> {}

struct Foo<T: for<'a> Meow<'a>>(T);

struct Test1<'b>(Foo<LivesForAll<'b>>);
struct Test2<'b>(Foo<LivesForSome1<'b>>);
struct Test3<'b>(Foo<LivesForSome2<'b>>);
struct Test4(Foo<LivesForSome2<'gc>>);
