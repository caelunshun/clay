struct Meow1<'a, 'b, 'c, T: 'a + 'b>(Thump<'c, T>);

struct Meow2<'a: 'c, 'b, 'c, T: 'a + 'b>(Thump<'c, T>);

struct Meow3<'a, 'b: 'c, 'c, T: 'a + 'b>(Thump<'c, T>);

struct Thump<'a, T: 'a>;
