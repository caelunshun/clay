struct Meow1<'a, 'b, 'c, T: &longer 'a + &longer 'b>(Thump<'c, T>);

struct Meow2<'a: &longer 'c, 'b, 'c, T: &longer 'a + &longer 'b>(Thump<'c, T>);

struct Meow3<'a, 'b: &longer 'c, 'c, T: &longer 'a + &longer 'b>(Thump<'c, T>);

struct Meow4<'a: &longer 'c, 'b: &longer 'c, 'c, T: &longer 'a + &longer 'b>(Thump<'c, T>);

struct Thump<'a, T: &longer 'a>;
