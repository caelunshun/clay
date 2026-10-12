pub trait MyTrait {}

// This should be denied....
pub impl MyTrait for () {}

// ...as should this.
priv impl MyTrait for ((),) {}

// And don't forget this!
pub(in self) impl MyTrait for ((),) {}

// This is fine.
impl MyTrait for (((),),) {}
