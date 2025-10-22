use vstd::prelude::*;
use vstd::arithmetic::overflow::*;

verus! {
    trait DummyTrait{}
    impl<T> DummyTrait for T{}
    trait DummyTraitA{
        type Output;
    }
    impl<T> DummyTraitA for T{
        type Output = T;
    }
    fn return_opaque_variable() -> impl DummyTraitA<Output = impl DummyTrait>{
        true
    }
}

fn main(){}