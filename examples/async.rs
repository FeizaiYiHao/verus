use verus_builtin_macros::*;
use vstd::*;
use vstd::future::*;

verus! {
    trait DummyTrait{
        spec fn s(&self) -> bool;
    }
    impl DummyTrait for bool{
        spec fn s(&self) -> bool{
            true
        }
    }
    // fn return_opaque_variable() -> impl DummyTrait{
    //     true
    // }


    async fn foo() -> (ret: impl DummyTrait)
        ensures
            ret.awaited() ==> ret@.s(),
    {
        if true{
            return true;
            true
        }else{
            true
        }
    }
}

fn main(){}