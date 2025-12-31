use verus_builtin_macros::*;
use vstd::*;
use std::future::*;
use vstd::future::*;
use vstd::prelude::*; 

verus! {
    // trait DummyTrait{
    //     spec fn dummy_spec(&self) -> bool;
    // }
    // impl DummyTrait for bool{
    //     spec fn dummy_spec(&self) -> bool{
    //         true
    //     }
    // }    
    // async fn foo() -> (ret: (impl DummyTrait, impl DummyTrait))
    //     ensures
    //         ret.0.dummy_spec(),
    // {
    //     (true, true)
    // }
    // async fn bar()
    // {
    //     let future = foo();
    //     assert(future.awaited() ==> future@.0.dummy_spec());
    //     let ret_0 = future.await.0;
    //     assert(ret_0.dummy_spec());
    // }
    // fn baz() -> (ret: impl Future<Output = (impl DummyTrait, impl DummyTrait)>)
    //     ensures
    //         ret.awaited() ==> ret@.0.dummy_spec(),
    // {
    //     foo()
    // }
    // async fn test_baz(){
    //     let future = baz();
    //     assert(future.awaited() ==> future@.0.dummy_spec());
    // }

    // async fn foo() -> (ret: usize)
    //     ensures
    //         ret == 233,
    // {
    //     233
    // }

    // fn bar() {
    //     let future = foo();
    //     future.await;
    // }

    #[verifier(external)]
    async fn negate_bool(b: bool, x: u8) -> bool {
        !b
    }

    #[verifier(external_fn_specification)]
    async fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
        requires x != 0,
        ensures ret_b == !b
    {
        negate_bool(b, x).await
    }
} 

fn main(){}