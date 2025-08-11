// rust_verify/tests/example.rs
#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{prelude::*, seq_lib::*};
verus!{
    use std::future::Future;
    use vstd::future::*;
    // async fn async_bar() -> (ret:usize)
    //     ensures
    //         spec_await(ret) == 1 + 1,
    // {
    //     let f = async_bar();
    //     let res = f.await;
    //     assert(f == f);
    //     1 + 1
    // }

    // async fn bar(){
    //     let f = make_a_future(usize);
    // }
    // #[verifier::external_body]
    // pub fn make_a<T>(v: T) -> (ret: T)
    //     ensures
    //         ret == v,
    // {
    //     v
    // }

    // #[verifier::external_body]
    // pub async fn make_a_future<T>(v: T) -> (ret: T)
    //     ensures
    //         ret@ == v,
    // {
    //     v
    // }

    // async fn async_bar() -> (ret:usize)
    //     ensures
    //         // ret == ret,
    //         ret@ == ret@,
    //     //     spec_awaited(ret) ==> spec_await(ret) == 1 + 1,
    // {
    //     // let f = async_bar();
    //     // let res = exec_await(f);
    //     // assert(f == f);
    //     1 + 1
    // }

    async fn foo() -> (ret:usize)
        ensures
            ret@ == 1,
    {
        // let f = make_a_future(1);
        // assert(f == f);
        // // let z = 
        // return 1;
        // if true{
        //     // return 1;
        //     return 1;
        // }else{
        //     // return 1;
        //     1
        // }
        1
    }

    fn bar() -> (ret:())
        ensures
            ret == ret,
    {
        // let f = |y: u64| -> (z: u64)
        //     requires y == 2
        //     ensures z == 2
        // {
        //     y
        // };
        // assert(f == f);
        // let res = f(2);
        // 1
        // if true{
        //     return 1;
        //     // 1
        // }else{
        //     // return 1;
        //     1
        // }
        // 1
        let ret = ();

        assert(ret == ret);
        ret
    }
    // struct St{ 
    //     x: usize 
    // }
    

    // pub trait Tr{
    //     fn get_usize(&self) -> (ret: usize)
    //         ensures
    //             ret == self.spec_get_usize(),;
    //     spec fn spec_get_usize(&self) -> usize;
    // }
    
    // pub async fn foo(x: impl Future<Output = usize>) -> (ret: usize)
    // {
    //     // let z = exec_await(x);
    //     // assert(z == z);
    //     let f = async_bar();
    //     let z = f.await;
    //     assert(z == z);
    //     z
    // }


    // pub fn take(tracked t: usize) {}

    // pub fn foo(x: usize, tracked t: usize, g: Ghost<usize>) -> (ret: usize)
    // requires
    //     x == 1,
    // ensures
    //     ret == x,
    // {
    //     take(t);
    //     let y = t;
    //     return x;
    // }

    // proof fn consume<A>(tracked a: A, b: A) {}
    // proof fn test1<A>(tracked a: A, b: A) {
    //     consume(a, b);
    //     consume(a, b);
    // }

    pub assume_specification<A: ?Sized, B: ?Sized>[<&A as PartialEq<&B>>::eq](
        x: &&A,
        y: &&B,
    ) -> (res: bool)
        where A: PartialEq<B>;


} // verus!
#[verifier::external]
fn main() {}