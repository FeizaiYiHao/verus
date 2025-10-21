use verus_builtin_macros::*;
use vstd::*;
use vstd::future::*;

verus! {
    pub async fn foo() -> (ret: usize)
        ensures
            ret.awaited() ==> ret@ == 1,
    {
        1
    }
}

fn main(){}