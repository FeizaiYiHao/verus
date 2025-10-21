use verus_builtin_macros::*;
use vstd::*;
use vstd::future::*;

verus! {
    pub async fn foo() -> (ret: usize)
        ensures
            ret.awaited() ==> ret@ == 1,
    {
        if true{
            return 2;
            1
        }else{
            2
        }
    }
}

fn main(){}