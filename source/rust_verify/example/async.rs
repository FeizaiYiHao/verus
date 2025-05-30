#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
use vstd::async_future::AsyncFuture;

verus! {
async fn add(x:usize, y:usize) -> (ret: usize)
    requires
        x + y <= usize::MAX
    ensures
        ret == x + y,
{
    x + y
}

async fn test(){
    let future = add(1,2).await;
    // let sum = future.await;
    assert(future == 3);
}

fn main(){
}
}