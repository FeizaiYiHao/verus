use core::marker::PhantomData;
use super::pervasive::*;
use builtin::*;
use builtin_macros::*;
use core::marker;
use std::future::*;


impl<V> Future for AsyncFuture<V>{
    type Output = V;
    fn poll(self: std::pin::Pin<&mut Self>, _: &mut std::task::Context<'_>) -> std::task::Poll<<Self as std::future::Future>::Output> { todo!() }
}

verus! {

#[verifier::external_body]
#[verifier::reject_recursive_types(V)]
pub struct AsyncFuture<V> {
    phantom_data: PhantomData<V>
}

impl<V> AsyncFuture<V> {
    pub uninterp spec fn awaited(&self) -> bool;
    pub uninterp spec fn view(&self) -> V;
    
    #[verifier::external_body]
    pub fn verus_impl_from(v:V) -> (ret:AsyncFuture<V>)
        ensures
            ret@ == v,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn verus_impl_await(self) -> (ret:V)
        ensures
            ret == self@,
            self.awaited() == true,
    {
        unimplemented!()
    }
}

}