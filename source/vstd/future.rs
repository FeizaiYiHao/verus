#![allow(unused_imports)]

use super::prelude::*;
use core::future::*;
verus! {

#[verifier::external_trait_specification]
pub trait ExFuture {
    type ExternalTraitSpecificationFor: core::future::Future;

    type Output;
}

pub trait FutureAdditionalSpecFns<T>: Future<Output = T> {
    #[verifier::prophetic]
    spec fn view(&self) -> T;

    #[verifier::prophetic]
    spec fn awaited(&self) -> bool;

    // Do not call this function. Call the regular Rust `await` keyword instead.
    fn exec_await(self) -> (ret: T)
        ensures
            self.awaited() == true,
            ret == self@,
        opens_invariants any
    ;
}

impl<V, T: Future<Output = V>> FutureAdditionalSpecFns<V> for T {
    #[verifier::prophetic]
    #[rustc_diagnostic_item = "verus::vstd::Future::FutureAdditionalSpecFns::view"]
    uninterp spec fn view(&self) -> V;

    #[verifier::prophetic]
    #[rustc_diagnostic_item = "verus::vstd::Future::FutureAdditionalSpecFns::awaited"]
    uninterp spec fn awaited(&self) -> bool;

    // Do not call this function. Call the regular Rust `await` keyword instead.
    #[rustc_diagnostic_item = "verus::vstd::Future::FutureAdditionalSpecFns::exec_await"]
    #[verifier::external_body]
    fn exec_await(self) -> (ret: V) {
        unimplemented!()
    }
}

} // verus!
