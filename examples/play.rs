use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

#[verifier::veriflat_push]
fn foo(){}

fn main() {
}

} // verus!
