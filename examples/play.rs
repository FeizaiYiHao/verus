use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

#[verifier::veriflat_kernel_level]
fn foo(){
    bar();
}

#[verifier::veriflat_push]
fn bar(){
    baz();
    baz();
}

#[verifier::veriflat_push]
fn baz(){}

fn main() {
}

} // verus!
