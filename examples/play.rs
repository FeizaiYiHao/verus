use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

#[verifier::veriflat_syscall]
fn foo(){
    bar();
}

#[verifier::veriflat_push]
fn bar(){}

fn main() {
}

} // verus!
