use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

#[verifier::veriflat_syscall]
fn foo(){}

fn main() {
}

} // verus!
