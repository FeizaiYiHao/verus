use verus_builtin::*;
use verus_builtin_macros::*;

verus! {
trait DummyTrait{
    type Output;
    fn foo(&self) -> (ret: bool)
    ensures
        ret == false;

    spec fn bar(&self) -> bool;
}
impl<T> DummyTrait for T{
    type Output = T;
    fn foo(&self) -> (ret: bool)
    {
        false
    }
    spec fn bar(&self) -> bool{
        true
    }
}
#[verifier::external]
fn return_opaque_variable<T>(x:T, y:T) -> (impl DummyTrait<Output = T>, impl DummyTrait<Output = T>)
{
    (x, y)
}
assume_specification<T> [ return_opaque_variable::<T> ](x:T, y:T) -> (ret: (impl DummyTrait<Output = T>, impl DummyTrait<Output = T>))
    ensures ret.0.bar();

pub fn main(){}
}