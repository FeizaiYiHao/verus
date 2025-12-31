#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

fn assert_spec_eq_type_err(err: TestErr, typ1: &str, typ2: &str) {
    assert_eq!(err.errors.len(), 1);
    let err0 = &err.errors[0];
    assert!(err0.code.is_none());
    assert!(err0.message.contains("mismatched types; types must be compatible to use == or !="));
    assert!(err0.spans.len() == 2 || err0.spans.len() == 3);
    assert_spans_contain(err0, typ1);
    assert_spans_contain(err0, typ2);
}

test_verify_one_file! {
    #[test] test_basic_async_function_ensures_pass verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                ret == 1,
        {
            1
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_basic_async_function_ensures_fail verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                ret == 2,  // FAILS
        {
            1
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_basic_async_function_and_await verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                ret == 1,
        {
            1
        }
        async fn bar() {
            let future = foo();
            let ret = future.await;
            assert(ret == 1);
        }
    } => Ok(())
}


test_verify_one_file! {
    #[test] test_basic_async_function_util verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                ret == 1,
        {
            1
        }
        async fn bar() {
            let future = foo();
            assert(future.awaited() ==> future@ == 1);
            let ret = future.await;
            assert(ret == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_basic_async_function_lifetime_fail verus_code! {
        use vstd::prelude::*;
        async fn foo(x :&usize) -> (ret: usize)
            ensures
                ret == 1,
        {
            1
        }
        async fn bar() {
            let mut x = 233;
            let future = foo(&x);
            x = 2333; 
            let ret = future.await;
            x = 2333;
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot assign to `x` because it is borrowed")
}

test_verify_one_file! {
    #[test] test_basic_async_function_nested_pass verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                ret == 233,
        {
            233
        }

        async fn foo_of_foo() -> (ret: impl Future<Output = usize>)
            ensures
                ret.awaited() ==> ret@ == 233,
        {
            foo()
        }
        async fn bar() {
            let future_of_future = foo_of_foo();
            let ret = future_of_future.await.await;
            assert(ret == 233);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_await_outside_of_async_function_fail verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                ret == 233,
        {
            233
        }

        fn bar() {
            let future = foo();
            future.await;
        }
    } => Err(err) => assert_rust_error_msg(err, "`await` is only allowed inside `async` functions and blocks")
}