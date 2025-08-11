async fn bar(f:impl Future<Output=usize>){
    let res = f.await;
}