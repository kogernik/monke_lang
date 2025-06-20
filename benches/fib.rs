use criterion::{Criterion, criterion_group, criterion_main};
use monkey_interpreter::vm::vm;
use std::hint::black_box;

fn fibonacci(n: u64) {
    let fib = format!("
        let fib = fn(n) {{ if (n==1) {{ return 1; }} if (n==2) {{ return 1; }} return fib(n-1) + fib(n-2) }};
        fib({n})
    ");

    let _result = vm::run_vm_on_input(&fib).unwrap();
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 32", |b| b.iter(|| fibonacci(black_box(32))));
    c.bench_function("fib 33", |b| b.iter(|| fibonacci(black_box(33))));
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(10);
    targets = criterion_benchmark
}
criterion_main!(benches);
