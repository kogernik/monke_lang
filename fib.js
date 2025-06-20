function fib(n) {
    if (n <= 1) {
        return n;
    } else {
        return fib(n - 1) + fib(n - 2);
    }
}

const n = 35;

const start = process.hrtime.bigint();
const result = fib(n);
const end = process.hrtime.bigint();

const elapsedMs = Number(end - start) / 1_000_000;

console.log(`fib(${n}) = ${result}`);
console.log(`elapsedMs: ${elapsedMs.toFixed(3)} мс`);
