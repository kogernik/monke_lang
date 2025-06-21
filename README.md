# Monke
Evaluator and VM for the Monkey language, but in Rust

[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/kogernik/monke_lang)
[Closure Implementation](https://deepwiki.com/search/how-are-closures-implemented-p_726d9d69-086a-471f-a4b1-e0eaf29f10a1)
[Pratt Parser Explanation](https://deepwiki.com/search/explain-in-detail-how-pratt-pa_72540bc6-4990-4da8-aaff-18d4023bb4d5)

Originally implemented by Thorsten Ball in Go
[Writing An Interpreter In Go](https://interpreterbook.com/)
[Writing A Compiler In Go](https://compilerbook.com/)

## REPL
```bash
cargo run -- --help
```

## TEST
```bash
cargo test
```

## BENCH
```bash
cargo bench fib
cargo flamegraph --dev --bench fib
```

