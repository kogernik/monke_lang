use std::rc::Rc;
use std::{path::PathBuf, time::Instant};

use clap::{Parser as ClapParser, Subcommand};
use monkey_interpreter::evaluator;
use monkey_interpreter::{
    builtin::BUILTIN_FNS,
    evaluator::Evaluator,
    lexer::{self, Lexer},
    object::Object,
    parser::parser::{self, Parser},
    vm::{
        compiler::Compiler,
        symbol_table::SymbolTable,
        vm::{self, VM},
    },
};

#[derive(ClapParser)]
#[command(version = "1", about = "Monke Lang CLI", long_about = None)]
struct Cli {
    /// Optional name to operate on
    name: Option<String>,

    /// Sets a custom config file
    #[arg(short, long, value_name = "FILE")]
    config: Option<PathBuf>,

    /// Turn debugging information on
    #[arg(short, long, action = clap::ArgAction::Count)]
    debug: u8,

    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    Lex { input: String },
    Parse { input: String },
    Eval,
    VM,
    FibRust,
    FibVM,
    FibEval,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();

    match &cli.command {
        Some(Commands::FibRust) => {
            let tim = Instant::now();
            fn fib(n: usize) -> usize {
                match n {
                    1 | 2 => 1,
                    _ => fib(n - 1) + fib(n - 2),
                }
            }

            dbg!(fib(35));
            dbg!(tim.elapsed());
        }

        Some(Commands::FibVM) => {
            let tim = Instant::now();

            let fib = "
                let fib = fn(n) { if (n==1) { return 1; } if (n==2) { return 1; } return fib(n-1) + fib(n-2) };
                //let fib = fn(n) { if (n<=1) { return n; } return fib(n-1) + fib(n-2) };
                fib(35)
            ";

            let result = vm::run_vm_on_input(fib).unwrap();
            dbg!(result);

            dbg!(tim.elapsed());
        }

        Some(Commands::FibEval) => {
            let tim = Instant::now();

            let fib = "
                let fib = fn(n) { if (n==1) { return 1; } if (n==2) { return 1; } return fib(n-1) + fib(n-2) };
                let fib = fn(n) { if (n<=1) { return n; } return fib(n-1) + fib(n-2) };
                fib(35)
            ";

            let result = evaluator::run_eval_on_input(fib).unwrap();
            dbg!(result);

            dbg!(tim.elapsed());
        }

        Some(Commands::Lex { input }) => {
            let lex = Lexer::new(input);

            let tokens: Vec<lexer::Token> = lex.collect();

            println!("{:?}", tokens);
        }

        Some(Commands::Parse { input }) => {
            let lexer = Lexer::new(input);
            let mut parser = Parser::new(lexer);
            let program = (&mut parser).collect::<Vec<_>>();

            let errors = parser.errors;
            if !errors.is_empty() {
                println!("Parser has {} errors:", errors.len());
                for error in errors {
                    println!("  {}", error);
                }
                return Ok(());
            }

            println!("Program AST:");
            println!("{:#?}", program);
        }

        Some(Commands::Eval) => {
            println!("===================================");
            println!("          REPL Evaluator           ");
            println!("===================================");

            let lines = std::io::stdin().lines().map(Result::unwrap);

            for line in lines {
                let mut evaluator = Evaluator::new();
                let lex = Lexer::new(&line);
                let mut parser = Parser::new(lex);
                let program: Vec<parser::Statement> = (&mut parser).collect();

                if !parser.errors.is_empty() {
                    dbg!(parser.errors);
                }

                println!(">>> {}\n", evaluator.evaluate_program(&program)?);
            }
        }

        Some(Commands::VM) => {
            println!("===================================");
            println!("             REPL VM               ");
            println!("===================================");

            let lines = std::io::stdin().lines().map(Result::unwrap);

            let mut constants: Vec<Rc<Object<'_>>> = vec![];
            let mut globals = vec![Rc::new(Object::Integer(0)); vm::GLOBALS_SIZE];
            let mut symbol_table = SymbolTable::new();

            for (idx, (bfn_name, _)) in BUILTIN_FNS.iter().enumerate() {
                symbol_table.define_builtin(idx, bfn_name);
            }

            let mut lines_history = Vec::with_capacity(1024);

            for line in lines {
                lines_history.push(line);

                // FIXME If lines_history grows, this will be a dangling pointer
                // or maybe not, it works with let mut lines_history = Vec::with_capacity(1)
                let line = unsafe {
                    let line_ptr = lines_history.last().unwrap().as_str() as *const str;
                    std::mem::transmute::<&str, &'static str>(&*line_ptr)
                };

                let lex = Lexer::new(&line);
                let mut parser = Parser::new(lex);
                let program: Vec<parser::Statement> = (&mut parser).collect();

                if !&parser.errors.is_empty() {
                    dbg!(&parser.errors);
                    continue;
                }

                let compiler = Compiler::new_with_state(symbol_table, constants);

                let (bytecode, compiler_constants, compiler_symbol_table) =
                    compiler.compile(&program)?;

                let mut vm = VM::new_with_globals_store(bytecode, compiler_constants, globals);

                match vm.run() {
                    Ok(res) => println!(">>> {res:#?}\n"),
                    Err(err) => println!(">>> {err:#?}"),
                }

                globals = vm.globals;
                constants = vm.constants;
                symbol_table = compiler_symbol_table.replace(SymbolTable::new());
            }
        }

        None => panic!("Don't know what to do"),
    }

    Ok(())
}
