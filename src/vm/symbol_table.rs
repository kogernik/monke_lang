use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::monke_error::MonkeError;

#[derive(Debug, Clone, PartialEq)]
pub enum SymbolScope {
    Global,
    Local,
    Builtin,
    Free,
    Function,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Symbol<'i> {
    pub name: &'i str,
    pub scope: SymbolScope,
    pub idx: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SymbolTable<'i> {
    pub store: HashMap<&'i str, Rc<Symbol<'i>>>,
    pub num_definitions: usize,
    pub outer: Option<Rc<RefCell<SymbolTable<'i>>>>,
    pub free_symbols: Vec<Rc<Symbol<'i>>>,
}

impl<'i> SymbolTable<'i> {
    pub fn new() -> Self {
        Self {
            store: HashMap::new(),
            num_definitions: 0,
            outer: None,
            free_symbols: vec![],
        }
    }
    pub fn with_outer(outer: Rc<RefCell<SymbolTable<'i>>>) -> Self {
        Self {
            store: HashMap::new(),
            num_definitions: 0,
            outer: Some(outer),
            free_symbols: vec![],
        }
    }

    pub fn define(&mut self, name: &'i str) -> Rc<Symbol<'i>> {
        let scope = if self.outer.is_none() {
            SymbolScope::Global
        } else {
            SymbolScope::Local
        };

        let symbol = Rc::new(Symbol {
            name,
            scope,
            idx: self.num_definitions,
        });

        self.store.insert(name, Rc::clone(&symbol));
        self.num_definitions += 1;

        symbol
    }

    pub fn define_builtin(&mut self, idx: usize, name: &'i str) -> Rc<Symbol<'i>> {
        let symbol = Rc::new(Symbol {
            name,
            scope: SymbolScope::Builtin,
            idx,
        });

        self.store.insert(name, Rc::clone(&symbol));

        symbol
    }

    pub fn define_free(&mut self, original: Rc<Symbol<'i>>) -> Rc<Symbol<'i>> {
        self.free_symbols.push(Rc::clone(&original));

        let symbol = Rc::new(Symbol {
            name: original.name,
            idx: self.free_symbols.len() - 1,
            scope: SymbolScope::Free,
        });

        self.store.insert(original.name, Rc::clone(&symbol));

        symbol
    }

    pub fn define_function_name(&mut self, name: &'i str) -> Rc<Symbol<'i>> {
        let symbol = Rc::new(Symbol {
            name,
            idx: 0,
            scope: SymbolScope::Function,
        });

        self.store.insert(name, Rc::clone(&symbol));

        symbol
    }

    pub fn resolve_or_define_free(&mut self, name: &'i str) -> Result<Rc<Symbol<'i>>, MonkeError> {
        match (self.store.get(name), &self.outer) {
            (Some(symbol), _) => Ok(Rc::clone(symbol)),

            (None, Some(outer)) => {
                let outer_symbol = outer.borrow_mut().resolve_or_define_free(name)?;

                let resolved_symbol = match &outer_symbol.scope {
                    SymbolScope::Builtin | SymbolScope::Global => outer_symbol,

                    SymbolScope::Local | SymbolScope::Free => self.define_free(outer_symbol),

                    SymbolScope::Function => panic!(
                        "Symbol = {outer_symbol:?} should be defined only in SymbolTable.store, instead found in SymbolTable.outer"
                    ),
                };

                Ok(resolved_symbol)
            }

            _ => MonkeError::new(format!("Undefined symbol {name}")).into(),
        }
    }
}

#[cfg(test)]
mod symbol_table_tests {
    use std::collections::BTreeMap;

    use super::*;

    #[test]
    fn define_global() {
        let expected = BTreeMap::from([
            (
                "a",
                Symbol {
                    name: "a",
                    scope: SymbolScope::Global,
                    idx: 0,
                },
            ),
            (
                "b",
                Symbol {
                    name: "b",
                    scope: SymbolScope::Global,
                    idx: 1,
                },
            ),
        ]);

        let mut global = SymbolTable::new();

        let a = global.define("a");
        assert_eq!(a.as_ref(), expected.get("a").unwrap());

        let b = global.define("b");
        assert_eq!(b.as_ref(), expected.get("b").unwrap());
    }

    #[test]
    fn resolve_global() {
        let expected = BTreeMap::from([
            (
                "a",
                Symbol {
                    name: "a",
                    scope: SymbolScope::Global,
                    idx: 0,
                },
            ),
            (
                "b",
                Symbol {
                    name: "b",
                    scope: SymbolScope::Global,
                    idx: 1,
                },
            ),
        ]);

        let mut global = SymbolTable::new();
        global.define("a");
        global.define("b");

        for (_, v) in &expected {
            let result = global.resolve_or_define_free(v.name);
            assert_eq!(v, result.unwrap().as_ref(), "{:#?}", global);
        }
    }

    #[test]
    fn resolve_local() {
        let expected = BTreeMap::from([
            (
                "a",
                Symbol {
                    name: "a",
                    scope: SymbolScope::Global,
                    idx: 0,
                },
            ),
            (
                "b",
                Symbol {
                    name: "b",
                    scope: SymbolScope::Global,
                    idx: 1,
                },
            ),
            (
                "c",
                Symbol {
                    name: "c",
                    scope: SymbolScope::Local,
                    idx: 0,
                },
            ),
            (
                "d",
                Symbol {
                    name: "d",
                    scope: SymbolScope::Local,
                    idx: 1,
                },
            ),
        ]);

        let mut global = SymbolTable::new();
        global.define("a");
        global.define("b");

        let mut local = SymbolTable::with_outer(Rc::new(RefCell::new(global)));
        local.define("c");
        local.define("d");

        for (_, v) in &expected {
            let result = local.resolve_or_define_free(v.name);
            assert_eq!(v, result.unwrap().as_ref(), "{:#?}", local);
        }
    }

    #[test]
    fn resolve_nested_local() {
        let expected_first_local = BTreeMap::from([
            (
                "a",
                Symbol {
                    name: "a",
                    scope: SymbolScope::Global,
                    idx: 0,
                },
            ),
            (
                "b",
                Symbol {
                    name: "b",
                    scope: SymbolScope::Global,
                    idx: 1,
                },
            ),
            (
                "c",
                Symbol {
                    name: "c",
                    scope: SymbolScope::Local,
                    idx: 0,
                },
            ),
        ]);

        let mut global = Rc::new(RefCell::new(SymbolTable::new()));
        global.borrow_mut().define("a");
        global.borrow_mut().define("b");

        let first_local = Rc::new(RefCell::new(SymbolTable::with_outer(Rc::clone(&global))));

        first_local.borrow_mut().define("c");

        for (_, v) in &expected_first_local {
            let result = first_local.borrow_mut().resolve_or_define_free(v.name);
            assert_eq!(v, result.unwrap().as_ref(), "{:#?}", first_local.borrow());
        }

        let expected_second_local = BTreeMap::from([
            (
                "a",
                Symbol {
                    name: "a",
                    scope: SymbolScope::Global,
                    idx: 0,
                },
            ),
            (
                "b",
                Symbol {
                    name: "b",
                    scope: SymbolScope::Global,
                    idx: 1,
                },
            ),
            (
                "d",
                Symbol {
                    name: "d",
                    scope: SymbolScope::Local,
                    idx: 0,
                },
            ),
            (
                "e",
                Symbol {
                    name: "e",
                    scope: SymbolScope::Local,
                    idx: 1,
                },
            ),
        ]);

        let mut second_local = Rc::new(RefCell::new(SymbolTable::with_outer(Rc::clone(&global))));

        second_local.borrow_mut().define("d");
        second_local.borrow_mut().define("e");

        for (_, v) in &expected_second_local {
            let result = second_local.borrow_mut().resolve_or_define_free(v.name);
            assert_eq!(v, result.unwrap().as_ref(), "{:#?}", second_local.borrow());
        }
    }

    #[test]
    fn resolve_free() {
        let expected_first_local = BTreeMap::from([
            (
                "a",
                Symbol {
                    name: "a",
                    scope: SymbolScope::Global,
                    idx: 0,
                },
            ),
            (
                "b",
                Symbol {
                    name: "b",
                    scope: SymbolScope::Global,
                    idx: 1,
                },
            ),
            (
                "c",
                Symbol {
                    name: "c",
                    scope: SymbolScope::Local,
                    idx: 0,
                },
            ),
            (
                "d",
                Symbol {
                    name: "d",
                    scope: SymbolScope::Local,
                    idx: 1,
                },
            ),
        ]);

        let expected_second_local = BTreeMap::from([
            (
                "a",
                Symbol {
                    name: "a",
                    scope: SymbolScope::Global,
                    idx: 0,
                },
            ),
            (
                "b",
                Symbol {
                    name: "b",
                    scope: SymbolScope::Global,
                    idx: 1,
                },
            ),
            (
                "c",
                Symbol {
                    name: "c",
                    scope: SymbolScope::Free,
                    idx: 0,
                },
            ),
            (
                "d",
                Symbol {
                    name: "d",
                    scope: SymbolScope::Free,
                    idx: 1,
                },
            ),
            (
                "e",
                Symbol {
                    name: "e",
                    scope: SymbolScope::Local,
                    idx: 0,
                },
            ),
            (
                "f",
                Symbol {
                    name: "f",
                    scope: SymbolScope::Local,
                    idx: 1,
                },
            ),
        ]);

        let expected_second_free_symbols = vec![
            Rc::new(Symbol {
                name: "c",
                scope: SymbolScope::Local,
                idx: 0,
            }),
            Rc::new(Symbol {
                name: "d",
                scope: SymbolScope::Local,
                idx: 1,
            }),
        ];

        let mut global = Rc::new(RefCell::new(SymbolTable::new()));
        global.borrow_mut().define("a");
        global.borrow_mut().define("b");

        let first_local = Rc::new(RefCell::new(SymbolTable::with_outer(Rc::clone(&global))));

        first_local.borrow_mut().define("c");
        first_local.borrow_mut().define("d");

        let mut second_local = Rc::new(RefCell::new(SymbolTable::with_outer(Rc::clone(
            &first_local,
        ))));

        second_local.borrow_mut().define("e");
        second_local.borrow_mut().define("f");

        for (_, v) in &expected_first_local {
            let result = first_local.borrow_mut().resolve_or_define_free(v.name);
            assert_eq!(v, result.unwrap().as_ref(), "{:#?}", first_local.borrow());
        }

        for (_, v) in &expected_second_local {
            let result = second_local.borrow_mut().resolve_or_define_free(v.name);
            assert_eq!(v, result.unwrap().as_ref(), "{:#?}", second_local.borrow());
        }

        assert_eq!(
            second_local.borrow().free_symbols,
            expected_second_free_symbols
        );
    }
}
