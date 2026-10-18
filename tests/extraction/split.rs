#![allow(dead_code)]
pub mod validator {
    pub struct Token {
        pub value: u32,
    }
    pub fn token_value(token: &Token) -> u32 {
        token.value
    }
    pub trait Visitor {
        fn visit(&mut self, token: &Token) -> bool;
    }
    pub fn validate<V: Visitor>(v: &mut V, x: &Token) -> bool {
        v.visit(x)
    }
}
pub mod runtime {
    pub struct Compiler {
        pub sum: u32,
    }
    impl super::validator::Visitor for Compiler {
        fn visit(&mut self, token: &super::validator::Token) -> bool {
            self.sum = super::validator::token_value(token);
            true
        }
    }
    pub fn compile(x: &super::validator::Token) -> Compiler {
        let mut c = Compiler { sum: 0 };
        super::validator::validate(&mut c, x);
        c
    }
}
