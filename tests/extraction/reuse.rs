#![allow(dead_code)]
pub mod validator {
    pub enum Kind { Small, Large }
    pub struct Token { pub kind: Kind, pub value: u32 }
    pub trait Visitor { fn visit(&mut self, token: &Token) -> bool; }
    pub fn validate<V: Visitor>(v: &mut V, x: &Token) -> bool { v.visit(x) }
}
pub mod runtime {
    pub struct Compiler { pub sum: u32 }
    impl super::validator::Visitor for Compiler {
        fn visit(&mut self, token: &super::validator::Token) -> bool {
            self.sum = match token.kind {
                super::validator::Kind::Small => token.value,
                super::validator::Kind::Large => token.value.wrapping_add(1),
            };
            true
        }
    }
    pub fn borrow_scope(flag: bool, x: &mut u32, y: &mut u32) {
        if flag {
            let local = &mut *x;
            *local = local.wrapping_add(1);
        } else {
            let local = &mut *y;
            *local = local.wrapping_add(2);
        }
        *x = x.wrapping_add(*y);
    }
    pub fn compile(x: &super::validator::Token) -> Compiler {
        let mut c = Compiler { sum: 0 };
        super::validator::validate(&mut c, x);
        c
    }
}
