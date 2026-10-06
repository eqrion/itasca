// Aeneas Lean output should keep namespace references distinct from fields.
pub mod types {
    pub struct FuncType {
        pub result: u32,
    }
}

pub mod module {
    pub struct ImportDesc {
        pub index: u32,
    }

    pub struct Import {
        pub module: Vec<u8>,
        pub desc: ImportDesc,
    }

    pub struct Env {
        pub types: Vec<super::types::FuncType>,
        pub func_types: Vec<super::types::FuncType>,
    }
}
