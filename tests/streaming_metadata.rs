use itasca::*;
use std::sync::Arc;
use std::thread::{scope, Scope, ScopedJoinHandle};

struct Source<'a> {
    code: &'a [u8],
    tail: &'a [u8],
}

impl StreamingSource for Source<'_> {
    fn environment(&self) -> Result<&[u8]> {
        // Two definitions share the empty signature.
        Ok(b"\0asm\x01\0\0\0\x01\x04\x01\x60\0\0\x03\x03\x02\0\0")
    }
    fn code_len(&self) -> usize {
        self.code.len()
    }
    fn code(&self, start: usize, end: usize) -> Result<&[u8]> {
        self.code.get(start..end).ok_or(Error::Host)
    }
    fn tail(&self) -> Result<&[u8]> {
        Ok(self.tail)
    }
}

struct Workers<'scope, 'env, 'data> {
    scope: &'scope Scope<'scope, 'env>,
    pending: Vec<ScopedJoinHandle<'scope, StreamingBatch<'data>>>,
    code: Option<Arc<CodeMetadata>>,
}

impl ModuleVisitor for Workers<'_, '_, '_> {}
impl<'scope, 'data: 'scope> StreamingVisitor<'data> for Workers<'scope, '_, 'data> {
    fn custom_region(&mut self, _region: StreamingRegion) {}
    fn environment_ready(&mut self, module: &ModuleMetadata) -> Result<StreamingConfig> {
        self.code = Some(Arc::clone(module.code()));
        Ok(StreamingConfig {
            batch_bytes: 1,
            max_batches: 2,
        })
    }
    fn submit_code_batch(&mut self, mut batch: StreamingBatch<'data>) -> Result<()> {
        assert!(std::ptr::eq(
            batch.code_metadata(),
            self.code.as_deref().unwrap()
        ));
        self.pending.push(self.scope.spawn(move || {
            assert_eq!(batch.code_metadata().num_func_defs(), 2);
            let entry = batch.next_entry().unwrap();
            // The batch records validation failure for the driver.
            let _ = batch.validate_func(entry.index, &mut DefaultOpVisitor);
            batch
        }));
        Ok(())
    }
    fn poll_code_batch(&mut self) -> Result<StreamingBatch<'data>> {
        // Return the second batch first.
        self.pending
            .pop()
            .ok_or(Error::Host)?
            .join()
            .map_err(|_| Error::Host)
    }
    fn code_end(&mut self) -> Result<()> {
        assert_eq!(self.pending.len(), 2);
        Ok(())
    }
}

#[test]
fn driver_collects_validated_batches_and_rejects_worker_errors() {
    let mut source = Source {
        code: b"\x0a\x07\x02\x02\0\x0b\x02\0\x0b",
        tail: b"\x0b\x04\x01\x01\x01x",
    };
    scope(|scope| {
        let mut visitor = Workers {
            scope,
            pending: Vec::new(),
            code: None,
        };
        let module = validate_streaming(0, &source, &mut visitor).unwrap();
        assert_eq!(module.data()[0].init, b"x");
        assert!(Arc::ptr_eq(module.code(), visitor.code.as_ref().unwrap()));
        drop(module);
        assert_eq!(visitor.code.unwrap().num_func_defs(), 2);
    });
    source.code = b"\x0a\x07\x02\x02\0\x0b\x02\0\xff";
    scope(|scope| {
        let mut visitor = Workers {
            scope,
            pending: Vec::new(),
            code: None,
        };
        assert!(matches!(
            validate_streaming(1, &source, &mut visitor),
            Err(Error::Body(_))
        ));
    });
}

#[test]
fn outstanding_batches_own_metadata_after_tail_error() {
    let source = Source {
        code: b"\x0a\x07\x02\x02\0\x0b\x02\0\x0b",
        tail: b"\x0b\x01\x01",
    };
    scope(|scope| {
        let mut visitor = Workers {
            scope,
            pending: Vec::new(),
            code: None,
        };
        assert!(validate_streaming(2, &source, &mut visitor).is_err());
        let weak = Arc::downgrade(&visitor.code.take().unwrap());
        assert_eq!(visitor.pending.len(), 2);
        for handle in visitor.pending {
            let batch = handle.join().unwrap();
            assert_eq!(batch.code_metadata().num_func_defs(), 2);
            assert!(weak.upgrade().is_some());
        }
        assert!(weak.upgrade().is_none());
    });
}

#[test]
fn retained_metadata_preserves_wasm_index_spaces() {
    let input = wast::parser::ParseBuffer::new(
        r#"(module
        (import "m" "f" (func (param i32)))
        (import "m" "g" (global i64))
        (import "m" "h" (func (result f32)))
        (func $start)
        (func $ex (export "a") (export "b"))
        (start $start)
        (table 1 funcref)
        (elem declare func $ex)
        (global i64 (global.get 0))
        (data "xyz"))"#,
    )
    .unwrap();
    let bytes = wast::parser::parse::<wast::Wat>(&input)
        .unwrap()
        .encode()
        .unwrap();
    let module = validate_module(&bytes).unwrap();
    let code = module.code();
    assert_eq!(code.num_imported_funcs(), 2);
    assert_eq!(code.num_func_defs(), 2);
    assert_eq!(code.func_type(0).unwrap().params, [ValueType::I32]);
    assert_eq!(code.func_type(1).unwrap().results, [ValueType::F32]);
    assert_eq!(code.start(), Some(2));
    assert!(code.funcs()[2].eager);
    assert!(!code.declares_function(2));
    assert!(code.declares_function(3));
    let imports = module.import_types().unwrap();
    assert!(matches!(
        imports.as_slice(),
        [
            ExternType::Func(_),
            ExternType::Global(_),
            ExternType::Func(_)
        ]
    ));
    assert_eq!(module.export_types().unwrap().len(), 2);
    assert_eq!(code.globals()[0].init, None);
    assert_eq!(code.globals()[1].init, Some(ConstExpr::GlobalGet(0)));
    assert_eq!(code.elem_segment_types(), &[module.elements()[0].elem]);
    assert_eq!(module.elements()[0].init, ElementInit::Functions(vec![3]));
    assert_eq!(module.data()[0].init, b"xyz");
}
