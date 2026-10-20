import Exec.Code.Body.Reader.Memory.ReaderMemoryAcceptance
import Exec.Code.Body.Reader.Memory.ReaderMemoryTypes
import Exec.Code.Body.Reader.Acceptance.ReaderProfileAcceptance

namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Independent Wasm 1 memory-reader acceptance determines the live
address/value layout, before any compiler callback is run. -/
theorem reached_reader_memory_load_available_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (demand : CallbackDemand compiler out bound) (op : Abs.Memory.Load)
    (capacity : st.vals.val.length < Usize.max)
    (known : compiler.reachable = true → ConcreteStack st.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (reference : code.step source st data env ctx (UScalar.cast .U8 (memoryLoadOpcode op)) before =
      .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryLoadOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · have facts := memory_load_reader_facts ops compiler out op ⟨0#u32,0#u32⟩
    obtain ⟨arg,rest,callback,read,post⟩ := reader_memory_wasm1 p source before after out _
      (memoryLoadMeaning op) byte facts.1 reference
    simp only [memoryReader,facts.2.1,Bool.false_eq_true,↓reduceIte,facts.2.2.1] at read
    obtain ⟨C,outer,spine,header,base,typed,controls,values⟩ := p.opened
    have currentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (values ▸ known live)).2
    have poly : Control.polymorphic st = false := by
      simpa [Control.polymorphic,controls] using monomorphic live
    have baseEq : (Control.base st).val = outer.length := by simpa [Control.base,controls] using base
    obtain ⟨rest,shape,stack,_,_⟩ := reader_memory_load_stack st out data env _ _ arg outer p.current.vals
      values baseEq poly currentKnown capacity read
    obtain ⟨front,_,oldTypes,_⟩ := memory_load_stack_types (known live) values shape stack
    have layout := wholeLayout live
    rw [oldTypes] at layout
    exact compiler_reader_memory_load_available ops bound available source before after compiler st out
      data env ctx demand front op (fun _ => layout) reference
  · exact compiler_reader_memory_load_available ops bound available source before after compiler st out
      data env ctx demand [] op (fun impossible => False.elim (live impossible)) reference

/-- Independent Wasm 1 memory-reader acceptance determines the live
address/value layout, before any compiler callback is run. -/
theorem reached_reader_memory_store_available_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (demand : CallbackDemand compiler out bound) (op : Abs.Memory.Store)
    (capacity : st.vals.val.length < Usize.max)
    (known : compiler.reachable = true → ConcreteStack st.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (reference : code.step source st data env ctx (UScalar.cast .U8 (memoryStoreOpcode op)) before =
      .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryStoreOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · have facts := memory_store_reader_facts ops compiler out op ⟨0#u32,0#u32⟩
    obtain ⟨arg,rest,callback,read,post⟩ := reader_memory_wasm1 p source before after out _
      (memoryStoreMeaning op) byte facts.1 reference
    simp only [memoryReader,facts.2.1,↓reduceIte,facts.2.2.1] at read
    obtain ⟨C,outer,spine,header,base,typed,controls,values⟩ := p.opened
    have currentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (values ▸ known live)).2
    have poly : Control.polymorphic st = false := by
      simpa [Control.polymorphic,controls] using monomorphic live
    have baseEq : (Control.base st).val = outer.length := by simpa [Control.base,controls] using base
    obtain ⟨rest,shape,stack,_,_⟩ := reader_memory_store_stack st out data env _ _ arg outer p.current.vals
      values baseEq poly currentKnown read
    obtain ⟨front,_,oldTypes,_⟩ := memory_store_stack_types (known live) values shape stack
    simp only [memoryRawType_translate] at oldTypes
    have layout := wholeLayout live
    rw [oldTypes] at layout
    exact compiler_reader_memory_store_available ops bound available source before after compiler st out
      data env ctx demand front op (fun _ => layout) reference
  · exact compiler_reader_memory_store_available ops bound available source before after compiler st out
      data env ctx demand [] op (fun impossible => False.elim (live impossible)) reference

/-- Independent Wasm 2 memory-reader acceptance determines the live
address/value layout, before any compiler callback is run. -/
theorem reached_reader_memory_load_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (demand : CallbackDemand compiler out bound) (op : Abs.Memory.Load)
    (capacity : st.core.vals.val.length < Usize.max)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (reference : code.step source st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (memoryLoadOpcode op)) before =
      .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (memoryLoadOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · have facts := memory_load_reader_facts ops compiler out op ⟨0#u32,0#u32⟩
    obtain ⟨arg,rest,callback,read,post⟩ := reader_memory_wasm2 p source before after out _
      (memoryLoadMeaning op) capacity byte facts.1 reference
    simp only [memoryReader,facts.2.1,Bool.false_eq_true,↓reduceIte,facts.2.2.1] at read
    obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
    have currentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (values ▸ known live)).2
    have poly : Control.polymorphic st.core = false := by
      simpa [Control.polymorphic,controls] using monomorphic live
    have baseEq : (Control.base st.core).val = outer.length := by simpa [Control.base,controls] using base
    obtain ⟨rest,shape,stack,_,_⟩ := reader_memory_load_stack st.core out data env _ _ arg outer p.current.vals
      values baseEq poly currentKnown capacity read
    obtain ⟨front,_,oldTypes,_⟩ := memory_load_stack_types (known live) values shape stack
    have layout := wholeLayout live
    rw [oldTypes] at layout
    exact compiler_reader_memory_load_available ops bound available source before after compiler st.core out
      data env ⟨locals,p.ft.results⟩ demand front op (fun _ => layout) reference
  · exact compiler_reader_memory_load_available ops bound available source before after compiler st.core out
      data env ⟨locals,p.ft.results⟩ demand [] op (fun impossible => False.elim (live impossible)) reference

/-- Independent Wasm 2 memory-reader acceptance determines the live
address/value layout, before any compiler callback is run. -/
theorem reached_reader_memory_store_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (demand : CallbackDemand compiler out bound) (op : Abs.Memory.Store)
    (capacity : st.core.vals.val.length < Usize.max)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (reference : code.step source st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (memoryStoreOpcode op)) before =
      .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (memoryStoreOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · have facts := memory_store_reader_facts ops compiler out op ⟨0#u32,0#u32⟩
    obtain ⟨arg,rest,callback,read,post⟩ := reader_memory_wasm2 p source before after out _
      (memoryStoreMeaning op) capacity byte facts.1 reference
    simp only [memoryReader,facts.2.1,↓reduceIte,facts.2.2.1] at read
    obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
    have currentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (values ▸ known live)).2
    have poly : Control.polymorphic st.core = false := by
      simpa [Control.polymorphic,controls] using monomorphic live
    have baseEq : (Control.base st.core).val = outer.length := by simpa [Control.base,controls] using base
    obtain ⟨rest,shape,stack,_,_⟩ := reader_memory_store_stack st.core out data env _ _ arg outer p.current.vals
      values baseEq poly currentKnown read
    obtain ⟨front,_,oldTypes,_⟩ := memory_store_stack_types (known live) values shape stack
    simp only [memoryRawType_translate] at oldTypes
    have layout := wholeLayout live
    rw [oldTypes] at layout
    exact compiler_reader_memory_store_available ops bound available source before after compiler st.core out
      data env ⟨locals,p.ft.results⟩ demand front op (fun _ => layout) reference
  · exact compiler_reader_memory_store_available ops bound available source before after compiler st.core out
      data env ⟨locals,p.ft.results⟩ demand [] op (fun impossible => False.elim (live impossible)) reference

/-- The complete Wasm 2 dispatcher accepts a reached scalar or packed
load; the source run supplies its real capacity check. -/
theorem reached_profile_memory_load_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (demand : CallbackDemand compiler out.core bound) (op : Abs.Memory.Load)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (reference : code.step_profile source st data env ctx index .Wasm2
      (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryLoadOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨_,_,_,_,_,ordinary,plain,sign,misc⟩ := memory_load_reader_facts ops compiler out.core op ⟨0#u32,0#u32⟩
  obtain ⟨capacity,raw⟩ := profile_base_success_wasm2 source st out data env ctx ⟨locals,p.ft.results⟩
    index _ before after ordinary plain sign misc contextLocals reference
  exact profile_base_available_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out.core data env ctx ⟨locals,p.ft.results⟩ index _ compiler
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0))
    capacity ordinary plain sign misc contextLocals
    (reached_reader_memory_load_available_wasm2 p ops bound available source before after compiler out.core demand
      op capacity known monomorphic wholeLayout byte raw)

/-- The complete Wasm 2 dispatcher accepts a reached scalar or packed
store; the source run supplies its real capacity check. -/
theorem reached_profile_memory_store_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (demand : CallbackDemand compiler out.core bound) (op : Abs.Memory.Store)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (reference : code.step_profile source st data env ctx index .Wasm2
      (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryStoreOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨_,_,_,_,_,ordinary,plain,sign,misc⟩ := memory_store_reader_facts ops compiler out.core op ⟨0#u32,0#u32⟩
  obtain ⟨capacity,raw⟩ := profile_base_success_wasm2 source st out data env ctx ⟨locals,p.ft.results⟩
    index _ before after ordinary plain sign misc contextLocals reference
  exact profile_base_available_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out.core data env ctx ⟨locals,p.ft.results⟩ index _ compiler
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0))
    capacity ordinary plain sign misc contextLocals
    (reached_reader_memory_store_available_wasm2 p ops bound available source before after compiler out.core demand
      op capacity known monomorphic wholeLayout byte raw)

end Exec.Code
