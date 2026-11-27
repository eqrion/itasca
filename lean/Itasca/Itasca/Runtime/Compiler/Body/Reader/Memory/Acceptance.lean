import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Runtime.Compiler.Body.Relations.CallbackReadiness
import Itasca.Runtime.Compiler.Local.Relations.Memory.MemorySafety
import Itasca.Runtime.Compiler.Body.Reader.Memory.MemoryEmissions
import Itasca.Body.Scalar.Env
import Itasca.Visitor.BodyReplay
import Itasca.Runtime.Compiler.Local.Capacity.CallbackBudgets
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.ReachedReferenceDemand

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Memory.

This module collects MemorySafety, Acceptance.
Each section documents its contracts and consumers.
-/

/-! ## MemorySafety -/

section

/-!
Normal return of scalar memory reader callbacks.

Main declarations: `compiler_reader_memory_load_total` and `compiler_reader_memory_store_total`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_reader_memory_load_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (op : SourceMachine.Memory.Load) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryLoadOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  have facts := memory_load_reader_facts ops compiler st op ⟨0#u32,0#u32⟩
  rw [code.step_memory.dispatch _ st data env ctx compiler _ _ facts.1, facts.2.1]
  simp only [Bool.false_eq_true,↓reduceIte]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.ScalarReaders.load st data env _ _ shape capacity) (by simp)
  · intro state arg read
    rw [(memory_load_reader_facts ops compiler state op arg).2.2.2.2.1]
    exact compiler_memory_load_total ops law compiler state op arg.offset arg.align
      ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_memory_store_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Body.Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (op : SourceMachine.Memory.Store) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryStoreOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  have facts := memory_store_reader_facts ops compiler st op ⟨0#u32,0#u32⟩
  rw [code.step_memory.dispatch _ st data env ctx compiler _ _ facts.1, facts.2.1]
  simp only [↓reduceIte]
  refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
  · exact WP.spec_mono (Body.ScalarReaders.store st data env _ _ shape capacity) (by simp)
  · intro state arg read
    rw [(memory_store_reader_facts ops compiler state op arg).2.2.2.2.1]
    exact compiler_memory_store_total ops law compiler state op arg.offset arg.align
      ready.codeFits ready.sourceFits ready.coordinateFits

end Itasca.Compiler

end

/-! ## Acceptance -/

section

/-!
Memory callback acceptance and successful replay from reached source prefixes and available resources.
-/

/-! ## Reader Memory Acceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Every scalar and packed load replays the independent reader result
and accepts with at most one instruction charge, including dead code. -/
theorem compiler_reader_memory_load_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound) (front : List valtype)
    (op : SourceMachine.Memory.Load)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ [.I32]))
    (reference : code.step source st data env ctx (UScalar.cast .U8 (memoryLoadOpcode op)) before =
      .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryLoadOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = final ∧ CompilationBudgetEffect compiler.budget out.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have facts := memory_load_reader_facts ops compiler st op ⟨0#u32,0#u32⟩
  rw [code.step_memory.dispatch _ st data env ctx before _ _ facts.1,facts.2.1] at reference
  rw [code.step_memory.dispatch _ st data env ctx compiler _ _ facts.1,facts.2.1]
  simp only [Bool.false_eq_true,↓reduceIte] at reference ⊢
  refine Visitor.Core.run.accepted_lift_on (code.read_load st data env _ _)
    (fun v state arg => code.visit_memory source v state (UScalar.cast .U8 (memoryLoadOpcode op)) arg)
    (fun v state arg => code.visit_memory (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      v state (UScalar.cast .U8 (memoryLoadOpcode op)) arg) before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro arg _ _
  rw [(memory_load_reader_facts ops compiler final op arg).2.2.2.2.1]
  exact compiler_memory_load_available ops bound available compiler final demand front op arg.offset arg.align layout

/-- Every scalar and packed store replays the independent reader result
and accepts with at most one instruction charge, including dead code. -/
theorem compiler_reader_memory_store_available {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (st final : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (demand : CallbackDemand compiler final bound) (front : List valtype)
    (op : SourceMachine.Memory.Store)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ [.I32,valtype_numtype op.type]))
    (reference : code.step source st data env ctx (UScalar.cast .U8 (memoryStoreOpcode op)) before =
      .ok (.Ok (),final,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryStoreOpcode op)) compiler ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = final ∧ CompilationBudgetEffect compiler.budget out.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have facts := memory_store_reader_facts ops compiler st op ⟨0#u32,0#u32⟩
  rw [code.step_memory.dispatch _ st data env ctx before _ _ facts.1,facts.2.1] at reference
  rw [code.step_memory.dispatch _ st data env ctx compiler _ _ facts.1,facts.2.1]
  simp only [↓reduceIte] at reference ⊢
  refine Visitor.Core.run.accepted_lift_on (code.read_store st data env _ _)
    (fun v state arg => code.visit_memory source v state (UScalar.cast .U8 (memoryStoreOpcode op)) arg)
    (fun v state arg => code.visit_memory (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      v state (UScalar.cast .U8 (memoryStoreOpcode op)) arg) before after compiler final
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro arg _ _
  rw [(memory_store_reader_facts ops compiler final op arg).2.2.2.2.1]
  exact compiler_memory_store_available ops bound available compiler final demand front op arg.offset arg.align layout

end Itasca.Compiler

end

/-! ## Reached Memory Acceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Independent Wasm 2 memory-reader acceptance determines the live
address/value layout, before any compiler callback is run. -/
theorem reached_reader_memory_load_available {data env locals index st}
    (p : Body.Pending data env locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (demand : CallbackDemand compiler out bound) (op : SourceMachine.Memory.Load)
    (capacity : st.core.vals.val.length < Usize.max)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Body.Stack.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (reference : code.step source st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (memoryLoadOpcode op)) before =
      .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (memoryLoadOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · have facts := memory_load_reader_facts ops compiler out op ⟨0#u32,0#u32⟩
    obtain ⟨arg,rest,callback,read,post⟩ := reader_memory p source before after out _
      (memoryLoadMeaning op) capacity byte facts.1 reference
    simp only [memoryReader,facts.2.1,Bool.false_eq_true,↓reduceIte,facts.2.2.1] at read
    obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
    have currentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (values ▸ known live)).2
    have poly : Body.Control.polymorphic st.core = false := by
      simpa [Body.Control.polymorphic,controls] using monomorphic live
    have baseEq : (Body.Control.base st.core).val = outer.length := by simpa [Body.Control.base,controls] using base
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
theorem reached_reader_memory_store_available {data env locals index st}
    (p : Body.Pending data env locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (demand : CallbackDemand compiler out bound) (op : SourceMachine.Memory.Store)
    (capacity : st.core.vals.val.length < Usize.max)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Body.Stack.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (reference : code.step source st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (memoryStoreOpcode op)) before =
      .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st.core data env ⟨locals,p.ft.results⟩ (UScalar.cast .U8 (memoryStoreOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · have facts := memory_store_reader_facts ops compiler out op ⟨0#u32,0#u32⟩
    obtain ⟨arg,rest,callback,read,post⟩ := reader_memory p source before after out _
      (memoryStoreMeaning op) capacity byte facts.1 reference
    simp only [memoryReader,facts.2.1,↓reduceIte,facts.2.2.1] at read
    obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
    have currentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (values ▸ known live)).2
    have poly : Body.Control.polymorphic st.core = false := by
      simpa [Body.Control.polymorphic,controls] using monomorphic live
    have baseEq : (Body.Control.base st.core).val = outer.length := by simpa [Body.Control.base,controls] using base
    obtain ⟨rest,shape,stack,_,_⟩ := reader_memory_store_stack st.core out data env _ _ arg outer p.current.vals
      values baseEq poly currentKnown read
    obtain ⟨front,_,oldTypes,_⟩ := memory_store_stack_types (known live) values shape stack
    simp only [memory_raw_type_translate] at oldTypes
    have layout := wholeLayout live
    rw [oldTypes] at layout
    exact compiler_reader_memory_store_available ops bound available source before after compiler st.core out
      data env ⟨locals,p.ft.results⟩ demand front op (fun _ => layout) reference
  · exact compiler_reader_memory_store_available ops bound available source before after compiler st.core out
      data env ⟨locals,p.ft.results⟩ demand [] op (fun impossible => False.elim (live impossible)) reference

/-- The complete Wasm 2 dispatcher accepts a reached scalar or packed
load; the source run supplies its real capacity check. -/
theorem reached_memory_load_available {data env locals index st}
    (p : Body.Pending data env locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (demand : CallbackDemand compiler out.core bound) (op : SourceMachine.Memory.Load)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Body.Stack.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (reference : code.step_body source st data env ctx index
      (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (memoryLoadOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨_,_,_,_,_,ordinary,plain,sign,misc⟩ := memory_load_reader_facts ops compiler out.core op ⟨0#u32,0#u32⟩
  obtain ⟨capacity,raw⟩ := base_success source st out data env ctx ⟨locals,p.ft.results⟩
    index _ before after ordinary plain sign misc contextLocals reference
  exact base_available (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out.core data env ctx ⟨locals,p.ft.results⟩ index _ compiler
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0))
    capacity ordinary plain sign misc contextLocals
    (reached_reader_memory_load_available p ops bound available source before after compiler out.core demand
      op capacity known monomorphic wholeLayout byte raw)

/-- The complete Wasm 2 dispatcher accepts a reached scalar or packed
store; the source run supplies its real capacity check. -/
theorem reached_memory_store_available {data env locals index st}
    (p : Body.Pending data env locals index st) {A V : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = locals)
    (demand : CallbackDemand compiler out.core bound) (op : SourceMachine.Memory.Store)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Body.Stack.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (reference : code.step_body source st data env ctx index
      (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index (UScalar.cast .U8 (memoryStoreOpcode op)) compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨_,_,_,_,_,ordinary,plain,sign,misc⟩ := memory_store_reader_facts ops compiler out.core op ⟨0#u32,0#u32⟩
  obtain ⟨capacity,raw⟩ := base_success source st out data env ctx ⟨locals,p.ft.results⟩
    index _ before after ordinary plain sign misc contextLocals reference
  exact base_available (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out.core data env ctx ⟨locals,p.ft.results⟩ index _ compiler
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0))
    capacity ordinary plain sign misc contextLocals
    (reached_reader_memory_store_available p ops bound available source before after compiler out.core demand
      op capacity known monomorphic wholeLayout byte raw)

end Itasca.Compiler

end

end
