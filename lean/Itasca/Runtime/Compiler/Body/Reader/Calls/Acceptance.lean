import Itasca.Wasm2.Trace.Acceptance
import Itasca.Visitor.ReaderAcceptance
import Itasca.Runtime.Compiler.Local.Capacity.CallAvailability
import Itasca.Runtime.Compiler.Local.Capacity.DeadOpAvailability
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallLowering
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Body.Relations.Calls.IndirectCalls
import Itasca.Runtime.Compiler.Body.Relations.Entry.EntrySignatures

/-!
Successful direct and indirect call replay from reached source prefixes and allocator availability. These acceptance directions complement inverse accepted-step facts.
-/

/-! ## Reached Call Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Independently accepted Wasm 2 calls determine their source parameter
signature and live layout. Captured scheduler metadata then justifies actual
compiler call acceptance and its single instruction charge. -/
theorem reached_profile_call_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (demand : CallbackDemand compiler out.core bound) (metadata : FunctionParameterSlots compiler env)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = 16#u8)
    (reference : code.step_profile source st data env ctx index .Wasm2 16#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 16#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨callee,_,_,read,_⟩ := reader_call_wasm2 p source before after out ctx byte reference
  have callback : (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_call compiler out.core callee ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change runtime.compiler.lower.FunctionCompiler.op ops compiler out.core 16#u16 callee 0#u32 0#u128 ⦃ _ ⦄
    by_cases live : compiler.reachable = true
    · obtain ⟨_,outer,_,_,base,_,controls,_,values⟩ := p.opened
      obtain ⟨ft,rest,found,afterValues,transfer⟩ := reader_call_info_effect st out data env callee outer p.current.vals values
        (by simpa [Control.base,controls] using base) read
      have poly : Control.polymorphic st.core = false := by simpa [Control.polymorphic,controls] using monomorphic live
      rw [poly] at transfer
      obtain ⟨front,beforeTypes,_⟩ := call_full_stack_types ft.params.val ft.results.val (known live) values afterValues transfer
      obtain ⟨parameterSlots,lookup,width⟩ := metadata.lookup callee ft found
      have layout := wholeLayout live
      rw [beforeTypes] at layout
      exact compiler_call_available ops bound available compiler out.core demand (front.map Translate.valueType)
        (ft.params.val.map Translate.valueType) callee parameterSlots (fun _ => layout) (fun _ => lookup) width
    · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler out.core 16#u16 callee 0#u32
        0#u128 live demand.operands demand.slots)
      intro result held
      rw [held.2]
      exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
  rw [Wasm2.CallbackTrace.dispatch_call]
  exact Wasm2.CallbackTrace.bodyRun.available_of_read _
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) .call compiler callee out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) read callback

end Itasca.Runtime.Compiler

end

/-! ## Reached Indirect Call Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Independent Wasm 2 indirect-call validation determines both source
indices and the full live parameter/selector layout. Captured signatures and
bounded pair storage then establish actual compiler acceptance. -/
theorem reached_profile_indirect_call_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (demand : CallbackDemand compiler out.core bound)
    (signatures : SignatureSequence compiler.signatures.val env.types.val)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (pairs : compiler.function.indirect.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (reference : code.step_profile source st data env ctx index .Wasm2 17#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 17#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨callee,table,_,_,read,_⟩ := reader_indirect_call_wasm2 p source before after out ctx byte reference
  have callback : (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_call_indirect
      compiler out.core callee table ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change runtime.compiler.lower.FunctionCompiler.op ops compiler out.core 17#u16 callee table 0#u128 ⦃ _ ⦄
    by_cases live : compiler.reachable = true
    · obtain ⟨_,outer,_,_,base,_,controls,_,values⟩ := p.opened
      have poly : Control.polymorphic st.core = false := by simpa [Control.polymorphic,controls] using monomorphic live
      obtain ⟨ft,_,front,typeFound,_,_,beforeTypes,_⟩ := reader_indirect_call_stack_wasm2 st out data env callee table
        outer p.current.vals values (by simpa [Control.base,controls] using base) (known live) poly p.opened.shape.core read
      obtain ⟨signature,selected,matched⟩ := signatures.select (bt := .TypeIndex callee) (ins := ft.params.val) (outs := ft.results.val)
        (by simp [Wasm2.inputs,Wasm2.resolve,typeFound]) (by simp [Wasm2.outputs,Wasm2.resolve,typeFound])
      have found : compiler.signatures.val[callee.val]? = some signature := by
        cases selected with
        | index _ _ found => exact found
      have layout := wholeLayout live
      rw [beforeTypes] at layout
      have pc := demand.pc
      have capacity := demand.codeCapacity
      have reserve := demand.codeReserve
      simp only [alloc.vec.Vec.length] at pairs pc capacity reserve
      exact compiler_indirect_call_available ops bound available compiler out.core demand (front.map Translate.valueType)
        (ft.params.val.map Translate.valueType) callee table signature (fun _ => layout) (fun _ => found)
        matched.paramWords
        (by change compiler.function.indirect.val.length ≤ U32.max; omega)
        (by change compiler.function.indirect.val.length < Usize.max; omega)
        (by change compiler.function.indirect.val.length+1 ≤ bound; omega)
    · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler out.core 17#u16 callee table
        0#u128 live demand.operands demand.slots)
      intro result held
      rw [held.2]
      exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
  rw [Wasm2.CallbackTrace.dispatch_call_indirect]
  exact Wasm2.CallbackTrace.bodyRun.available_of_read _
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) (fun arg : U32 × U32 => .call_indirect arg.1 arg.2)
    compiler (callee,table) out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) read callback

end Itasca.Runtime.Compiler

end
