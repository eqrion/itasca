import Itasca.Runtime.Compiler.Body.Relations.Entry.PreparedCompilerStart
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionStartRaw
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackSafety
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget

/-!
Fresh entry establishes the raw operand and auxiliary-buffer ledger before any body byte is read. This includes bottom-capable observations used later.

Main declarations: `prepared_compiler_raw_initial`. A direct consumer is `Compiler.Module.PreparedExecutableSafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Fresh entry establishes the raw operand and auxiliary-buffer ledger before
any body byte is read. This includes bottom-capable observations used later. -/
theorem prepared_compiler_raw_initial {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start profile}
    (w : CodeEntry.Prepared data env index start profile)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (endFits : batchStart.val + w.finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (startedCall : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started)) :
    ObservedStack started [] ∧
    started.function.indirect.val.length ≤ started.function.code.val.length ∧
    started.function.simd.val.length ≤ started.function.code.val.length ∧
    started.function.v128_pool.val.length ≤ started.function.code.val.length ∧
    FixupBudget started.frames.val started.function.code.val.length := by
  have sourceLookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  obtain ⟨signature,lookup,_⟩ := signatureTable.lookup_source sourceLookup
  have fresh := compiler_new ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at fresh
  obtain ⟨localLayout,locals,operands,controls,frames,code,reachable,sigs,slots,batch⟩ := fresh
  have post := compiler_function_start_raw ops law initial w.ctx w.typeIdx signature w.bodyStart w.finish
    (by simpa only [sigs] using lookup)
    (by rw [batch]; have length := w.body_bytes.length; omega)
    (by simpa only [batch] using endFits) locals localLayout operands
    (by simp only [controls,List.length_nil]; scalar_tac)
    (by simp only [frames,List.length_nil]; scalar_tac)
  rw [startedCall,WP.spec_ok] at post
  obtain ⟨layout,codeEq,framesEq,tablesEq⟩ := post rfl
  have initialTables : CompilerTables.ofFunction initial.function = .empty := by
    simp only [runtime.compiler.FunctionCompiler.new,Result.ok.injEq] at created
    subst initial
    rfl
  have tables := tablesEq.trans initialTables
  have tableCounts := congrArg (fun t : CompilerTables =>
    (t.indirect.length,t.simd.length,t.constants.length)) tables
  simp only [CompilerTables.ofFunction,CompilerTables.empty,List.length_nil,Prod.mk.injEq] at tableCounts
  refine ⟨⟨?_,?_⟩,by omega,by omega,by omega,?_⟩
  · simpa only [stackOffsets,List.length_nil,List.range_zero,List.map_nil,observedOffsets]
      using layout.operandOffsets
  · simpa [layout.localSlots,stackWords,Compiler.slots] using layout.height
  · simp [FixupBudget,framesEq,frames,alloc.vec.Vec.new]
end Itasca.Runtime.Compiler
