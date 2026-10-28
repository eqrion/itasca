import Exec.Code.Body.Relations.Common.EntryCompilerInitial
import Itasca.Module.Code.ReachedEntry
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Entry framing and captured signature lookup justify every unchecked
operation in the fresh function-start callback, including rejected allocation. -/
theorem prepared_compiler_start_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial : runtime.compiler.FunctionCompiler A} {data env index start profile}
    (w : CodeEntry.Prepared data env index start profile)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (endFits : batchStart.val + w.finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish ⦃ _ => True ⦄ := by
  have sourceLookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  obtain ⟨signature,lookup,_⟩ := signatureTable.lookup_source sourceLookup
  have fresh := compiler_new ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at fresh
  obtain ⟨layout,locals,operands,controls,frames,code,reachable,sigs,slots,batch⟩ := fresh
  apply WP.spec_mono (compiler_function_start ops law initial w.ctx w.typeIdx signature
    w.bodyStart w.finish (by simpa only [sigs] using lookup)
    (by rw [batch]; have length := w.body_bytes.length; omega)
    (by simpa only [batch] using endFits) locals layout operands
    (by simp only [controls,List.length_nil]; scalar_tac)
    (by simp only [frames,List.length_nil]; scalar_tac))
  intros
  trivial

end Itasca.Runtime.Code
