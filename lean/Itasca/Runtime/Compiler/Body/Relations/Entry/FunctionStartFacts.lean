import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEnvironment
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEntry
import Itasca.Runtime.Compiler.Local.Relations.Table.SignatureTable
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallLowering

/-!
Fixed metadata and local layout obtained from actual construction and the successful function-start callback. These are static premises of the body fold.

Main declarations: `compiler_function_start_facts` and `function_body_coordinate_bound`. A direct consumer is `Compiler.Body.Relations.Entry.EntryCompilerInitial`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Fixed metadata and local layout obtained from actual construction and the
successful function-start callback. These are static premises of the body fold. -/
theorem compiler_function_start_facts {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (budget : runtime.compiler.Budget A) (batchStart : Usize)
    (initial started : runtime.compiler.FunctionCompiler A)
    (ctx : code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize)
    (lookup : signatures.val[typeIndex.val]? = some signature)
    (beginFits : batchStart.val + bodyBegin.val ≤ Usize.max)
    (endFits : batchStart.val + bodyEnd.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial ctx typeIndex bodyBegin bodyEnd = .ok (.Ok (), started)) :
    LocalLayout started ∧ started.function.locals = ctx.locals ∧
      started.function.slot_count = started.function.local_slots ∧
      started.function.param_slots = signature.param_slots ∧
      started.function.type_index = typeIndex ∧
      started.function.body_start.val = batchStart.val + bodyBegin.val ∧
      started.function.body_end.val = batchStart.val + bodyEnd.val ∧
      started.signatures = signatures ∧ started.func_param_slots = functionSlots ∧
      started.batch_start = batchStart := by
  have newPost := compiler_new ops signatures functionSlots budget batchStart
  rw [created, WP.spec_ok] at newPost
  obtain ⟨localLayout, emptyLocals, emptyOperands, emptyMaps, emptyFrames, _, _,
    sigs, functionWidths, coordinate⟩ := newPost
  have startPost := compiler_function_start ops law initial ctx typeIndex signature bodyBegin bodyEnd
    (by simpa only [sigs] using lookup) (by simpa only [coordinate] using beginFits)
    (by simpa only [coordinate] using endFits) emptyLocals localLayout emptyOperands
    (by simp [emptyMaps]; scalar_tac) (by simp [emptyFrames]; scalar_tac)
  rw [accepted, WP.spec_ok] at startPost
  obtain ⟨layout, _, capacity, localTypes, params, typeIdx, start, finish, _, _, _⟩ := startPost rfl
  have environment := compiler_function_start_environment_frame ops law initial started ctx typeIndex bodyBegin bodyEnd
    (.Ok ()) accepted
  have fields : started.signatures = initial.signatures ∧
      started.func_param_slots = initial.func_param_slots ∧ started.batch_start = initial.batch_start := by
    simpa only [FunctionEnvironment, Prod.mk.injEq] using environment
  refine ⟨⟨layout.localSlots, layout.localOffsets⟩, ?_, capacity, params, typeIdx,
    ?_, ?_, fields.1.trans sigs, fields.2.1.trans functionWidths, fields.2.2.trans coordinate⟩
  · exact alloc.vec.Vec.ext _ _ localTypes
  · simpa only [coordinate] using start
  · simpa only [coordinate] using finish

/-- The exact byte span from the accepted entry bounds every body-relative
source coordinate after rebasing it to the module origin. -/
theorem function_body_coordinate_bound {A : Type}
    {compiler : runtime.compiler.FunctionCompiler A} {data body : Slice U8}
    {bodyBegin bodyEnd batchStart : Usize}
    (span : Wasm1.BytesAt data bodyBegin body.val bodyEnd)
    (start : compiler.function.body_start.val = batchStart.val + bodyBegin.val)
    (endFits : batchStart.val + bodyEnd.val ≤ Usize.max) :
    compiler.function.body_start.val + body.length ≤ Usize.max := by
  have length := span.length
  change bodyEnd.val = bodyBegin.val + body.length at length
  omega
end Itasca.Runtime.Code
