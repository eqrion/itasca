import Itasca.Runtime.Code.Body.Reader.Control.StructuredElseExitSlots
import Itasca.Runtime.Code.Body.Reader.Common.ReaderCloseWasm2
import Itasca.Runtime.Code.Body.Reader.Control.ReaderScopeZipper
import Itasca.Runtime.Code.Body.Reader.Control.ReaderScopeFronts
import Itasca.Runtime.Code.Body.Reader.Common.ReaderStacks

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual ELSE reading preserves stored instruction checks from its matched THEN scope. -/
theorem reader_else_exit_slots_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (held : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 5#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 5#u8 before = .ok (.Ok (),out,after)) : FrameExitSlotBounds after := by
  obtain ⟨callback,read,sourceForm,encoded,results,opened,afterState⟩ := reader_else_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have matched := same.current.form
  rw [sourceForm] at matched
  have sourceThen : ∃ condition, current.form = .then_ (Wasm2.blockType p.current.bt) condition := by
    generalize currentForm : current.form = scopeForm at matched
    cases matched with
    | then_ condition => exact ⟨condition,rfl⟩
  obtain ⟨condition,form⟩ := sourceThen
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,vals⟩ := p.opened
  have frontEq : current.front = Sequence.stackTypes outer := by
    rw [wasm2_spine_values spine]
    simpa only [List.flatMap_def] using fronts.current
  have stack : before.reachable = true → Sequence.stackTypes st.core.vals.val = current.front ++ current.results := by
    intro live
    have segmentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (vals ▸ invariant.known live)).2
    have mono := monomorphic live
    have realized := results
    rw [mono] at realized
    have segmentTypes := (realized_concrete_types segmentKnown realized).symm
    simp only [vals, Sequence.stackTypes, List.map_append]
    change Sequence.stackTypes outer ++ Sequence.stackTypes p.current.vals = _
    rw [segmentTypes, ← frontEq, same.current.results]
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  exact invariant.else_exit_slots ops law out.core _ condition form p.current.bt stack sourceBound held callback

end Itasca.Runtime.Code
