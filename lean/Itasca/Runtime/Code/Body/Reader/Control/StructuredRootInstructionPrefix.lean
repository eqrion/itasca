import Itasca.Runtime.Code.Body.Reader.Control.StructuredRootMapPublication
import Itasca.Runtime.Code.Local.Checking.RootCloseInstructionPrefix
import Itasca.Runtime.Code.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Code.Body.Source.TypedLowering

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Source root geometry, the preceding live stack, and branch exits discharge every
stored instruction check at actual function close. The final return's capacity
comes from the retained slot bounds and prepared local region. -/
theorem structured_root_checked_instructions {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals [] current raw position)
    (rootForm : current.form = .body) (entered : current.entered = true)
    (front : current.front = []) (results : current.results = returns)
    (initialLayout : LocalLayout initial) (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (normal : before.reachable = true → Sequence.stackTypes raw = returns)
    (exits : ∀ frame ∈ before.frames.val, frame.end_reachable = true →
      frame.height.val+frame.results.val ≤ before.function.slot_count.val)
    (maps : ControlMapPublication before) (held : CompilerInstructionPrefix before)
    (consumed : position < state.pos.val)
    (endBound : before.function.body_start.val+state.pos.val ≤ before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    CheckedInstructionPrefix after.function ∧ after.frames.val = [] := by
  obtain ⟨prior,frame,frames,paired,shape⟩ := invariant.frames.split
  have empty : prior = [] := by cases paired; rfl
  let rest := alloc.vec.Vec.new runtime.compiler.Frame
  have restEmpty : rest.val = [] := by simp [rest,alloc.vec.Vec.new]
  have physical : before.frames.val = rest.val++[frame] := by simpa only [restEmpty,empty] using frames
  have root : frame.kind = .Body := by simpa only [rootForm,ScopeForm.kind] using shape.kind
  have noIf : frame.if_pc = none := by
    have guard := shape.guard
    simpa only [rootForm,SourceScope.guardPosition,Option.map_eq_none_iff] using guard
  have bound := invariant.codeBudget.fetch_bound sourceBound
  let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have sites := (invariant.mode.sites frame (by simp [frames])).branches.branches
  let geometry : ScopeCloseGeometry before := ⟨frame,rest,target,physical,rfl,sites⟩
  have stable := invariant.metadata.trans (compiler_end_stable_result ops law before after state kind bt (.Ok ()) called)
  have localLayout := stable.local_layout initialLayout
  obtain ⟨_,_,_,_,localsEq,_,slotsEq,_⟩ := stable.fields
  have localTypes : compilerLocals after = locals := by simpa only [compilerLocals,localsEq] using initialLocals
  have localCapacity : after.function.local_slots.val ≤ after.function.slot_count.val := by
    rw [slotsEq]
    exact initialCapacity.trans stable.capacity
  have height : frame.height = after.function.local_slots := by
    apply UScalar.eq_of_val_eq
    rw [localLayout.slots,localTypes]
    simpa only [front,slots,Nat.add_zero] using shape.height entered
  have width : frame.results.val = slots returns := by simpa only [results] using shape.results
  obtain ⟨codeFits,offsetsFit,_,_⟩ := invariant.capacities sourceBound
  have progress : before.next_source.val < state.pos.val := lt_of_le_of_lt invariant.cursor consumed
  have endFits : before.function.body_end.val ≤ Usize.max := by scalar_tac
  have returnFits : frame.height.val+
      (if scopeExitLive before.reachable frame then frame.results else 0#u32).val ≤ after.function.slot_count.val := by
    have capacity := (compiler_end_stable_result ops law before after state kind bt (.Ok ()) called).capacity
    by_cases live : before.reachable = true
    · have layout := (invariant.live live).2.layout
      have bound := layout.live_slots_fit live
      have localsMatch := (invariant.live live).2.localsEq
      rw [normal live,localsMatch,← width] at bound
      have heightBefore : frame.height.val = slots locals := by
        simpa only [front,slots,Nat.add_zero] using shape.height entered
      rw [← heightBefore] at bound
      simpa [scopeExitLive,live,root] using bound.trans capacity
    · have dead : before.reachable = false := by cases reachable : before.reachable <;> simp_all
      by_cases exit : frame.end_reachable = true
      · have bound := exits frame (by simp [frames]) exit
        simpa [scopeExitLive,dead,root,exit] using bound.trans capacity
      · have noExit : frame.end_reachable = false := by cases reachable : frame.end_reachable <;> simp_all
        simpa [scopeExitLive,dead,root,noExit,height] using localCapacity
  refine ⟨compiler_root_close_checked_instructions_of_slots ops law before after state kind bt geometry root restEmpty noIf
    codeFits offsetsFit (by omega) (by omega) maps held returnFits called,?_⟩
  have effect := close_function_effect ops law before state frame rest target physical root noIf rfl sites shape.mapBound
    (by omega) codeFits offsetsFit (by omega)
  have canonical : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty =
      .ok (.Ok (),after) := called
  rw [canonical,WP.spec_ok] at effect
  obtain ⟨frames,_,_,_⟩ := effect rfl
  rw [frames]
  exact restEmpty

end Itasca.Runtime.Code
