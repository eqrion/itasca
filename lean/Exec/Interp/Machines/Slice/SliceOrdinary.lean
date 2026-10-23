import Exec.Interp.Machines.Slice.SliceAdvance
import Exec.Interp.Relations.OrdinaryStep
import Exec.Interp.Control.LoopStack
import Exec.Interp.Relations.AdministrativeStack

namespace Exec.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_opcode_advance (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (op : OrdinaryOpcode) (after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes functions)
    (binding : FrameBinding store exec raw f)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (slice : Abs.SliceState ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (stack : FrameStackRel store exec ({ f with code := op.source :: after } :: rest))
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw { f with code := op.source :: after } compiled functions targets next output)
    (expected : List valtype)
    (result : Abs.InvocationResult expected ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧
      SliceAdvance store out.2.1 expected compiled.code.length raw.pc.val false
        ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ ⦄ := by
  apply WP.spec_mono (step_opcode_stack memory hooks floats allocator exec store platform index raw inst compiled
    functions targets next output s ambient f rest op after last hf hi hc program binding typed slice stack slots point)
  intro out effect
  obtain ⟨success, sameStore, samePlatform, pc, g, pending, top, continuation, nextStack, nextTyped, nextSlice,
    metadata, simulation, bounded, references⟩ := effect
  exact ⟨success, sameStore, SliceAdvance.ordinary program result top continuation nextStack nextTyped nextSlice
    ⟨metadata.address, metadata.module, metadata.results, metadata.locals⟩ simulation bounded references⟩

theorem step_loop_advance {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (bt : blocktype) (body after : List instr)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes functions)
    (binding : FrameBinding store exec raw f)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩)
    (slice : Abs.SliceState ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩)
    (stack : FrameStackRel store exec ({ f with code := .LOOP bt body :: after } :: rest))
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw { f with code := .LOOP bt body :: after } compiled functions targets next output)
    (expected : List valtype)
    (result : Abs.InvocationResult expected ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧
      ((out.1 = .Ok () ∧ SliceAdvance store out.2.1 expected compiled.code.length raw.pc.val false
        ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩) ∨
      (out.1 = .Err .Terminated ∧ hooks.interrupt platform = .ok (.Terminate, out.2.2.2))) ⦄ := by
  apply WP.spec_mono (step_loop_stack memory hooks floats allocator law exec store platform index raw inst compiled
    functions targets next output s ambient f rest bt body after last hf hi hc program binding typed slice stack slots point)
  intro out effect
  obtain ⟨sameStore, transition⟩ := effect
  refine ⟨sameStore, ?_⟩
  rcases transition with advanced | terminated
  · obtain ⟨success, pc, g, pending, top, continuation, nextStack, nextTyped, nextSlice, metadata, simulation, bounded, references⟩ := advanced
    exact Or.inl ⟨success, SliceAdvance.ordinary program result top continuation nextStack nextTyped nextSlice
      ⟨metadata.address, metadata.module, metadata.results, metadata.locals⟩ simulation bounded references⟩
  · exact Or.inr terminated

theorem step_forwardSkip_advance (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes functions)
    (binding : FrameBinding store exec raw f)
    (stack : FrameStackRel store exec (f :: rest))
    (slots : FrameSlots exec raw f)
    (skip : ForwardSkip raw f compiled functions targets next output)
    (expected : List valtype)
    (typed : Abs.ATyped ⟨s, ambient, f :: rest, []⟩)
    (slice : Abs.SliceState ⟨s, ambient, f :: rest, []⟩)
    (result : Abs.InvocationResult expected ⟨s, ambient, f :: rest, []⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧
      SliceAdvance store out.2.1 expected compiled.code.length raw.pc.val false ⟨s, ambient, f :: rest, []⟩ ⦄ := by
  apply WP.spec_mono (step_forwardSkip_stack memory hooks floats allocator exec store platform index raw inst compiled
    functions targets next output s ambient f rest last hf hi hc program binding stack slots skip)
  intro out effect
  obtain ⟨success, sameStore, samePlatform, target, exactState, nextStack, continuation, simulation⟩ := effect
  have top : out.2.1.frames.val.getLast? = some { raw with pc := target } := by
    rw [exactState, frames_set_last exec index _ last]
    simp
  exact ⟨success, sameStore, SliceAdvance.ordinary program result top ⟨targets, next, output, .ready continuation⟩
    nextStack typed slice ⟨rfl, rfl, rfl, rfl⟩ simulation (fun _ h => h) (fun _ h => h)⟩

theorem step_pendingJump_advance (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes functions)
    (binding : FrameBinding store exec raw f)
    (stack : FrameStackRel store exec (f :: rest))
    (slots : FrameSlots exec raw f)
    (point : ControlPoint raw f compiled functions targets next output true)
    (expected : List valtype)
    (typed : Abs.ATyped ⟨s, ambient, f :: rest, []⟩)
    (slice : Abs.SliceState ⟨s, ambient, f :: rest, []⟩)
    (result : Abs.InvocationResult expected ⟨s, ambient, f :: rest, []⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧
      SliceAdvance store out.2.1 expected compiled.code.length raw.pc.val true ⟨s, ambient, f :: rest, []⟩ ⦄ := by
  apply WP.spec_mono (step_pendingJump_stack memory hooks floats allocator exec store platform index raw inst compiled
    functions targets next output s ambient f rest last hf hi hc program binding stack slots point)
  intro out effect
  obtain ⟨success, sameStore, samePlatform, target, exactState, nextStack, continuation, simulation⟩ := effect
  have top : out.2.1.frames.val.getLast? = some { raw with pc := target } := by
    rw [exactState, frames_set_last exec index _ last]
    simp
  exact ⟨success, sameStore, SliceAdvance.ordinary program result top ⟨targets, next, output, .ready continuation⟩
    nextStack typed slice ⟨rfl, rfl, rfl, rfl⟩ simulation (fun _ h => h) (fun _ h => h)⟩

end Exec.Interp
