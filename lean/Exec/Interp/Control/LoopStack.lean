import Exec.Interp.Relations.OrdinaryStack
import Exec.Interp.Relations.OrdinaryFetch
import Exec.Interp.Control.StructuredLoop

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem step_loop_stack {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance)
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
    (point : StructuredFramePoint raw { f with code := .LOOP bt body :: after } compiled functions targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧
      ((out.1 = .Ok () ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        out.2.1.frames.val.getLast? = some { raw with pc := pc } ∧
        (∃ targets' next' output', ControlPoint { raw with pc := pc } g compiled functions targets' next' output' pending) ∧
        FrameStackRel store out.2.1 (g :: rest) ∧ Abs.ATyped ⟨s, ambient, g :: rest, []⟩ ∧
        Abs.SliceState ⟨s, ambient, g :: rest, []⟩ ∧ FrameMetadata f g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩ ⟨s, ambient, g :: rest, []⟩ ∧
        (∀ bound, Abs.CodeBound bound ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩ →
          Abs.CodeBound bound ⟨s, ambient, g :: rest, []⟩) ∧
        (∀ bound, Abs.StateReferencesBound bound ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩ →
          Abs.StateReferencesBound bound ⟨s, ambient, g :: rest, []⟩)) ∨
      (out.1 = .Err .Terminated ∧ hooks.interrupt platform = .ok (.Terminate, out.2.2.2))) ⦄ := by
  obtain ⟨instruction, fetched, allowed⟩ := codeRel_ordinary_fetch point.code.current (by trivial)
  have pcBound := program.fetched_bound instruction fetched
  obtain ⟨out, returned, sameStore, result⟩ := WP.spec_imp_exists
    (step_loop_structured memory hooks floats allocator law exec store platform index raw inst compiled functions
      targets next output s ambient f rest bt body after last hf hi hc pcBound typed slots point)
  rw [returned]
  apply WP.spec.ret
  refine ⟨sameStore, ?_⟩
  rcases result with success | terminated
  · obtain ⟨success, pc, g, targets', next', output', pending, effect, represented, continuation,
      nextTyped, metadata, closure, simulation⟩ := success
    have preserved := step_prefix memory hooks floats allocator exec store platform index raw inst compiled instruction
      last hf hi hc fetched allowed out returned
    have top : out.2.1.frames.val.getLast? = some { raw with pc := pc } := by
      have frames := congrArg runtime.interp.Execution.frames effect
      change out.2.1.frames = exec.frames.set index { raw with pc := pc } at frames
      rw [frames, frames_set_last exec index _ last, List.getLast?_concat]
    exact Or.inl ⟨success, pc, g, pending, top, ⟨targets', next', output', continuation⟩,
      stack.ordinary raw index pc last hf binding program continuation represented
        ⟨metadata.address, metadata.module, metadata.results, metadata.locals⟩ effect preserved,
      nextTyped, closure.slice slice, metadata, simulation, (fun _ bounded => closure.codeBound bounded), fun _ bounded => closure.referenceBound bounded⟩
  · exact Or.inr terminated

end Exec.Interp
