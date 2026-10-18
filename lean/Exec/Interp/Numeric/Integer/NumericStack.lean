import Exec.Interp.Control.StructuredNumeric
import Exec.Interp.Machines.Slice.SliceAdvance
import Exec.Interp.Relations.OrdinaryFetch
import Exec.Interp.Relations.OrdinaryStack

namespace Exec.Interp
open Aeneas Aeneas.Std Abs.Numeric

theorem step_numeric_advance {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (op : Instruction) (after : List instr)
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
      out.2.2.1 = store ∧
      ((out.1 = .Ok () ∧ SliceAdvance store out.2.1 expected compiled.code.length raw.pc.val false
        ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧
        (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count
          (Abs.decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
          ⟨⟨s, ambient⟩, [.TRAP]⟩)) ⦄ := by
  have ordinary : OrdinarySource op.source := by
    cases op <;> (try casesm* Conversion) <;> trivial
  obtain ⟨instruction, fetched, allowed⟩ := codeRel_ordinary_fetch point.code.current ordinary
  have pcBound := program.fetched_bound instruction fetched
  obtain ⟨out, returned, sameStore, samePlatform, transition⟩ := WP.spec_imp_exists
    (step_numeric_structured memory hooks floats allocator exec store platform index raw inst compiled functions targets
      next output s ambient f rest op after last hf hi hc pcBound typed slots point)
  rw [returned]
  apply WP.spec.ret
  refine ⟨sameStore, ?_⟩
  rcases transition with success | trapped
  · obtain ⟨status, pc, g, effect, represented, continuation, nextTyped, metadata, closure, simulation⟩ := success
    have preserved := step_ordinary_prefix memory hooks floats allocator exec store platform index raw inst compiled
      functions targets next output f op.source after last hf hi hc point ordinary out returned
    have top : out.2.1.frames.val.getLast? = some { raw with pc := pc } := by
      have frames := congrArg runtime.interp.Execution.frames effect
      change out.2.1.frames = exec.frames.set index { raw with pc := pc } at frames
      rw [frames, frames_set_last exec index _ last, List.getLast?_concat]
    have nextStack := stack.ordinary raw index pc last hf binding program (.ready continuation) represented
      ⟨metadata.address, metadata.module, metadata.results, metadata.locals⟩ effect preserved
    exact .inl ⟨status, SliceAdvance.ordinary program result top ⟨targets,next,output,.ready continuation⟩
      nextStack nextTyped (closure.slice slice) ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩
      simulation (fun _ bounded => closure.codeBound bounded) (fun _ bounded => closure.referenceBound bounded)⟩
  · exact .inr trapped
end Exec.Interp
