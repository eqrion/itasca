import Exec.Interp.Machines.Slice.SliceOpcode
import Exec.Interp.Relations.OrdinaryFetch
import Exec.Interp.Relations.OrdinaryStack
import Exec.Interp.Control.StructuredScalar
import Exec.Interp.Control.StructuredEqz
import Exec.Interp.Control.StructuredConst
import Exec.Interp.Control.StructuredLocalGet
import Exec.Interp.Control.StructuredLocalWrite
import Exec.Interp.Control.StructuredBranchIf
import Exec.Interp.Control.StructuredIf
import Exec.Interp.Relations.ConstCapacity
import Exec.Interp.Relations.LocalCapacity

namespace Exec.Interp
open Aeneas Aeneas.Std


def OrdinaryResult {M P : Type} (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (compiled : runtime.bytecode.CompiledFunction)
    (functions : List functype) (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (op : OrdinaryOpcode) (after : List instr)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
  ∃ (pc : U32) (g : Abs.AFrame) (targets' : List Code.LabelTarget) (next' : Nat)
    (output' : List valtype) (pending : Bool),
    { out.2.1 with slots := exec.slots } =
      { exec with frames := exec.frames.set index { raw with pc := pc } } ∧
    FrameSlots out.2.1 { raw with pc := pc } g ∧
    ControlPoint { raw with pc := pc } g compiled functions targets' next' output' pending ∧
    Abs.ATyped ⟨s, ambient, g :: rest, []⟩ ∧ FrameMetadata f g ∧
    SourceClosure { f with code := op.source :: after } g ∧
    ConcreteSim compiled.code.length raw.pc.val pc.val false pending
      ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ ⟨s, ambient, g :: rest, []⟩

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_opcode_structured (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance)
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
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw { f with code := op.source :: after } compiled functions targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ out => OrdinaryResult exec store platform index raw compiled functions s ambient f rest op after out ⦄ := by
  obtain ⟨instruction, fetched, allowed⟩ := codeRel_ordinary_fetch point.code.current op.ordinary
  have pcBound := program.fetched_bound instruction fetched
  cases op with
  | const32 value =>
    have bound := Code.const32_capacity compiled program.checked f.module.TYPES functions f.resultTypes
      (f.locals.map Code.valueType) (f.vals.map Code.valueType) targets value after next output raw.pc.val point.code.current
    have storage := binding.capacity inst compiled hi hc
    have capacity : raw.base.val + Code.slots ((f.locals ++ f.vals).map Code.valueType) < exec.slots.length := by
      simp only [List.map_append, Code.slots_append]
      omega
    exact step_const32_structured memory hooks floats allocator exec store platform index raw inst compiled functions targets
      next output s ambient f rest value after last hf hi hc pcBound typed slots capacity point
  | const64 value =>
    have bound := Code.const64_capacity compiled program.checked f.module.TYPES functions f.resultTypes
      (f.locals.map Code.valueType) (f.vals.map Code.valueType) targets value after next output raw.pc.val point.code.current
    have storage := binding.capacity inst compiled hi hc
    have capacity : raw.base.val + Code.slots ((f.locals ++ f.vals).map Code.valueType) < exec.slots.length := by
      simp only [List.map_append, Code.slots_append]
      omega
    exact step_const64_structured memory hooks floats allocator exec store platform index raw inst compiled functions targets
      next output s ambient f rest value after last hf hi hc pcBound typed slots capacity point
  | binary ty op =>
    exact step_sliceBinary_structured memory hooks floats allocator exec store platform index raw inst compiled functions targets
      next output s ambient f rest ty op after last hf hi hc pcBound typed slots point
  | eqz ty =>
    exact step_eqz_structured memory hooks floats allocator exec store platform index raw inst compiled functions targets
      next output s ambient f rest ty after last hf hi hc pcBound typed slots point
  | localGet localIndex =>
    have capacity := local_get_storage_capacity binding inst compiled hi hc program.checked localIndex.val after point
    exact step_localGet_structured memory hooks floats allocator exec store platform index raw inst compiled functions targets
      next output s ambient f rest localIndex after last hf hi hc pcBound typed slots capacity point
  | localWrite localIndex keep =>
    exact step_localWrite_structured memory hooks floats allocator exec store platform index raw inst compiled functions targets
      next output s ambient f rest localIndex keep after last hf hi hc pcBound typed slots point
  | branch depth =>
    exact step_branch_structured memory hooks floats allocator exec store platform index raw inst compiled functions targets
      next output s ambient f rest depth after last hf hi hc pcBound typed slots (slots.capacity binding) point
  | branchIf depth =>
    exact step_branchIf_structured memory hooks floats allocator exec store platform index raw inst compiled functions targets
      next output s ambient f rest depth after last hf hi hc pcBound typed slots point
  | ifElse bt yes no =>
    exact step_if_structured memory hooks floats allocator exec store platform index raw inst compiled functions targets
      next output s ambient f rest bt yes no after last hf hi hc pcBound typed slots point

/-- The actual ordinary dispatch preserves the complete concrete/source frame
stack, together with generated typing and counted source simulation. -/
theorem step_opcode_stack (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance)
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
    (point : StructuredFramePoint raw { f with code := op.source :: after } compiled functions targets next output) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame) (pending : Bool),
        out.2.1.frames.val.getLast? = some { raw with pc := pc } ∧
        (∃ targets' next' output', ControlPoint { raw with pc := pc } g compiled functions targets' next' output' pending) ∧
        FrameStackRel store out.2.1 (g :: rest) ∧ Abs.ATyped ⟨s, ambient, g :: rest, []⟩ ∧
        Abs.SliceState ⟨s, ambient, g :: rest, []⟩ ∧ FrameMetadata f g ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false pending
          ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ ⟨s, ambient, g :: rest, []⟩ ∧
        (∀ bound, Abs.CodeBound bound ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ →
          Abs.CodeBound bound ⟨s, ambient, g :: rest, []⟩) ∧
        (∀ bound, Abs.StateReferencesBound bound ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ →
          Abs.StateReferencesBound bound ⟨s, ambient, g :: rest, []⟩) ⦄ := by
  obtain ⟨out, returned, success, sameStore, samePlatform, pc, g, targets', next', output', pending,
      effect, represented, continuation, nextTyped, metadata, closure, simulation⟩ :=
    WP.spec_imp_exists (step_opcode_structured memory hooks floats allocator exec store platform index raw inst compiled
      functions targets next output s ambient f rest op after last hf hi hc program binding typed slots point)
  have preserved := step_ordinary_prefix memory hooks floats allocator exec store platform index raw inst compiled
    functions targets next output f op.source after last hf hi hc point op.ordinary out returned
  have top : out.2.1.frames.val.getLast? = some { raw with pc := pc } := by
    have frames := congrArg runtime.interp.Execution.frames effect
    change out.2.1.frames = exec.frames.set index { raw with pc := pc } at frames
    rw [frames, frames_set_last exec index _ last, List.getLast?_concat]
  rw [returned]
  apply WP.spec.ret
  exact ⟨success, sameStore, samePlatform, pc, g, pending, top, ⟨targets', next', output', continuation⟩,
    stack.ordinary raw index pc last hf binding program continuation represented ⟨metadata.address, metadata.module, metadata.results, metadata.locals⟩ effect preserved,
    nextTyped, closure.slice slice, metadata, simulation, (fun _ bounded => closure.codeBound bounded), fun _ bounded => closure.referenceBound bounded⟩

end Exec.Interp
