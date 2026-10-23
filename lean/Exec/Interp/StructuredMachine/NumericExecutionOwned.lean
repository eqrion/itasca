import Exec.Abs.Numeric.Positive
import Exec.Interp.Machines.Uniform.UniformSourceControl
import Exec.Interp.StructuredMachine.ControlSemantics
import Exec.Interp.Machines.Core.CoreBound
import Exec.Abs.Ownership.Core
import Exec.Interp.StructuredMachine.NumericFetch
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Spec.Extend
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std Abs.Numeric
variable {emission : FunctionEmission} [∀ compiled, FloatHeads (emission compiled)]

variable {allowed supported owned} (semantics : ControlSemantics allowed supported owned)
include semantics

theorem step_numeric_execution_owned_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (op : Instruction) (after : List instr)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := op.source :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ pc : U32, ∃ g : Abs.AFrame,
        Execution emission supported view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        UniformConcreteSim raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ [] ∧
        (∀ bounds, owned bounds initial → owned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩)) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧ (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count (Abs.decode initial) [] ⟨⟨initial.store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched⟩ := numeric_fetched op after point
  have pcBound := program.fetched_bound instruction fetched
  apply WP.spec_mono (step_numeric memory hooks floats allocator exec store platform index raw inst compiled C targets
    next output (Store.decodeStore view code store) ambient f rest op after last hf hi hc pcBound machine.typed slots point)
  intro out effect
  refine ⟨effect.1,effect.2.1,?_⟩
  rcases effect.2.2 with success | trapped
  · obtain ⟨status,pc,g,unchanged,represented,continuation,fresh,metadata,closure,simulation,prefixEffect,sourceStep⟩ := success
    have uniform : UniformConcreteSim raw.pc.val pc.val false false
        ⟨Store.decodeStore view code store,ambient,{f with code := op.source::after}::rest,[]⟩
        ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
      rcases sourceStep with same | step
      · subst g
        exact simulation.uniform_same (by scalar_tac)
      · exact UniformConcreteSim.single (Abs.Numeric.core_step_positive _ _ _ _ _ _ _ machine.typed.typed step)
    have covered : supported ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
      rcases sourceStep with same | step
      · simpa only [same] using machine.core
      · exact semantics.next_covered machine.typed machine.core step
    have ownership : ∀ bounds, owned bounds ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩ →
        owned bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
      intro bounds bounded
      rcases sourceStep with same | step
      · simpa only [same] using bounded
      · exact semantics.next_owned machine.typed machine.core step bounds bounded
    refine Or.inl ⟨status,pc,g,?_,simulation,uniform,ownership,semantics.bound_transition machine.typed machine.core (sourceStep.imp_left (fun same => by rw [same]))⟩
    exact machine.ordinary view code ambient {f with code := op.source :: after} g rest expected raw.pc.val false
      (.refl store) (Spec.extend_store_refl _ machine.typed.typed.store) raw index pc last hf program (.ready continuation)
      represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged prefixEffect fresh covered
  · exact Or.inr trapped
theorem step_numeric_execution_owned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (op : Instruction) (after : List instr)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := op.source :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ pc : U32, ∃ g : Abs.AFrame,
        Execution emission supported view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩ ∧
        (∀ bounds, owned bounds initial → owned bounds ⟨initial.store,ambient,g::rest,[]⟩) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound ⟨initial.store,ambient,g::rest,[]⟩)) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧ (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count (Abs.decode initial) [] ⟨⟨initial.store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  apply WP.spec_mono (step_numeric_execution_owned_uniform semantics memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest op after last hf hi hc program slots point expected machine)
  rintro out ⟨same,platform,success | trapped⟩
  · rcases success with ⟨success,pc,g,machine,simulation,uniform,ownership,bounded⟩
    exact ⟨same,platform,Or.inl ⟨success,pc,g,machine,simulation,ownership,bounded⟩⟩
  · exact ⟨same,platform,Or.inr trapped⟩

end Exec.Interp.StructuredMachine
