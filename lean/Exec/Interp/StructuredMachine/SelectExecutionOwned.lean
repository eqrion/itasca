import Exec.Abs.Core.SelectPositive
import Exec.Interp.Machines.Uniform.UniformSourceControl
import Exec.Interp.StructuredMachine.SupportedControlSemantics
import Exec.Interp.Machines.Core.CoreOwnership
import Exec.Abs.Core.Bound
import Exec.Interp.StructuredMachine.SelectStep
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Spec.Extend
namespace Itasca.Runtime.Interp.StructuredMachine.Select
open Aeneas Aeneas.Std
theorem step_select_core_execution_owned_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame)
    (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .SELECT none::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        UniformConcreteSim raw.pc.val pc.val false false initial {initial with frames := g::rest} [] ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    rcases corePoint_select_head after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,ty,a,b,condition,input,leftPos,rightPos,conditionPos,fetched,tail⟩
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
  apply WP.spec_mono (step_select_core memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    (Store.decodeStore view code store) ambient f rest after last frameFound instanceFound codeFound pcBound slots point machine.typed)
  intro out effect
  obtain ⟨success,sameStore,samePlatform,pc,g,fields,represented,retained,fresh,metadata,transition,simulation,preserved⟩ := effect
  have uniform : UniformConcreteSim raw.pc.val pc.val false false
      ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩
      ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ [] := by
    rcases transition with same | step
    · rw [← same] at simulation ⊢
      exact simulation.uniform_same (by scalar_tac)
    · exact UniformConcreteSim.single (Abs.Core.select_step_positive _ _ _ _ _ _ machine.typed step)
  have covered : Abs.SupportedState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
    rcases transition with same | step
    · rw [← same]; exact machine.core
    · exact StructuredMachine.core_step_supported machine.typed machine.core step
  exact ⟨success,sameStore,samePlatform,pc,g,
    Execution.ordinary view code ambient {f with code := .SELECT none::after} g rest expected raw.pc.val false machine
      (.refl store) (Itasca.Runtime.Spec.extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound program
      (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields preserved fresh covered,simulation,uniform,StructuredMachine.owned_transition machine.typed machine.core transition,StructuredMachine.bound_transition machine.typed machine.core transition⟩
theorem step_select_core_execution_owned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame)
    (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .SELECT none::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT none::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ (pc : U32) (g : Abs.AFrame),
        Execution view code store out.2.1 {initial with frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds {initial with frames := g::rest}) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound {initial with frames := g::rest}) ⦄ := by
  apply WP.spec_mono (step_select_core_execution_owned_uniform memory hooks floats allocator exec store platform index raw inst compiled C targets next output view code ambient f rest after last frameFound instanceFound codeFound slots point expected machine program)
  rintro out ⟨success,same,platform,pc,g,machine,simulation,uniform,ownership,bounded⟩
  exact ⟨success,same,platform,pc,g,machine,simulation,ownership,bounded⟩

end Itasca.Runtime.Interp.StructuredMachine.Select
