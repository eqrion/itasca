import Exec.Interp.Core.Numeric
import Exec.Interp.Core.OrdinaryExecution
import Exec.Spec.Extend
namespace Exec.Interp
open Aeneas Aeneas.Std Abs.Numeric

theorem core_numeric_fetched {raw compiled C targets next output s} {f : Abs.AFrame}
    (op : Instruction) (after : List instr)
    (point : CoreFramePoint s raw {f with code := op.source :: after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction := by
  have linear : linearSource op.source = true := by cases op <;> (try casesm* Conversion) <;> rfl
  rcases structuredCode_linear_inv linear point.code.current with ⟨target,forward,fetch,tail⟩ | ⟨middle,emitted,tail,head,fragment,rest⟩
  · exact ⟨_,fetch⟩
  · obtain ⟨stack,left,right,shape,emittedEq,middleEq,leftPos,rightPos⟩ := linearEmission_numeric_inv op (coreEmission_numeric_pure op head)
    refine ⟨Code.integerInstruction op left left right,?_⟩
    simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])

theorem step_numeric_core_execution {M P F A : Type}
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
    (point : CoreFramePoint (Store.decodeStore view code store) raw {f with code := op.source :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : CoreExecution view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ pc : U32, ∃ g : Abs.AFrame,
        CoreExecution view code store out.2.1 ⟨initial.store,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨initial.store,ambient,g::rest,[]⟩) ∨
      (∃ trap, out.1 = .Err (.Trap trap) ∧ (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        ∃ count, 0 < count ∧ Spec.StepsHN count (Abs.decode initial) [] ⟨⟨initial.store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  obtain ⟨instruction,fetched⟩ := core_numeric_fetched op after point
  have pcBound := program.fetched_bound instruction fetched
  apply WP.spec_mono (step_numeric_core memory hooks floats allocator exec store platform index raw inst compiled C targets
    next output (Store.decodeStore view code store) ambient f rest op after last hf hi hc pcBound machine.typed slots point)
  intro out effect
  refine ⟨effect.1,effect.2.1,?_⟩
  rcases effect.2.2 with success | trapped
  · obtain ⟨status,pc,g,unchanged,represented,continuation,fresh,metadata,closure,simulation,prefixEffect,sourceStep⟩ := success
    have covered : Abs.CoreState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
      rcases sourceStep with same | step
      · simpa only [same] using machine.core
      · exact Abs.Core.step_core _ _ machine.typed.typed machine.core step
    refine Or.inl ⟨status,pc,g,?_,simulation⟩
    exact machine.ordinary view code ambient {f with code := op.source :: after} g rest expected raw.pc.val false
      (.refl store) (Spec.extend_store_refl _ machine.typed.typed.store) raw index pc last hf program (.ready continuation)
      represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ unchanged prefixEffect fresh covered
  · exact Or.inr trapped
end Exec.Interp
