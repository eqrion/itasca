import Itasca.Runtime.Interp.Machines.Core.CoreOwnership
import Itasca.Runtime.Interp.StructuredMachine.StructuredReturn
import Itasca.Runtime.Interp.StructuredMachine.ReturnExecutionCommon
import Itasca.Runtime.Interp.StructuredMachine.OrdinaryExecution
import Itasca.Runtime.Interp.StructuredMachine.JumpExecution
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Spec.Extend
namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std

theorem step_return_execution {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)] (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .RETURN::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .RETURN::after}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .RETURN::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ pc source, Execution view code store out.2.1 source expected pc false ∧
        ConcreteSim compiled.code.length raw.pc.val pc false false initial source ∧
        (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds source) ∧ source.ambient = ambient ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound source) ⦄ := by
  dsimp only
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1 = index.val := by change exec.frames.length-1 = index.val; omega
    rw [position]; exact hf
  have binding := (machine.stack.top raw top).binding
  have capacity := slots.capacity binding
  have current := point.code.current
  rw [point.locals] at current
  have pcBound : raw.pc.val < U32.max := by
    rcases codeRel_return_values f.locals f.vals current with ⟨target,forward,fetched,continuation⟩ | ⟨front,results,src,count,split,types,source,width,fetched⟩
    · exact program.fetched_bound _ fetched
    · exact program.fetched_bound _ fetched
  apply WP.spec_mono (step_return_structured memory hooks floats allocator exec store platform index raw inst compiled C targets next output
    (Store.decodeStore view code store) ambient f rest after last hf hi hc pcBound machine.typed.typed slots capacity point)
  intro out effect
  obtain ⟨success,sameStore,samePlatform,operation⟩ := effect
  refine ⟨success,sameStore,samePlatform,?_⟩
  rcases operation with ⟨target,exactState,retained,decrease⟩ | ⟨front,results,src,count,split,types,source,width,original,bounds,returned,represented,nextTyped,simulation⟩
  · have fields : {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := target}} := by rw [exactState]
    have represented : FrameSlots out.2.1 {raw with pc := target} {f with code := .RETURN::after} := by simpa only [FrameSlots,exactState] using slots
    have preserved : SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val := by rw [exactState]; exact .refl _ _
    refine ⟨target.val,_,Execution.ordinary view code ambient {f with code := .RETURN::after} {f with code := .RETURN::after} rest expected raw.pc.val false machine
      (.refl store) (Itasca.Runtime.Spec.extend_store_refl _ machine.typed.typed.store) raw index target last hf program (.ready retained)
      represented ⟨rfl,rfl,rfl,rfl⟩ fields preserved machine.typed machine.core,?_,(fun _ h => h),rfl,(fun _ bounded => bounded)⟩
    exact Or.inl ⟨rfl,decrease⟩
  · have result := return_invocation_result (Store.decodeStore view code store) ambient f rest after front results machine.typed.typed split types expected machine.result
    obtain ⟨pc,fresh⟩ := Execution.return_complete view code ambient {f with code := .RETURN::after} rest expected raw.pc.val false machine raw top
      src count returned results original (by simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using types)
      width bounds nextTyped result
    exact ⟨pc,_,fresh,ConcreteSim.of_source _ _ _ _ _ simulation,
      StructuredMachine.return_owned results (by intro value member; change value ∈ f.vals; rw [split]; exact List.mem_append_right _ member),by cases rest <;> rfl,(fun _ bounded => returnedState_codeBound bounded results)⟩
end Itasca.Runtime.Interp.StructuredMachine
