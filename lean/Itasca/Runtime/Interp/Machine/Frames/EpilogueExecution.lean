import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Interp.Machine.Frames.FunctionEnd
import Itasca.Runtime.Interp.Machine.Frames.ReturnCompletion
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Interp.Machine.Control.JumpExecution
import Itasca.Runtime.Interp.Relations.Capacity
import Itasca.Runtime.Spec.Extend

/-!
Execution of the function-end epilogue.

Main declarations: `step_function_end_execution`. A direct consumer is `Integration.Execution.Dispatch.HostSite`.
-/

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std

theorem step_function_end_execution {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := [],labels := []} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := [],labels := []}::rest,[]⟩ expected raw.pc.val false) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := [],labels := []}::rest,[]⟩
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
  rcases function_end program point with ⟨target,forward,fetched,retained⟩ | ⟨count,fetched,localSlots,width,pcBound⟩
  · apply WP.spec_mono (step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled
      ambient {f with code := [],labels := []} rest expected C targets next output target last hf hi hc forward fetched slots retained machine program)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,fresh,simulation⟩ := effect
    exact ⟨success,sameStore,samePlatform,target.val,_,fresh,simulation,(fun _ h => h),rfl,(fun _ h => h)⟩
  · obtain ⟨types,nextTyped,simulation⟩ := frame_end_source (Store.decodeStore view code store) ambient f rest machine.typed.typed
    have codeTypes : f.vals.map Code.valueType = f.resultTypes := by
      simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using types
    have actualWidth : count.val = Code.slots (f.vals.map Code.valueType) := by rw [codeTypes]; exact width
    have capacity := slots.capacity binding
    have bounds : raw.base.val+compiled.local_slots.val+count.val ≤ exec.slots.length := by
      simpa only [List.map_append,Code.slots_append,localSlots,actualWidth,Nat.add_assoc] using capacity
    have original : ValuesAt exec.slots.val (raw.base.val+compiled.local_slots.val) f.vals := by
      simpa only [localSlots] using slots.operands
    apply WP.spec_mono (step_epilogue_refines memory hooks floats allocator exec store platform index raw compiled.local_slots count inst compiled
      last hf hi hc fetched pcBound (Store.decodeStore view code store) ambient {f with labels := []} rest (Or.inl rfl)
      machine.typed.typed slots localSlots width capacity)
    intro out effect
    obtain ⟨success,returned,represented,sameStore,samePlatform,preserved,nextState⟩ := effect
    have result := function_end_invocation_result (Store.decodeStore view code store) ambient f rest machine.typed.typed types expected machine.result
    obtain ⟨pc,fresh⟩ := Execution.return_complete view code ambient {f with code := [],labels := []} rest expected raw.pc.val false machine raw top
      compiled.local_slots.val count.val returned f.vals original codeTypes actualWidth bounds nextTyped result
    exact ⟨success,sameStore,samePlatform,pc,_,fresh,ConcreteSim.of_source _ _ _ _ _ simulation,
      StructuredMachine.return_owned f.vals (fun _ member => member),by cases rest <;> rfl,(fun _ bounded => returnedState_codeBound bounded f.vals)⟩
end Itasca.Runtime.Interp.StructuredMachine
