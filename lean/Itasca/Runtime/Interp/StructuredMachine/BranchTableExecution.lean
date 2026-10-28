import Itasca.Runtime.Interp.StructuredMachine.BranchTable
import Itasca.Runtime.Interp.StructuredMachine.SupportedAdvance
import Itasca.Runtime.Abs.BrTableTransition
namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std

/-- The actual table jump consumes its selector, then reuses the checked branch
fragment inside the same active and suspended machine. -/
theorem step_brTable_execution
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (depths : List labelidx) (fallback : labelidx) (front : List val) (value : Nat)
    (selector start len : U32) (expected : List valtype)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw
      {f with code:=.BR_TABLE depths fallback::after} compiled C targets next output)
    (values : f.vals=front++[Abs.integerVal .I32 value]) (bound : value<2^32)
    (table : Code.BranchTableCode (Code.CompilerTables.ofFunction compiled) C.LOCALS targets
      (front.map Code.valueType) compiled.code.val depths fallback raw.pc.val next selector start len)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code:=.BR_TABLE depths fallback::after}::rest,[]⟩ expected raw.pc.val false) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.1=store ∧ out.2.2.2=platform ∧
      Advance view code store out.2.1 expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=.BR_TABLE depths fallback::after}::rest,[]⟩ ⦄ := by
  have transition : Abs.BrTable.Transition
      ⟨Store.decodeStore view code store,ambient,{f with code:=.BR_TABLE depths fallback::after}::rest,[]⟩
      ⟨Store.decodeStore view code store,ambient,{f with code:=.BR (Abs.BrTable.select depths fallback value)::after,vals:=front}::rest,[]⟩ := .next values bound
  apply WP.spec_mono (step_brTable_point memory hooks floats allocator exec store platform index raw inst compiled selector start len value
    (Store.decodeStore view code store) ambient f rest after depths fallback front C targets next output hf hi hc last
    (program.fetched_bound _ table.instruction) bound table point.bindings point.locals
    (by simpa only [←values] using point.labels) point.code.targets point.code.normal point.code.exit point.code.root
    (by simpa only [←values] using machine.typed) (by simpa only [←values] using slots))
  rintro out ⟨target,success,sameStore,samePlatform,effect,represented,retained,typed,simulation⟩
  refine ⟨success,sameStore,samePlatform,target.val,false,
    ⟨Store.decodeStore view code store,ambient,{f with code:=.BR (Abs.BrTable.select depths fallback value)::after,vals:=front}::rest,[]⟩,?_,?_,?_,rfl,?_⟩
  · exact Execution.ordinary view code ambient {f with code:=.BR_TABLE depths fallback::after}
      {f with code:=.BR (Abs.BrTable.select depths fallback value)::after,vals:=front} rest expected raw.pc.val false machine
      (.refl store) (Itasca.Runtime.Spec.extend_store_refl _ machine.typed.typed.store) raw index target last hf program (.ready retained)
      represented ⟨rfl,rfl,rfl,rfl⟩ (by rw [effect]) (by rw [effect]; exact .refl _ _) typed
      (transition.next_supported machine.core)
  · exact ConcreteSim.of_source _ _ _ _ _ (transition.correct machine.typed).2
  · exact fun _ owned => transition.next_owned owned
  · exact fun _ bounded => transition.next_bound bounded
end Itasca.Runtime.Interp.StructuredMachine
