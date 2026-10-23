import Exec.Theorems.Composition.Supported.SupportedExecutionOutcome
import Exec.Interp.StructuredMachine.BranchTableExecution
import Exec.Interp.StructuredMachine.JumpExecution
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

theorem step_branch_table_supported
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (depths : List labelidx) (fallback : labelidx) (expected : List valtype)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint (Store.decodeStore view code store) raw
      {f with code:=.BR_TABLE depths fallback::after} compiled C targets next output)
    (machine : StructuredMachine.Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code:=.BR_TABLE depths fallback::after}::rest,[]⟩ expected raw.pc.val false)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=.BR_TABLE depths fallback::after}::rest,[]⟩ out ⦄ := by
  rcases StructuredMachine.branchTable_point_head point.code with jump | operation
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    have retained : StructuredMachine.FramePoint (Store.decodeStore view code store) {raw with pc:=target}
        {f with code:=.BR_TABLE depths fallback::after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,tail⟩
    apply WP.spec_mono (StructuredMachine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled
      ambient {f with code:=.BR_TABLE depths fallback::after} rest expected C targets next output target last hf hi hc forward fetch slots retained machine program)
    rintro out ⟨success,sameStore,samePlatform,effect,fresh,simulation⟩
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success
      ⟨target.val,false,_,fresh,simulation,fun _ h => h,rfl,fun _ h => h⟩
  · obtain ⟨stack,selector,start,len,shape,table⟩ := operation
    have typed : Abs.FrameTyped (Store.decodeStore view code store) {f with code:=.BR_TABLE depths fallback::after} [] := by
      cases machine.typed.typed.frames with | cons head _ => exact head
    obtain ⟨front,value,values,bound⟩ := Abs.BrTable.operands typed
    have frontTypes : front.map Code.valueType = stack := by
      have equal : front.map Code.valueType ++ [.I32] = stack ++ [.I32] := by
        simpa only [values,List.map_append,List.map_cons,List.map_nil,Abs.integerVal,Code.valueType,numtype_Inn,valtype_numtype] using shape
      exact List.append_cancel_right equal
    rw [←frontTypes] at table
    apply WP.spec_mono (StructuredMachine.step_brTable_execution memory hooks floats allocator view code exec store platform
      index raw inst compiled C targets next output ambient f rest after depths fallback front value selector start len expected
      last hf hi hc program slots point values bound table machine)
    rintro out ⟨success,sameStore,samePlatform,advance⟩
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success advance
end Exec.Theorems
