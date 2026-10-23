import Exec.Abs.Cumulative.ChosenStep
import Exec.Abs.Stateful.ChosenSelection
import Exec.Theorems.Composition.Stateful.StatefulDropDispatch
import Exec.Interp.State.StatefulContinue
import Exec.Interp.StructuredMachine.StatefulPrepare
import Exec.Interp.StructuredMachine.Execution
import Exec.Abs.Cumulative.Step
import Exec.Code.Local.Relations.Common.StatefulEmission
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Spec Exec.Interp Exec.Interp.Stateful

theorem stateful_drop_point_step_chosen {choices : SourceChoices} (occurrence : Nat) {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [projection : Exec.Interp.StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (op : Abs.Stateful.Instruction)
    (isDrop : statefulIsDrop op=true) (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (fetchBound : compiled.code.length≤U32.max)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint (decodeStore view code store) raw {f with code:=op.source::after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩) :
    let initial : Abs.AState := ⟨decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩
    (∃ target : U32,raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      StructuredMachine.FramePoint (decodeStore view code store) {raw with pc:=target} {f with code:=op.source::after} compiled C targets next output) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧
      StatefulDropEffect store out.2.2.1 ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ pc : U32,pc.val=raw.pc.val+1 ∧ out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
      FrameSlots out.2.1 {raw with pc:=pc} {f with code:=after} ∧
      StructuredMachine.FramePoint (decodeStore view code out.2.2.1) {raw with pc:=pc} {f with code:=after} compiled C targets next output ∧
      Abs.Cumulative.ChosenStep choices occurrence initial (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after}::rest,[]⟩) ⦄ := by
  dsimp only
  have frameTyped : Abs.FrameTyped (decodeStore view code store) {f with code:=op.source::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases point_values (pairs:=compiled.indirect.val) (decodeStore view code store) f op after frameTyped point.code with jump | operation
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨front,operands,input,result,first,second,a,b,entry,values,operandTypes,signature,heights,operandTyped,position,secondSlot,arguments,pair,fetch,tail⟩ := operation
    have pcBound : raw.pc.val<U32.max := by
      have inCode := (List.getElem?_eq_some_iff.mp fetch).1
      change compiled.code.val.length≤U32.max at fetchBound
      omega
    have bindings : Abs.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C := by
      rw [←moduleEq]
      exact point.bindings
    apply Or.inr
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled _ last frameFound found codeFound fetch pcBound
    intro pc pcNext
    let advanced := {exec with frames:=exec.frames.set index {raw with pc:=pc}}
    let initial : Abs.AState := ⟨decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩
    obtain ⟨out,run,success,same,samePlatform,resultNil,frontEq,effect,metadata,represented,transition⟩ := WP.spec_imp_exists
      (stateful_drop_dispatch memory hooks floats allocator view code advanced store platform index raw inst C initial
        {f with code:=op.source::after} rest after front operands input result op first second a b entry isDrop signature
        bindings found rfl moduleEq slots values operandTypes arguments)
    rw [run]
    apply WP.spec.ret
    refine ⟨success,samePlatform,effect,metadata,pc,pcNext,same,represented,?_,?_⟩
    · have safe := Abs.Stateful.transition_next op (decodeStore view code store) ambient f rest after
        ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after}::rest,[]⟩ typed transition
      have noOperands : operands=[] := by
        have lengths := congrArg List.length values
        simp only [List.length_append,frontEq] at lengths
        exact List.length_eq_zero_iff.mp (by omega)
      have continued := point.continue safe.2.1 front operands [] after values heights (by simpa only [resultNil,List.map_nil] using tail) pc pcNext
      simpa only [frontEq,List.append_nil] using continued
    · exact .stateful (transition.chosen_of_no_growth (by cases op <;> simp only [statefulIsDrop] at isDrop <;> first | contradiction | rfl)) (by intro impossible; cases impossible)
end Exec.Theorems
