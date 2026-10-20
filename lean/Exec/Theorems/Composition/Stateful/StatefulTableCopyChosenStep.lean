import Exec.Abs.Cumulative.ChosenStep
import Exec.Abs.Stateful.ChosenSelection
import Exec.Theorems.Composition.Stateful.StatefulTableCopyDispatch
import Exec.Interp.State.StatefulContinue
import Exec.Interp.StructuredMachine.StatefulPrepare
import Exec.Interp.Cumulative.Machine
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Spec Exec.Interp Exec.Interp.Stateful
variable {emission : Exec.Interp.StructuredMachine.FunctionEmission}

theorem stateful_table_copy_point_step_chosen {choices : SourceChoices} (occurrence : Nat) {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    [projection : Exec.Interp.StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (tableIndex sourceIndex : Nat)
    (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (fetchBound : compiled.code.length≤U32.max)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint emission (decodeStore view code store) raw {f with code:=(Abs.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after}::rest,[]⟩) :
    let initial : Abs.AState := ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after}::rest,[]⟩
    (∃ target : U32,raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      StructuredMachine.FramePoint emission (decodeStore view code store) {raw with pc:=target} {f with code:=(Abs.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after} compiled C targets next output) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2=platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      ((∃ pc : U32,∃ front : List val,
        out.1=.Ok () ∧ pc.val=raw.pc.val+1 ∧ out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}} ∧
        (∃ address sourceAddress : runtime.TableAddr,∃ object segment destination source count,store.tables.val[address.index.val]?=some object ∧ store.tables.val[sourceAddress.index.val]?=some segment ∧ segment.ty=object.ty ∧ TableCopyEffect store address.index object segment destination source count (out.1,out.2.2.1)) ∧
        FrameSlots out.2.1 {raw with pc:=pc} {f with code:=after,vals:=front} ∧
        StructuredMachine.FramePoint emission (decodeStore view code out.2.2.1) {raw with pc:=pc} {f with code:=after,vals:=front} compiled C targets next output ∧
        Abs.Cumulative.ChosenStep choices occurrence initial (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩)) ∨
      (out.1=.Err (.Trap .TableOutOfBounds) ∧ out.2.2.1=store ∧
        (∃ pc : U32,pc.val=raw.pc.val+1 ∧ out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}}) ∧
        Abs.Cumulative.ChosenStep choices occurrence initial .trap)) ⦄ := by
  dsimp only
  have frameTyped : Abs.FrameTyped (decodeStore view code store) {f with code:=(Abs.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases point_values (pairs:=compiled.indirect.val) (decodeStore view code store) f (.tableCopy tableIndex sourceIndex) after frameTyped point.code with jump | operation
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨front,operands,input,result,first,second,a,b,entry,values,operandTypes,signature,heights,operandTyped,position,secondSlot,arguments,pair,fetch,tail⟩ := operation
    have pcBound : raw.pc.val<U32.max := by
      have inCode := (List.getElem?_eq_some_iff.mp fetch).1
      change compiled.code.val.length≤U32.max at fetchBound
      omega
    have actualPosition : first.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType) := by
      simpa only [point.locals] using position
    have bindings : Abs.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C := by
      rw [←moduleEq]
      exact point.bindings
    apply Or.inr
    apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled _ last frameFound found codeFound fetch pcBound
    intro pc pcNext
    let advanced := {exec with frames:=exec.frames.set index {raw with pc:=pc}}
    let initial : Abs.AState := ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after}::rest,[]⟩
    obtain ⟨out,run,same,samePlatform,resultNil,rawEffect,metadata,represented,transition⟩ := WP.spec_imp_exists
      (stateful_table_copy_dispatch memory hooks floats allocator view code advanced store platform index raw inst compiled C initial
        {f with code:=(Abs.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after} rest after front operands input result tableIndex sourceIndex first second a b entry signature
        bindings found codeFound rfl moduleEq slots values operandTypes operandTyped actualPosition arguments pair)
    rw [run]
    apply WP.spec.ret
    refine ⟨samePlatform,metadata,?_⟩
    obtain ⟨address,sourceAddress,object,segment,destination,source,count,issued,sourceFound,sameType,effect⟩ := rawEffect
    have classified : out.1=.Ok () ∨ (out.1=.Err (.Trap .TableOutOfBounds) ∧ out.2.2.1=store) := by
      unfold TableCopyEffect at effect
      split at effect
      · obtain ⟨buffer,equal,content⟩ := effect
        exact Or.inl (congrArg Prod.fst equal)
      · exact Or.inr ⟨congrArg Prod.fst effect,congrArg Prod.snd effect⟩
    rcases classified with success | ⟨error,sameStore⟩
    · change out.1=.Ok () at success
      have sourceStep : Abs.Stateful.Transition initial {f with code:=(Abs.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after} rest after (.tableCopy tableIndex sourceIndex)
          (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩) := by
        simpa [statefulBulkResult,success,initial,Abs.advance] using transition
      refine Or.inl ⟨pc,front,success,pcNext,same,⟨address,sourceAddress,object,segment,destination,source,count,issued,sourceFound,sameType,effect⟩,represented,?_,?_⟩
      · have safe := Abs.Stateful.transition_next (.tableCopy tableIndex sourceIndex) (decodeStore view code store) ambient {f with code:=(Abs.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after} rest after
          ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front}::rest,[]⟩ typed sourceStep
        have continued := point.continue safe.2.1 front operands [] after values heights (by simpa only [resultNil,Cumulative.emission,List.map_nil] using tail) pc pcNext
        simpa only [List.append_nil] using continued
      · exact .stateful (sourceStep.chosen_of_no_growth (by rfl)) (by intro impossible;cases impossible)
    · change out.1=.Err (.Trap .TableOutOfBounds) at error
      have sourceStep : Abs.Stateful.Transition initial {f with code:=(Abs.Stateful.Instruction.tableCopy tableIndex sourceIndex).source::after} rest after (.tableCopy tableIndex sourceIndex) .trap := by
        simpa [statefulBulkResult,error] using transition
      exact Or.inr ⟨error,sameStore,⟨pc,pcNext,same⟩,.stateful (sourceStep.chosen_of_no_growth (by rfl)) (by intro impossible;cases impossible)⟩
end Exec.Theorems
