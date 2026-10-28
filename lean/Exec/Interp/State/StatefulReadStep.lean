import Exec.Interp.State.StatefulReadDispatch
import Exec.Interp.State.StatefulCapacity
import Exec.Interp.State.StatefulContinue
import Exec.Interp.StructuredMachine.StatefulPrepare
import Exec.Interp.StructuredMachine.Execution
import Exec.Abs.Cumulative.Step
import Exec.Code.Local.Relations.Common.StatefulEmission
namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Spec

theorem read_point_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [projection : Itasca.Runtime.Interp.StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (op : Abs.Stateful.Instruction)
    (readOnly : op.readOnly=true) (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (checked : runtime.bytecode.CompiledFunction.well_formed compiled=.ok true)
    (fetchBound : compiled.code.length≤U32.max)
    (allocated : raw.base.val+compiled.slot_count.val≤exec.slots.length)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint (decodeStore view code store) raw {f with code:=op.source::after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩) :
    let initial : Abs.AState := ⟨decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩
    (∃ target : U32,raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      StructuredMachine.FramePoint (decodeStore view code store) {raw with pc:=target} {f with code:=op.source::after} compiled C targets next output) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1=store ∧ out.2.2.2=platform ∧
      ((∃ pc : U32,∃ produced : List val,∃ position : Nat,∃ word : U64,
        out.1=.Ok () ∧ pc.val=raw.pc.val+1 ∧ raw.base.val≤position ∧ position<exec.slots.length ∧
        SlotsEffect {exec with frames:=exec.frames.set index {raw with pc:=pc}} out.2.1 (exec.slots.val.set position word) ∧
        FrameSlots out.2.1 {raw with pc:=pc} {f with code:=after,vals:=produced} ∧
        StructuredMachine.FramePoint (decodeStore view code store) {raw with pc:=pc} {f with code:=after,vals:=produced} compiled C targets next output ∧
        Abs.Cumulative.Step initial (.next ⟨decodeStore view code store,ambient,{f with code:=after,vals:=produced}::rest,[]⟩)) ∨
      (out.1=.Err (.Trap .TableOutOfBounds) ∧
        (∃ pc : U32,pc.val=raw.pc.val+1 ∧ out.2.1={exec with frames:=exec.frames.set index {raw with pc:=pc}}) ∧
        Abs.Cumulative.Step initial .trap)) ⦄ := by
  dsimp only
  have frameTyped : Abs.FrameTyped (decodeStore view code store) {f with code:=op.source::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases point_values (pairs:=compiled.indirect.val) (decodeStore view code store) f op after frameTyped point.code with jump | operation
  · obtain ⟨target,forward,fetch,tail⟩ := jump
    exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨front,operands,input,result,first,second,a,b,entry,values,operandTypes,signature,heights,operandTyped,position,secondSlot,arguments,pair,fetch,tail⟩ := operation
    have bounded := read_valid_capacity compiled op first second a entry readOnly (Code.well_formed_fetched compiled checked raw.pc.val _ fetch)
    have capacity : raw.base.val+first.val<exec.slots.length := by omega
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
    let initial : Abs.AState := ⟨decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩
    obtain ⟨out,run,sameStore,samePlatform,effect⟩ := WP.spec_imp_exists
      (read_dispatch memory hooks floats allocator view laws code advanced store platform index raw inst C initial
        {f with code:=op.source::after} rest after front operands input result op first second a b entry readOnly signature
        bindings found rfl moduleEq slots values operandTypes operandTyped actualPosition capacity arguments)
    rw [run]
    apply WP.spec.ret
    refine ⟨sameStore,samePlatform,?_⟩
    rcases effect with ⟨produced,word,success,producedTypes,written,represented,transition⟩ | ⟨error,same,transition⟩
    · refine Or.inl ⟨pc,front++produced,raw.base.val+first.val,word,success,pcNext,Nat.le_add_right _ _,capacity,written,represented,?_,?_⟩
      · apply point.continue (extend_store_refl _ typed.typed.store) front operands produced after values heights _ pc pcNext
        simpa only [producedTypes] using tail
      · exact .stateful transition (by intro impossible; cases impossible)
    · exact Or.inr ⟨error,⟨pc,pcNext,same⟩,.stateful transition (by intro impossible; cases impossible)⟩
end Itasca.Runtime.Interp.Stateful
