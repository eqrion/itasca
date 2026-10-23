import Exec.Abs.Cumulative.ChosenStep
import Exec.Theorems.Api.GrowthChoiceMatching
import Exec.Theorems.Api.StatefulTableGrowDispatchChosen
import Exec.Interp.State.StatefulContinue
import Exec.Interp.StructuredMachine.StatefulPrepare
import Exec.Interp.Cumulative.Machine
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Spec Exec.Interp Exec.Interp.Stateful
variable {emission : Exec.Interp.StructuredMachine.FunctionEmission}

theorem stateful_table_grow_point_step_chosen {choices : Exec.Spec.SourceChoices} (occurrence : Nat) {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [projection : Exec.Interp.StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (table : Nat)
    (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (fetchBound : compiled.code.length≤U32.max)
    (sizes : ∀ object∈store.tables.val,object.elements.length≤U32.max)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint emission (decodeStore view code store) raw {f with code:=(Abs.Stateful.Instruction.tableGrow table).source::after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.tableGrow table).source::after}::rest,[]⟩) :
    let initial : Abs.AState := ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.tableGrow table).source::after}::rest,[]⟩
    (∃ target : U32,raw.pc.val<target.val ∧ compiled.code.val[raw.pc.val]?=some (.Jump target) ∧
      StructuredMachine.FramePoint emission (decodeStore view code store) {raw with pc:=target} {f with code:=(Abs.Stateful.Instruction.tableGrow table).source::after} compiled C targets next output) ∨
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1=.Ok () ∧ out.2.2.2=platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ pc : U32,∃ front : List val,∃ position : Nat,∃ result : U32,
        pc.val=raw.pc.val+1 ∧ raw.base.val≤position ∧ position<exec.slots.length ∧
        SlotsEffect {exec with frames:=exec.frames.set index {raw with pc:=pc}} out.2.1 (exec.slots.val.set position (UScalar.cast .U64 result)) ∧
        (∃ address object delta reference,store.tables.val[address.val]?=some object ∧ TableGrowth store address delta reference (result,out.2.2.1) ∧ val_ref (decodeRef object.ty reference)∈f.vals) ∧
        FrameSlots out.2.1 {raw with pc:=pc} {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} ∧
        StructuredMachine.FramePoint emission (decodeStore view code out.2.2.1) {raw with pc:=pc} {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} compiled C targets next output ∧
        Abs.Cumulative.ChosenStep choices occurrence initial (.next ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]}::rest,[]⟩) ⦄ := by
  dsimp only
  have frameTyped : Abs.FrameTyped (decodeStore view code store) {f with code:=(Abs.Stateful.Instruction.tableGrow table).source::after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases point_values (pairs:=compiled.indirect.val) (decodeStore view code store) f (.tableGrow table) after frameTyped point.code with jump | operation
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
    let initial : Abs.AState := ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.tableGrow table).source::after}::rest,[]⟩
    obtain ⟨out,run,success,samePlatform,resultType,metadata,resultValue,written,mutation,represented,transition⟩ := WP.spec_imp_exists
      (stateful_table_grow_dispatch_chosen occurrence memory hooks floats allocator allocation view code compatible advanced store platform index raw inst C initial
        {f with code:=(Abs.Stateful.Instruction.tableGrow table).source::after} rest after front operands input result table first second a b entry signature
        bindings found sizes rfl moduleEq slots values operandTypes operandTyped actualPosition arguments)
    rw [run]
    apply WP.spec.ret
    have operandLength : operands.length≥1 := by
      have equal := congrArg List.length operandTypes
      rw [List.length_map,signature.input_length] at equal
      cases signature <;> simp_all [Abs.Stateful.Instruction.arity]
    have capacity : raw.base.val+first.val<exec.slots.length := by
      have allScalar := signature.inputs_scalar
      have live := slots
      have enough : Code.encodeValues operands ≠ [] := by
        intro empty
        have lengthEq := congrArg List.length empty
        rw [Code.encodeValues_length,operandTypes] at lengthEq
        cases signature <;> simp [Code.slots,Code.width] at lengthEq
      have words := frame_read_suffix slots values actualPosition rfl
      have firstWord := words 0 (List.length_pos_iff.mpr enough)
      simpa only [Nat.add_zero] using firstWord.1
    refine ⟨success,samePlatform,metadata,pc,front,raw.base.val+first.val,resultValue,pcNext,Nat.le_add_right _ _,capacity,written,mutation,represented,?_,?_⟩
    · have safe := Abs.Stateful.transition_next (.tableGrow table) (decodeStore view code store) ambient f rest after
        ⟨decodeStore view code out.2.2.1,ambient,{f with code:=after,vals:=front++[Abs.integerVal .I32 resultValue.val]}::rest,[]⟩ typed transition.erases
      exact point.continue safe.2.1 front operands [Abs.integerVal .I32 resultValue.val] after values heights
        (by simpa only [resultType,Cumulative.emission,Code.valueType,Abs.integerVal,List.map_cons,List.map_nil,numtype_Inn,valtype_numtype] using tail) pc pcNext
    · exact .stateful transition (by intro impossible;cases impossible)
end Exec.Theorems
