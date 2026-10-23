import Exec.Theorems.Composition.Stateful.StatefulDrops
import Exec.Store.Initialization.SegmentStep
import Exec.Interp.State.StatefulSegmentLookup
import Exec.Interp.State.StatefulOperandSlots
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

def statefulIsDrop : Abs.Stateful.Instruction → Bool
  | .dataDrop _ | .elemDrop _ => true
  | _ => false

inductive StatefulDropEffect {M : Type} (before : runtime.store.Store M) : runtime.store.Store M → Prop where
  | data (address : Usize) (issued : address.val<before.datas.length) :
      StatefulDropEffect before {before with datas:=before.datas.set address ⟨alloc.vec.Vec.new U8⟩}
  | element (address : Usize) (issued : address.val<before.elems.length) :
      StatefulDropEffect before {before with elems:=before.elems.set address {before.elems.val[address.val] with refs:=alloc.vec.Vec.new U64}}

theorem stateful_drop_dispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (C : context)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front operands : List val) (input output : List valtype) (op : Abs.Stateful.Instruction)
    (first second a b entry : U32) (isDrop : statefulIsDrop op=true)
    (signature : Abs.Stateful.Signature C op input output)
    (bindings : Abs.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals=front++operands)
    (operandTypes : operands.map Code.valueType=input) (arguments : Code.StatefulArguments op a b) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Code.statefulInstruction op first second a entry) ⦃ out =>
      out.1=.Ok () ∧ out.2.1=exec ∧ out.2.2.2=platform ∧ output=[] ∧ front=f.vals ∧
      StatefulDropEffect store out.2.2.1 ∧ FrameStoreMetadata store out.2.2.1 ∧
      FrameSlots out.2.1 raw {f with code:=after} ∧
      Abs.Stateful.Transition state f rest after op
        (Abs.advance {state with store:=decodeStore view code out.2.2.1} {f with code:=after} rest) ⦄ := by
  cases signature <;> simp only [statefulIsDrop,Bool.false_eq_true] at isDrop
  case elemDrop index type selected =>
    have operandsNil := List.map_eq_nil_iff.mp operandTypes
    subst operands
    simp only [List.append_nil] at values
    have indexEq : a.val=index := arguments.1
    obtain ⟨address,mapped,issued⟩ := Stateful.element_binding_raw view code store inst C index _ bindings selected
    rw [←indexEq] at mapped
    obtain ⟨out,run,same,effect,metadata,transition⟩ := WP.spec_imp_exists
      (segment_execute_bulk memory exec store raw.instance raw.function raw.base (.ElemDrop a) _
        (stateful_element_drop_effect memory view code store raw.instance raw.function raw.base (alloc.vec.Vec.deref exec.slots) inst a address
          state f rest after found mapped issued sourceStore moduleEq))
    have status := congrArg Prod.fst effect
    have changed := congrArg Prod.snd effect
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨status,same,rfl,trivial,values.symm,by rw [changed];exact .element address issued,metadata,
      by rw [same];exact slots,by simpa only [indexEq] using transition⟩
  case dataDrop index selected =>
    have operandsNil := List.map_eq_nil_iff.mp operandTypes
    subst operands
    simp only [List.append_nil] at values
    have indexEq : a.val=index := arguments.1
    obtain ⟨address,mapped,issued⟩ := Stateful.data_binding_raw view code store inst C index _ bindings selected
    rw [←indexEq] at mapped
    obtain ⟨out,run,same,effect,metadata,transition⟩ := WP.spec_imp_exists
      (segment_execute_bulk memory exec store raw.instance raw.function raw.base (.DataDrop a) _
        (stateful_data_drop_effect memory view code store raw.instance raw.function raw.base (alloc.vec.Vec.deref exec.slots) inst a address
          state f rest after found mapped issued sourceStore moduleEq))
    have status := congrArg Prod.fst effect
    have changed := congrArg Prod.snd effect
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨status,same,rfl,trivial,values.symm,by rw [changed];exact .data address issued,metadata,
      by rw [same];exact slots,by simpa only [indexEq] using transition⟩
end Exec.Theorems
