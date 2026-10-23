import Exec.Interp.State.StatefulTableSet
import Exec.Interp.State.StatefulOperandSlots
namespace Exec.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Exec.Store

theorem table_set_slots {M : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (index value table : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (position : U32)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f)
    (first : index.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType))
    (second : value.val=index.val+1)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[Abs.integerVal .I32 position.val,val_ref (decodeRef object.ty exec.slots.val[raw.base.val+value.val]!)]) :
    runtime.interp.execute_table_set memory exec store raw.instance raw.base index value table ⦃ out =>
      out.2.1 = exec ∧ FrameStoreMetadata store out.2.2 ∧
      if position.val < object.elements.length then
        out.1 = .Ok () ∧ TableMutation store out.2.2 address object exec.slots.val[raw.base.val+value.val]! ∧
        FrameSlots out.2.1 raw {f with code:=after,vals:=front} ∧
        Abs.Stateful.Transition state f rest after (.tableSet table.val)
          (Abs.advance {state with store := decodeStore view code out.2.2} {f with code := after,vals := front} rest)
      else out = (.Err (.Trap .TableOutOfBounds),exec,store) ∧
        Abs.Stateful.Transition state f rest after (.tableSet table.val) .trap ⦄ := by
  have encoded : Code.encodeValues [Abs.integerVal .I32 position.val,val_ref (decodeRef object.ty exec.slots.val[raw.base.val+value.val]!)] =
      [position.val,exec.slots.val[raw.base.val+value.val]!.val] := by
    have reference : Code.encodeValue (val_ref (decodeRef object.ty exec.slots.val[raw.base.val+value.val]!)) = [exec.slots.val[raw.base.val+value.val]!.val] := encode_decoded_ref _ _
    simp only [Code.encodeValues,List.flatMap_cons,List.flatMap_nil,List.append_nil,reference]
    rfl
  have words := frame_read_suffix slots values first encoded
  obtain ⟨indexBound,indexWord⟩ := words 0 (by simp)
  obtain ⟨valueBound,_⟩ := words 1 (by simp)
  simp only [Nat.add_zero,List.getElem!_cons_zero] at indexBound indexWord
  have valueBound' : raw.base.val+value.val<exec.slots.length := by simpa [second,Nat.add_assoc] using valueBound
  have actual : UScalar.cast .U32 exec.slots.val[raw.base.val+index.val]! = position := by scalar_tac
  apply WP.spec_mono (stateful_table_set_effect memory view code exec store raw.instance raw.base index value table
    inst address object position state f rest after front found mapped issued actual indexBound valueBound' sourceStore moduleEq values)
  rintro out ⟨same,metadata,effect⟩
  refine ⟨same,metadata,?_⟩
  split at effect
  · rename_i inside
    rw [if_pos inside]
    exact ⟨effect.1,effect.2.1,by rw [same];exact frame_consume after slots values,effect.2.2⟩
  · rename_i outside
    rw [if_neg outside]
    exact effect
end Exec.Interp.Stateful
