import Itasca.Runtime.Interp.State.StatefulOperandSlots
import Itasca.Runtime.Interp.Relations.Capacity
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem indirect_call_slots {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : Abs.AFrame} {front args : List val} {params : List valtype} {position : Nat} {offset index : U32}
    (slots : FrameSlots exec raw f)
    (values : f.vals=(front++args)++[Abs.integerVal .I32 position])
    (argumentTypes : args.map Code.valueType=params)
    (basePosition : offset.val=Code.slots ((f.locals++front).map Code.valueType))
    (indexPosition : index.val=offset.val+Code.slots params)
    (bounded : position<2^32) :
    ∃ selector : U32, selector.val=position ∧ raw.base.val+index.val<exec.slots.length ∧
      UScalar.cast .U32 exec.slots.val[raw.base.val+index.val]! = selector := by
  have read := Stateful.frame_read_suffix_word slots values
    (src:=index) (by simp only [List.map_append,Code.slots_append,argumentTypes] at basePosition ⊢;omega)
    (show Code.encodeValues [Abs.integerVal .I32 position]=[position] from rfl) 0 (by simp)
  obtain ⟨inside,word⟩ := read
  simp only [Nat.add_zero,List.getElem!_cons_zero] at inside word
  let selector : U32 := UScalar.ofNatCore position bounded
  refine ⟨selector,rfl,inside,?_⟩
  apply UScalar.eq_of_val_eq
  simp only [UScalar.cast_val_eq,word]
  exact Nat.mod_eq_of_lt bounded
end Itasca.Runtime.Interp
