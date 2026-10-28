import Exec.Interp.State.StatefulOperandValues
namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt

theorem three_i32_operands (store : _root_.store) (operands : List val)
    (types : operands.map Code.valueType=[.I32,.I32,.I32])
    (typed : ∀ value∈operands,Val_ok store value (Code.valueType value)) :
    ∃ x y z : U32,operands=[Abs.integerVal .I32 x.val,Abs.integerVal .I32 y.val,Abs.integerVal .I32 z.val] := by
  obtain ⟨x,y,z,rfl,xType,yType,zType⟩ := three_operand_values types
  have xTyped := typed x (by simp)
  have yTyped := typed y (by simp)
  have zTyped := typed z (by simp)
  rw [xType] at xTyped
  rw [yType] at yTyped
  rw [zType] at zTyped
  obtain ⟨a,rfl,aBound⟩ := Abs.integer_val_inv (ty:=.I32) xTyped
  obtain ⟨b,rfl,bBound⟩ := Abs.integer_val_inv (ty:=.I32) yTyped
  obtain ⟨c,rfl,cBound⟩ := Abs.integer_val_inv (ty:=.I32) zTyped
  exact ⟨UScalar.ofNatCore a aBound,UScalar.ofNatCore b bBound,UScalar.ofNatCore c cBound,rfl⟩

theorem frame_three_i32_slots {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : Abs.AFrame} {front : List val} {first : U32} (a b c : U32)
    (slots : FrameSlots exec raw f)
    (values : f.vals=front++[Abs.integerVal .I32 a.val,Abs.integerVal .I32 b.val,Abs.integerVal .I32 c.val])
    (position : first.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType)) :
    exec.slots.val[raw.base.val+first.val]?=some (UScalar.cast .U64 a) ∧
    exec.slots.val[raw.base.val+first.val+1]?=some (UScalar.cast .U64 b) ∧
    exec.slots.val[raw.base.val+first.val+2]?=some (UScalar.cast .U64 c) := by
  have encoded : Code.encodeValues [Abs.integerVal .I32 a.val,Abs.integerVal .I32 b.val,Abs.integerVal .I32 c.val]=[a.val,b.val,c.val] := rfl
  refine ⟨?_,?_,?_⟩
  · simpa only [Nat.add_zero] using frame_read_scalar slots values position encoded 0 (by simp) (UScalar.cast .U64 a) (by simp)
  · exact frame_read_scalar slots values position encoded 1 (by simp) (UScalar.cast .U64 b) (by simp)
  · exact frame_read_scalar slots values position encoded 2 (by simp) (UScalar.cast .U64 c) (by simp)
end Itasca.Runtime.Interp.Stateful
