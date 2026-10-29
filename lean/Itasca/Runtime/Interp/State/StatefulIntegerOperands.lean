import Itasca.Runtime.Interp.State.StatefulOperandValues
namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt

theorem three_i32_operands (store : _root_.store) (operands : List val)
    (types : operands.map Compiler.valueType=[.I32,.I32,.I32])
    (typed : ∀ value∈operands,Val_ok store value (Compiler.valueType value)) :
    ∃ x y z : U32,operands=[SourceMachine.integerVal .I32 x.val,SourceMachine.integerVal .I32 y.val,SourceMachine.integerVal .I32 z.val] := by
  obtain ⟨x,y,z,rfl,xType,yType,zType⟩ := three_operand_values types
  have xTyped := typed x (by simp)
  have yTyped := typed y (by simp)
  have zTyped := typed z (by simp)
  rw [xType] at xTyped
  rw [yType] at yTyped
  rw [zType] at zTyped
  obtain ⟨a,rfl,aBound⟩ := SourceMachine.integer_val_inv (ty:=.I32) xTyped
  obtain ⟨b,rfl,bBound⟩ := SourceMachine.integer_val_inv (ty:=.I32) yTyped
  obtain ⟨c,rfl,cBound⟩ := SourceMachine.integer_val_inv (ty:=.I32) zTyped
  exact ⟨UScalar.ofNatCore a aBound,UScalar.ofNatCore b bBound,UScalar.ofNatCore c cBound,rfl⟩

theorem frame_three_i32_slots {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {front : List val} {first : U32} (a b c : U32)
    (slots : FrameSlots exec raw f)
    (values : f.vals=front++[SourceMachine.integerVal .I32 a.val,SourceMachine.integerVal .I32 b.val,SourceMachine.integerVal .I32 c.val])
    (position : first.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType)) :
    exec.slots.val[raw.base.val+first.val]?=some (UScalar.cast .U64 a) ∧
    exec.slots.val[raw.base.val+first.val+1]?=some (UScalar.cast .U64 b) ∧
    exec.slots.val[raw.base.val+first.val+2]?=some (UScalar.cast .U64 c) := by
  have encoded : Compiler.encodeValues [SourceMachine.integerVal .I32 a.val,SourceMachine.integerVal .I32 b.val,SourceMachine.integerVal .I32 c.val]=[a.val,b.val,c.val] := rfl
  refine ⟨?_,?_,?_⟩
  · simpa only [Nat.add_zero] using frame_read_scalar slots values position encoded 0 (by simp) (UScalar.cast .U64 a) (by simp)
  · exact frame_read_scalar slots values position encoded 1 (by simp) (UScalar.cast .U64 b) (by simp)
  · exact frame_read_scalar slots values position encoded 2 (by simp) (UScalar.cast .U64 c) (by simp)
end Itasca.Runtime.Interp.Stateful
