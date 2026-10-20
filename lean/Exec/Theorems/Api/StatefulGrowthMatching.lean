import Exec.Abs.Stateful.ChosenTransition
namespace Exec.Theorems
open SpecExt

theorem stateful_memory_match (choices : Exec.Spec.SourceChoices) (occurrence : Nat) (state : Abs.AState) (f : Abs.AFrame) (front : List val)
    (delta address : Nat) (object : meminst) (choice : Option meminst)
    (values : f.vals = front++[Abs.integerVal .I32 delta])
    (mapped : f.module.MEMS[0]? = some address) (found : state.store.MEMS[address]? = some object)
    (matched : choices.memory occurrence object delta=choice) :
    Abs.Stateful.Selection.Matches {memory:=choice} choices occurrence .memoryGrow state.store f := by
  intro otherFront otherDelta otherAddress otherObject otherValues otherMapped otherFound
  have addresses : otherAddress=address := Option.some.inj (otherMapped.symm.trans mapped)
  subst otherAddress
  have objects : otherObject=object := Option.some.inj (otherFound.symm.trans found)
  subst otherObject
  have equal := congrArg Abs.pop (otherValues.symm.trans values)
  simp only [Abs.pop_append,Option.some.injEq,Prod.mk.injEq] at equal
  have deltaEq : otherDelta=delta := by simpa [Abs.integerVal,numtype_Inn] using equal.2
  simpa only [deltaEq] using matched

theorem stateful_table_match (choices : Exec.Spec.SourceChoices) (occurrence : Nat) (state : Abs.AState) (f : Abs.AFrame) (front : List val)
    (index delta address : Nat) (reference : ref) (object : tableinst) (choice : Option tableinst)
    (values : f.vals = front++[val_ref reference,Abs.integerVal .I32 delta])
    (mapped : f.module.TABLES[index]? = some address) (found : state.store.TABLES[address]? = some object)
    (matched : choices.table occurrence object delta reference=choice) :
    Abs.Stateful.Selection.Matches {table:=choice} choices occurrence (.tableGrow index) state.store f := by
  intro otherFront otherReference otherDelta otherAddress otherObject otherValues otherMapped otherFound
  have addresses : otherAddress=address := Option.some.inj (otherMapped.symm.trans mapped)
  subst otherAddress
  have objects : otherObject=object := Option.some.inj (otherFound.symm.trans found)
  subst otherObject
  have equal := congrArg Abs.pop (otherValues.symm.trans values)
  rw [show otherFront++[val_ref otherReference,Abs.integerVal .I32 otherDelta] =
    (otherFront++[val_ref otherReference])++[Abs.integerVal .I32 otherDelta] by simp,
    show front++[val_ref reference,Abs.integerVal .I32 delta] =
    (front++[val_ref reference])++[Abs.integerVal .I32 delta] by simp] at equal
  simp only [Abs.pop_append,Option.some.injEq,Prod.mk.injEq] at equal
  have deltaEq : otherDelta=delta := by simpa [Abs.integerVal,numtype_Inn] using equal.2
  have refs := congrArg Abs.pop equal.1
  simp only [Abs.pop_append,Option.some.injEq,Prod.mk.injEq] at refs
  have refEq : otherReference=reference := by
    have decoded := congrArg Abs.Stateful.asReference refs.2
    simpa only [Abs.Stateful.asReference_value,Option.some.injEq] using decoded
  simpa only [deltaEq,refEq] using matched
end Exec.Theorems
