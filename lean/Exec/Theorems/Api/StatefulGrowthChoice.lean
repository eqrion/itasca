import Exec.Abs.Stateful.Transition
namespace Exec.Theorems
open SpecExt

theorem stateful_memory_choice (state : Abs.AState) (f : Abs.AFrame) (front : List val)
    (delta address : Nat) (object : meminst) (choice : Option meminst)
    (values : f.vals = front++[Abs.integerVal .I32 delta])
    (mapped : f.module.MEMS[0]? = some address) (found : state.store.MEMS[address]? = some object)
    (grown : Abs.Stateful.MemoryGrowthChoice object delta choice) :
    Abs.Stateful.Selection.Allowed {memory:=choice} .memoryGrow state.store f := by
  intro otherFront otherDelta otherAddress otherObject otherValues otherMapped otherFound
  have addresses : otherAddress=address := Option.some.inj (otherMapped.symm.trans mapped)
  subst otherAddress
  have objects : otherObject=object := Option.some.inj (otherFound.symm.trans found)
  subst otherObject
  have equal := congrArg Abs.pop (otherValues.symm.trans values)
  simp only [Abs.pop_append,Option.some.injEq,Prod.mk.injEq] at equal
  have deltaEq : otherDelta=delta := by simpa [Abs.integerVal,numtype_Inn] using equal.2
  simpa only [deltaEq] using grown

theorem stateful_table_choice (state : Abs.AState) (f : Abs.AFrame) (front : List val)
    (index delta address : Nat) (reference : ref) (object : tableinst) (choice : Option tableinst)
    (values : f.vals = front++[val_ref reference,Abs.integerVal .I32 delta])
    (mapped : f.module.TABLES[index]? = some address) (found : state.store.TABLES[address]? = some object)
    (grown : Abs.Stateful.TableGrowthChoice object delta reference choice) :
    Abs.Stateful.Selection.Allowed {table:=choice} (.tableGrow index) state.store f := by
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
  simpa only [deltaEq,refEq] using grown
end Exec.Theorems
