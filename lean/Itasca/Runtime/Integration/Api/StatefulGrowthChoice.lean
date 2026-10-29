import Itasca.Runtime.SourceMachine.Stateful.Transition
namespace Itasca.Runtime.Integration
open SpecExt

theorem stateful_memory_choice (state : SourceMachine.AState) (f : SourceMachine.AFrame) (front : List val)
    (delta address : Nat) (object : meminst) (choice : Option meminst)
    (values : f.vals = front++[SourceMachine.integerVal .I32 delta])
    (mapped : f.module.MEMS[0]? = some address) (found : state.store.MEMS[address]? = some object)
    (grown : SourceMachine.Stateful.MemoryGrowthChoice object delta choice) :
    SourceMachine.Stateful.Selection.Allowed {memory:=choice} .memoryGrow state.store f := by
  intro otherFront otherDelta otherAddress otherObject otherValues otherMapped otherFound
  have addresses : otherAddress=address := Option.some.inj (otherMapped.symm.trans mapped)
  subst otherAddress
  have objects : otherObject=object := Option.some.inj (otherFound.symm.trans found)
  subst otherObject
  have equal := congrArg SourceMachine.pop (otherValues.symm.trans values)
  simp only [SourceMachine.pop_append,Option.some.injEq,Prod.mk.injEq] at equal
  have deltaEq : otherDelta=delta := by simpa [SourceMachine.integerVal,numtype_Inn] using equal.2
  simpa only [deltaEq] using grown

theorem stateful_table_choice (state : SourceMachine.AState) (f : SourceMachine.AFrame) (front : List val)
    (index delta address : Nat) (reference : ref) (object : tableinst) (choice : Option tableinst)
    (values : f.vals = front++[val_ref reference,SourceMachine.integerVal .I32 delta])
    (mapped : f.module.TABLES[index]? = some address) (found : state.store.TABLES[address]? = some object)
    (grown : SourceMachine.Stateful.TableGrowthChoice object delta reference choice) :
    SourceMachine.Stateful.Selection.Allowed {table:=choice} (.tableGrow index) state.store f := by
  intro otherFront otherReference otherDelta otherAddress otherObject otherValues otherMapped otherFound
  have addresses : otherAddress=address := Option.some.inj (otherMapped.symm.trans mapped)
  subst otherAddress
  have objects : otherObject=object := Option.some.inj (otherFound.symm.trans found)
  subst otherObject
  have equal := congrArg SourceMachine.pop (otherValues.symm.trans values)
  rw [show otherFront++[val_ref otherReference,SourceMachine.integerVal .I32 otherDelta] =
    (otherFront++[val_ref otherReference])++[SourceMachine.integerVal .I32 otherDelta] by simp,
    show front++[val_ref reference,SourceMachine.integerVal .I32 delta] =
    (front++[val_ref reference])++[SourceMachine.integerVal .I32 delta] by simp] at equal
  simp only [SourceMachine.pop_append,Option.some.injEq,Prod.mk.injEq] at equal
  have deltaEq : otherDelta=delta := by simpa [SourceMachine.integerVal,numtype_Inn] using equal.2
  have refs := congrArg SourceMachine.pop equal.1
  simp only [SourceMachine.pop_append,Option.some.injEq,Prod.mk.injEq] at refs
  have refEq : otherReference=reference := by
    have decoded := congrArg SourceMachine.Stateful.asReference refs.2
    simpa only [SourceMachine.Stateful.as_reference_value,Option.some.injEq] using decoded
  simpa only [deltaEq,refEq] using grown
end Itasca.Runtime.Integration
