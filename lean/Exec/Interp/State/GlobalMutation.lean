import Exec.Interp.State.GlobalCoreWrite
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- An instruction writes the represented source value into one existing global;
scalar writes retain the unused high word. -/
def GlobalMutation {M : Type} (before after : runtime.store.Store M) (value : val) : Prop :=
  ∃ index : Usize, ∃ old : runtime.store.GlobalInst, ∃ lo hi : U64,
    before.globals.val[index.val]? = some old ∧ old.ty.mutability = .Var ∧
    sourceType old.ty.valtype = Code.valueType value ∧
    pairWords old.ty.valtype (lo,hi) = Code.encodeValue value ∧
    (old.ty.valtype ≠ .V128 → hi = old.hi) ∧
    after = {before with globals := before.globals.set index {old with lo,hi}}

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem global_set_mutation
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (f : Abs.AFrame) (front : List val) (value : val)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (scalar : object.ty.valtype ≠ .V128) (mutable : object.ty.mutability = .Var)
    (typed : sourceType object.ty.valtype = Code.valueType value) :
    runtime.interp.execute_global_set memory exec store raw.instance raw.base src index
      ⦃ out => GlobalMutation store out.2.2 value ⦄ := by
  have operand := (global_top_words exec raw f front value src values slots position).2
  have width : (Code.encodeValue value).length = 1 := by
    rw [Code.encodeValue_length,←typed]
    cases eq : object.ty.valtype <;> simp only [sourceType,Code.width]
    exact False.elim (scalar eq)
  have capacity : raw.base.val+src.val < exec.slots.length := by
    have atZero := (operand 0 (by rw [width]; omega)).1
    simpa only [Nat.add_zero] using atZero
  have represented := operand.readPair object.ty.valtype (by rw [Code.encodeValue_length,←typed])
  have scalarType : sourceType object.ty.valtype ≠ .V128 := by
    cases eq : object.ty.valtype <;> simp only [sourceType,ne_eq,reduceCtorEq,not_false_eq_true]
    exact False.elim (scalar eq)
  simp only [pairWords,readPair,scalarType,ite_false] at represented
  apply WP.spec_mono (global_set_dispatch_effect memory exec store raw.instance raw.base src index inst address object found mapped issued capacity)
  intro out effect
  subst out
  refine ⟨address.index,object,_,object.hi,issued,mutable,typed,?_,fun _ => rfl,rfl⟩
  simpa only [pairWords,scalarType,ite_false] using represented

theorem global_set2_mutation
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (f : Abs.AFrame) (front : List val) (value : val)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (vector : object.ty.valtype = .V128) (mutable : object.ty.mutability = .Var)
    (typed : sourceType object.ty.valtype = Code.valueType value) :
    runtime.interp.execute_global_set2 memory exec store raw.instance raw.base src index
      ⦃ out => GlobalMutation store out.2.2 value ⦄ := by
  have operand := (global_top_words exec raw f front value src values slots position).2
  have width : (Code.encodeValue value).length = 2 := by
    rw [Code.encodeValue_length,←typed,vector]; rfl
  have capacity : raw.base.val+src.val+2 ≤ exec.slots.length := by
    have atOne := (operand 1 (by rw [width]; omega)).1
    change raw.base.val+src.val+1 < exec.slots.val.length at atOne
    change raw.base.val+src.val+2 ≤ exec.slots.val.length
    omega
  have represented := operand.readPair object.ty.valtype (by rw [Code.encodeValue_length,←typed])
  simp only [pairWords,readPair,vector,sourceType,ite_true] at represented
  apply WP.spec_mono (global_set2_dispatch_effect memory exec store raw.instance raw.base src index inst address object found mapped issued capacity)
  intro out effect
  subst out
  refine ⟨address.index,object,_,_,issued,mutable,typed,?_,fun h => False.elim (h vector),rfl⟩
  simpa only [pairWords,vector,sourceType,ite_true] using represented
end Itasca.Runtime.Interp
