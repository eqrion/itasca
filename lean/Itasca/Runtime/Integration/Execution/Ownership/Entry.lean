import Itasca.Runtime.SourceMachine.Ownership.Core
import Itasca.Runtime.Store.Invariant.ValueShape
import Itasca.Runtime.Interp.Relations.ReferenceArguments
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The two reference namespaces are measured independently. -/
def ownershipBounds {M : Type} (store : runtime.store.Store M) : SourceMachine.Ownership.Bounds :=
  ⟨store.funcs.length,store.externs.length⟩

theorem source_value_owned {M : Type} (store : runtime.store.Store M) (value : runtime.Value)
    (owned : ValueInStore store value) :
    SourceMachine.Ownership.ValueOwned (ownershipBounds store) (Interp.sourceValue value) := by
  cases value <;> try trivial
  case FuncRef address =>
    cases address with
    | none => trivial
    | some address => exact owned.2
  case ExternRef address =>
    cases address with
    | none => trivial
    | some address => exact owned.2

theorem source_values_owned {M : Type} (store : runtime.store.Store M) (values : List runtime.Value)
    (owned : ∀ value ∈ values, ValueInStore store value) :
    SourceMachine.Ownership.ValuesOwned (ownershipBounds store) (values.map Interp.sourceValue) := by
  intro value member
  obtain ⟨raw, present, rfl⟩ := List.mem_map.mp member
  exact source_value_owned store raw (owned raw present)

theorem global_value_owned {M : Type} (store : runtime.store.Store M)
    (global : runtime.store.GlobalInst) (shape : GlobalShape store global) :
    SourceMachine.Ownership.ValueOwned (ownershipBounds store) (decodeGlobal global).VALUE := by
  cases type : global.ty.valtype <;>
    simp only [GlobalShape,type] at shape <;>
    simp only [decodeGlobal,decodeWords,type]
  all_goals try trivial
  all_goals
    obtain ⟨reference,high⟩ := shape
    unfold ReferenceShape at reference
    rcases reference with zero | bound
    · simp [decodeRef,zero,refVal,SourceMachine.Ownership.ValueOwned]
    · by_cases zero : global.lo.val = 0
      · simp [decodeRef,zero,refVal,SourceMachine.Ownership.ValueOwned]
      · simpa only [decodeRef,if_neg zero,refVal,SourceMachine.Ownership.ValueOwned,ownershipBounds] using bound

theorem Shape.globals_owned {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    (shape : Shape view store) (code : CodeInterpretation) :
    SourceMachine.Ownership.GlobalsOwned (ownershipBounds store) (decodeStore view code store) := by
  intro object member
  obtain ⟨raw,present,rfl⟩ := List.mem_map.mp member
  exact global_value_owned store raw (shape.globals raw present)

theorem owned_reference_bound {M : Type} (store : runtime.store.Store M) (value : val)
    (owned : SourceMachine.Ownership.ValueOwned (ownershipBounds store) value) :
    SourceMachine.ReferenceBound Usize.max value := by
  cases value <;> try trivial
  case REF_FUNC_ADDR address =>
    have bound : store.funcs.length ≤ Usize.max := by scalar_tac
    exact Nat.lt_of_lt_of_le owned bound
  case REF_HOST_ADDR address =>
    have bound : store.externs.length ≤ Usize.max := by scalar_tac
    exact Nat.lt_of_lt_of_le owned bound

theorem owned_result_fits {M : Type} (store : runtime.store.Store M) (value : val)
    (owned : SourceMachine.Ownership.ValueOwned (ownershipBounds store) value) : Interp.ResultIndexFits value :=
  Interp.result_index_fits_of_reference_bound value (owned_reference_bound store value owned)
end Itasca.Runtime.Store
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std

/-- Issued arguments, default locals, and actual stored globals establish the
reference provenance preserved by mutable scalar execution. -/
theorem core_entry_owned {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} (shape : Store.Shape view store)
    (ambient : frame) (address : funcaddr) (moduleInst : moduleinst) (results : List valtype)
    (body : List instr) (args : List runtime.Value) (locals : List «local») (defaults : List val)
    (owned : ∀ value ∈ args, Store.ValueInStore store value)
    (created : SourceMachine.defaultLocals locals = some defaults) :
    SourceMachine.Ownership.CoreOwned (Store.ownershipBounds store)
      (SourceMachine.entryState (Store.decodeStore view code store) ambient address moduleInst results body
        (args.map Interp.sourceValue) defaults) := by
  refine ⟨⟨SourceMachine.Ownership.values_owned_nil _,?_⟩,shape.globals_owned code⟩
  intro frame member
  simp only [SourceMachine.entryState,List.mem_singleton] at member
  subst frame
  exact ⟨SourceMachine.Ownership.values_owned_append.mpr ⟨Store.source_values_owned store args owned,
    SourceMachine.Ownership.default_locals_ownership created⟩,SourceMachine.Ownership.values_owned_nil _⟩
end Itasca.Runtime.Integration
