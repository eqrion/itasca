import Exec.Abs.ReferenceBounds
import Exec.Interp.Relations.Readback
import Exec.Representation.Values
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Issued API references fit the decoder's address space on both supported
pointer widths; numeric values carry no address obligation. -/
theorem sourceValue_reference_bound (store : Usize) (value : runtime.Value)
    (owned : ValueOwnedFits store value) :
    Abs.ReferenceBound Usize.max (sourceValue value) := by
  cases value <;> try trivial
  case FuncRef address =>
    cases address with
    | none => trivial
    | some address => exact owned.2.1
  case ExternRef address =>
    cases address with
    | none => trivial
    | some address => exact owned.2.1

theorem sourceValues_reference_bound (store : Usize) (values : List runtime.Value)
    (owned : ∀ value ∈ values, ValueOwnedFits store value) :
    Abs.ValuesBound Usize.max (values.map sourceValue) := by
  intro value member
  obtain ⟨raw, present, rfl⟩ := List.mem_map.mp member
  exact sourceValue_reference_bound store raw (owned raw present)

/-- The actual invocation entry gets its references only from owned arguments;
new locals are numeric zeroes or null references. -/
theorem entry_reference_bound (store : Usize) (sourceStore : _root_.store) (ambient : frame)
    (address : funcaddr) (moduleInst : moduleinst) (results : List valtype) (body : List instr)
    (args : List runtime.Value) (locals : List «local») (defaults : List val)
    (owned : ∀ value ∈ args, ValueOwnedFits store value)
    (created : Abs.defaultLocals locals = some defaults) :
    Abs.StateReferencesBound Usize.max
      (Abs.entryState sourceStore ambient address moduleInst results body (args.map sourceValue) defaults) := by
  refine ⟨Abs.valuesBound_nil _, ?_⟩
  intro frame member
  simp only [Abs.entryState, List.mem_singleton] at member
  subst frame
  exact ⟨Abs.valuesBound_append.mpr ⟨sourceValues_reference_bound store args owned,
    Abs.defaultLocals_reference_bound created⟩, Abs.valuesBound_nil _⟩

/-- A retained source reference bound discharges the concrete result decoder's
usize conversion, including its nonzero reference sentinel. -/
theorem resultIndexFits_of_reference_bound (value : val)
    (bounded : Abs.ReferenceBound Usize.max value) : ResultIndexFits value := by
  cases value <;> simp_all [Abs.ReferenceBound, ResultIndexFits] <;> omega

theorem results_fit_of_bound (values : List val)
    (bounded : Abs.ValuesBound Usize.max values) : ∀ value ∈ values, ResultIndexFits value :=
  fun value member => resultIndexFits_of_reference_bound value (bounded value member)
end Exec.Interp
