import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.SourceMachine.Ownership.Extension
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.SourceMachine.Stateful.Bound
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.Store.Invariant.CodeAgreement
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Initialization.SegmentExtension

/-!
Sections, each formerly its own module: Contents, Entry, StoreOperations, Publication.
-/

/-! ## Contents -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Actual owned store shape supplies every non-function source payload typing
fact required by mutable scalar execution. -/
theorem decode_store_contents_typed {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (store : runtime.store.Store M)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (segments : SegmentBounds store) :
    SourceMachine.StoreContentsTyped (decodeStore view code store) := by
  obtain ⟨globals,tables,memories,elements,data⟩ := decoded_components_typed view code store shape sourceSyntax segments
  exact ⟨globals,tables,memories,elements,data⟩

end Itasca.Runtime.Store

end

/-! ## Entry -/

section

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

end

/-! ## StoreOperations -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem reference_value_owned {M : Type} (store : runtime.store.Store M)
    (type : Itasca.wasm_types.ElemType) (word : U64) (shape : ReferenceShape store type word) :
    SourceMachine.Ownership.ValueOwned (ownershipBounds store) (val_ref (decodeRef type word)) := by
  cases type <;> unfold ReferenceShape at shape
  all_goals
    by_cases zero : word.val = 0
    · simp [decodeRef,zero,val_ref,SourceMachine.Ownership.ValueOwned]
    · have bound := shape.resolve_left zero
      simpa only [decodeRef,if_neg zero,val_ref,SourceMachine.Ownership.ValueOwned,ownershipBounds] using bound

theorem Shape.stateful_heap_owned {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    (shape : Shape view store) (code : CodeInterpretation) :
    SourceMachine.Ownership.StatefulHeapOwned (ownershipBounds store) (decodeStore view code store) := by
  refine ⟨shape.globals_owned code,?_,?_,?_⟩
  · intro object member reference present
    obtain ⟨raw,rawMember,rfl⟩ := List.mem_map.mp member
    obtain ⟨word,wordMember,rfl⟩ := List.mem_map.mp present
    exact reference_value_owned store raw.ty word ((shape.tables raw rawMember).2.2 word wordMember)
  · intro object member reference present
    obtain ⟨raw,rawMember,rfl⟩ := List.mem_map.mp member
    obtain ⟨word,wordMember,rfl⟩ := List.mem_map.mp present
    exact reference_value_owned store raw.ty word (shape.elements raw rawMember word wordMember)
  · simp [decodeStore,ownershipBounds]
end Itasca.Runtime.Store
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std

theorem stateful_entry_owned {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} (shape : Store.Shape view store)
    (ambient : frame) (address : funcaddr) (moduleInst : moduleinst) (results : List valtype)
    (body : List instr) (args : List runtime.Value) (locals : List «local») (defaults : List val)
    (owned : ∀ value ∈ args,Store.ValueInStore store value)
    (created : SourceMachine.defaultLocals locals = some defaults) :
    SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store)
      (SourceMachine.entryState (Store.decodeStore view code store) ambient address moduleInst results body
        (args.map Interp.sourceValue) defaults) :=
  ⟨(core_entry_owned shape ambient address moduleInst results body args locals defaults owned created).values,
    shape.stateful_heap_owned code⟩
end Itasca.Runtime.Integration

end

/-! ## Publication -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv

/-- The installed source subset is preserved for old functions and established
for every new defined function by its actual source index. -/
theorem store_supported_publish {M : Type} (view : M → Slice U8)
    (before after : runtime.store.Store M) (oldCode : CodeInterpretation)
    (shape : Shape view before) (retained : StagedPrefix before after)
    (oldSlice : SourceMachine.FunctionsSupported (decodeStore view oldCode before))
    (inst : runtime.store.ModuleInst) (sources : List funccode)
    (sourceCount : sources.length = inst.module.module.env.func_type_indices.val.length)
    (supported : ∀ source ∈ sources, match source with
      | .HOST _ => False | .FUNC _ _ body => Forall SourceMachine.BinaryInstr body)
    (found : after.instances.val[before.instances.len.val]? = some inst)
    {tables memories} (cache : Cache inst.module.module.env tables memories)
    (staged : StagedFunctionSignatures before after before.instances.len
      (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length)) :
    SourceMachine.FunctionsSupported (decodeStore view (installCode oldCode before.instances.len.val sources) after) := by
  intro decoded present
  obtain ⟨function, member, rfl⟩ := List.mem_map.mp present
  rcases staged function member with old | ⟨index, bound, encoded, signature⟩
  · rw [decode_function_prefix _ before after retained view shape function old]
    simp only [alloc.vec.Vec.len_val]
    rw [decode_function_code_agrees (install_code_agrees before oldCode sources) function]
    exact oldSlice _ (List.mem_map.mpr ⟨function, old, rfl⟩)
  · have resolves := List.forall₂_drop (importedFuncs inst.module.module.env.imports.val).length cache.funcs
    have count : inst.module.module.env.func_type_indices.val.length =
        (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length).length := by
      simpa only [List.drop_left] using resolves.length_eq
    have sourceBound : index.val < sources.length := by rw [sourceCount, count]; exact bound
    let source := sources[index.val]
    have sourceFound : sources[index.val]? = some source := List.getElem?_eq_getElem sourceBound
    have known := supported source (List.mem_of_getElem? sourceFound)
    simp only [decodeFunction, encoded, found,
      install_code_lookup oldCode before.instances.len.val sources inst.module index.val source sourceFound]
    cases same : source <;> simpa only [same] using known

end Itasca.Runtime.Store

end
