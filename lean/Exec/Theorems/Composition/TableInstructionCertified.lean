import Exec.Interp.State.TableMutation
import Exec.Spec.TableWriteBounds
import Exec.Theorems.Composition.Entry
import Exec.Code.Local.Relations.Common.Function
import Exec.Interp.Calls.CallRefinement
import Exec.Interp.Control.StructuredPoint
import Exec.Interp.Calls.CallStack
import Exec.Interp.Machines.Slice.SliceExecution
import Exec.Interp.Machines.Slice.SliceHistory
import Exec.Interp.Relations.Readback
import Exec.Abs.Results
import Exec.Interp.Invocation.InvokeChecks
import Exec.Interp.Relations.Marshal
import Exec.Representation.Collection
import Exec.Interp.Relations.TypeSlots
import Exec.Interp.Relations.Ensure
import Exec.Interp.Relations.ExecutionLoop
import Exec.Interp.Machines.Slice.SliceErrors
import Exec.Interp.Invocation.InvokeDivergence
import Exec.Interp.Machines.Slice.SliceDivergence
import Exec.Interp.Relations.TypedArguments
import Exec.Spec.Invocation
import Exec.Store.Invariant.Typing
import Exec.Store.Invariant.FunctionTables
import Exec.Abs.ModuleBindingsExtension
import Exec.Interp.Machines.Core.CoreFunctionTyping
import Exec.Abs.Core
import Exec.Theorems.Composition.Core.CoreContents
import Exec.Interp.Relations.CompiledFunctions
import Exec.Code.Local.Relations.Common.CoreFunctionContext
import Exec.Store.Invariant.CoreTypingExtension
import Exec.Store.Invariant.FunctionCapacities
import Exec.Store.Invariant.ObjectExtension
import Exec.Store.Invariant.SemanticApi
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp

theorem table_mutation_shape {M : Type} (view : M → Slice U8)
    (before after : runtime.store.Store M) (shape : Shape view before)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (replacement : U64)
    (issued : before.tables.val[address.index.val]? = some object)
    (mutation : TableMutation before after address object replacement)
    (reference : ReferenceShape before object.ty replacement) : Shape view after := by
  obtain ⟨words,rfl,lengthEq,references⟩ := mutation
  obtain ⟨bound,found⟩ := List.getElem?_eq_some_iff.mp issued
  have old := shape.tables object (List.mem_of_getElem? issued)
  apply shape.table_replace_same_length address.index bound {object with elements := words}
  · refine ⟨by simpa only [lengthEq] using old.1,by simpa only [lengthEq] using old.2.1,?_⟩
    intro word member
    rcases references word member with previous | changed
    · exact old.2.2 word previous
    · simpa only [changed] using reference
  · simpa only [found] using lengthEq

/-- Typed table content replacement retains decoded store extension. -/
theorem table_mutation_extends {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (before after : runtime.store.Store M)
    (shape : Shape view before) (syntaxProof : StoreSyntax code before)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (replacement : U64)
    (issued : before.tables.val[address.index.val]? = some object)
    (mutation : TableMutation before after address object replacement)
    (reference : ReferenceShape before object.ty replacement) :
    Shape view after ∧ Extend_store (decodeStore view code before) (decodeStore view code after) := by
  have fresh := table_mutation_shape view before after shape address object replacement issued mutation reference
  obtain ⟨words,rfl,lengthEq,references⟩ := mutation
  obtain ⟨bound,found⟩ := List.getElem?_eq_some_iff.mp issued
  let after := {before with tables := before.tables.set address.index {object with elements := words}}
  have sourceSyntax : StoreSyntax code after := syntaxProof
  have oldWf := decodeStore_wf view code before shape syntaxProof
  have newWf := decodeStore_wf view code after fresh sourceSyntax
  have oldTableWf : wf_tableinst (decodeTable object) := by
    apply wf_tableinst.tableinst_case_
    apply wf_tabletype.tabletype_case_0
    exact decodeLimits_wf _ _ (shape.tables object (List.mem_of_getElem? issued)).1
  have newTableWf : wf_tableinst (decodeTable {object with elements := words}) := by
    apply wf_tableinst.tableinst_case_
    apply wf_tabletype.tabletype_case_0
    apply decodeLimits_wf
    simpa only [lengthEq] using (shape.tables object (List.mem_of_getElem? issued)).1
  have objectExtension := decodeTable_extends object {object with elements := words}
    rfl rfl (Nat.le_of_eq lengthEq.symm) oldTableWf newTableWf
  refine ⟨fresh,?_⟩
  unfold after at newWf
  rw [decodeStore_table_update view code before (before.tables.set address.index {object with elements := words})] at newWf ⊢
  simp only [alloc.vec.Vec.set_val_eq,List.map_set] at newWf ⊢
  apply Spec.extend_store_set_table _ _ _ oldWf
  · simpa only [decodeStore] using newWf
  · intro indexBound
    simpa only [decodeStore,found,
      getElem!_pos (before.tables.val.map decodeTable) address.index.val
        (by simpa only [List.length_map] using bound),List.getElem_map] using objectExtension

end Itasca.Runtime.Theorems
