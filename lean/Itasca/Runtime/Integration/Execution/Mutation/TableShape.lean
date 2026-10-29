import Itasca.Runtime.Interp.State.TableMutation
import Itasca.Runtime.Spec.TableWriteBounds
import Itasca.Runtime.Integration.Execution.Dispatch.Arguments
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Interp.Calls.CallRefinement
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Interp.Calls.CallStack
import Itasca.Runtime.Interp.Machine.Frames.Reposition
import Itasca.Runtime.Interp.Machine.History.Append
import Itasca.Runtime.Interp.Relations.Readback
import Itasca.Runtime.SourceMachine.Results
import Itasca.Runtime.Interp.Invocation.Checks
import Itasca.Runtime.Interp.Relations.Marshal
import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Interp.Relations.TypeSlots
import Itasca.Runtime.Interp.Relations.Ensure
import Itasca.Runtime.Interp.Relations.ExecutionLoop
import Itasca.Runtime.Interp.Machine.Resources.CallErrors
import Itasca.Runtime.Interp.Invocation.Divergence
import Itasca.Runtime.Interp.Machine.Progress.ActiveLoop
import Itasca.Runtime.Interp.Relations.TypedArguments
import Itasca.Runtime.Spec.Invocation
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Store.Invariant.FunctionTables
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.Interp.Machine.Functions.Typing
import Itasca.Runtime.SourceMachine.Core
import Itasca.Runtime.Integration.Execution.Ownership.Contents
import Itasca.Runtime.Interp.Relations.CompiledFunctions
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunctionContext
import Itasca.Runtime.Store.Invariant.CoreTypingExtension
import Itasca.Runtime.Store.Invariant.FunctionCapacities
import Itasca.Runtime.Store.Invariant.ObjectExtension
import Itasca.Runtime.Store.Invariant.SemanticApi
namespace Itasca.Runtime.Integration
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
  have oldWf := decode_store_wf view code before shape syntaxProof
  have newWf := decode_store_wf view code after fresh sourceSyntax
  have oldTableWf : wf_tableinst (decodeTable object) := by
    apply wf_tableinst.tableinst_case_
    apply wf_tabletype.tabletype_case_0
    exact decode_limits_wf _ _ (shape.tables object (List.mem_of_getElem? issued)).1
  have newTableWf : wf_tableinst (decodeTable {object with elements := words}) := by
    apply wf_tableinst.tableinst_case_
    apply wf_tabletype.tabletype_case_0
    apply decode_limits_wf
    simpa only [lengthEq] using (shape.tables object (List.mem_of_getElem? issued)).1
  have objectExtension := decode_table_extends object {object with elements := words}
    rfl rfl (Nat.le_of_eq lengthEq.symm) oldTableWf newTableWf
  refine ⟨fresh,?_⟩
  unfold after at newWf
  rw [decode_store_table_update view code before (before.tables.set address.index {object with elements := words})] at newWf ⊢
  simp only [alloc.vec.Vec.set_val_eq,List.map_set] at newWf ⊢
  apply Spec.extend_store_set_table _ _ _ oldWf
  · simpa only [decodeStore] using newWf
  · intro indexBound
    simpa only [decodeStore,found,
      getElem!_pos (before.tables.val.map decodeTable) address.index.val
        (by simpa only [List.length_map] using bound),List.getElem_map] using objectExtension

end Itasca.Runtime.Integration
