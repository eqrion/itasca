import Exec.Theorems.Composition.Entry
import Exec.Theorems.Composition.Certified.CertifiedCore
import Exec.Theorems.Composition.Core.CoreOwnership
import Exec.Interp.Machines.Core.CoreCallStackEntry
import Exec.Interp.Machines.Core.CoreCallLookup
import Exec.Interp.Core.Execution
import Exec.Abs.Core.Invoke
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- A real defined-function call establishes the complete mutable-machine entry
from checked arguments and retained source/compiler certificates. -/
theorem call_defined_core_entry_certified {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedCoreStore view code store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value)
    (empty : before.frames.val = []) (identity : before.store = store.id)
    (arguments : Interp.ValuesAt before.slots.val 0 (args.val.map Interp.sourceValue))
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex) :
    runtime.interp.call memory hooks floats allocator before store platform address 0#usize ⦃ out =>
      out.2.2.1 = store ∧ (out.1 = .Ok () → ∃ entry,
        Interp.CoreExecution view code store out.2.1 entry
          (signature.results.val.map Interp.sourceType) 0 false ∧
        Abs.Ownership.CoreOwned (Store.ownershipBounds store) entry ∧
        entry.ambient = ambient ∧
        StepH ⟨⟨Store.decodeStore view code store, ambient⟩,
          vals (args.val.map Interp.sourceValue) ++ [.CALL_ADDR address.index.val]⟩ [] (Abs.decode entry)) ⦄ := by
  obtain ⟨inst,compiled,actualSignature,declared,body,epilogue,hi,hc,actualHs,table,certificate,bindings,lookup⟩ :=
    certified.compiled.defined view certified.typed address function instanceIndex functionIndex hf hw
  have same : actualSignature = signature := Option.some.inj (actualHs.symm.trans hs)
  subst actualSignature
  have storeWf := Store.decodeStore_wf view code store certified.shape certified.storeSyntax
  have argumentTypes := checked_arguments_typed memory view code store storeWf args signature.params accepted owned
  obtain ⟨defaults,default,typed,covered,sourceStep⟩ := Abs.defined_core_invocation
    (Store.decodeStore view code store) ambient address.index.val (Store.decodeInstance store inst)
    (.mk_uN compiled.type_index.val) (signature.params.val.map Interp.sourceType)
    (signature.results.val.map Interp.sourceType) (declared.map local.LOCAL) body
    (args.val.map Interp.sourceValue) storeWf ambientWf certified.functions_typed certified.core lookup argumentTypes
  have tags := checked_argument_type_tags memory store args signature.params accepted
  apply WP.spec_mono (Interp.call_wasm_core_stack memory hooks floats allocator allocation interrupts
    before store platform address 0#usize function signature instanceIndex functionIndex inst compiled epilogue
    (Store.decodeStore view code store)
    (Code.moduleFunctionContext inst.module (signature.params.val.map Interp.sourceType++declared)
      (signature.results.val.map Interp.sourceType)) bindings declared body
    (args.val.map Interp.sourceValue) defaults certificate hf hs hw hi hc table identity
    arguments tags default [] [] empty (.nil _))
  intro out result
  refine ⟨result.1,fun success => ?_⟩
  obtain ⟨stack,top,ready⟩ := result.2 success
  obtain ⟨pc,cursor⟩ := ready.cursor
  have zero : pc = 0 := by
    have position := cursor.pc
    simp only [top,Option.map_some,Option.some.injEq] at position
    scalar_tac
  subst pc
  refine ⟨_,?_,?_,rfl,sourceStep⟩
  · exact ⟨rfl,⟨typed,certified.contents_typed⟩,covered,Abs.entry_result _ _ _ _ _ _ _ _,stack,cursor⟩
  · exact core_entry_owned certified.shape ambient address.index.val (Store.decodeInstance store inst)
      (signature.results.val.map Interp.sourceType) body args.val (declared.map local.LOCAL) defaults owned default
end Exec.Theorems
