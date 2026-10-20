import Exec.Interp.Host.OpenWasmPreparation
import Exec.Theorems.Composition.Supported.SupportedEntryOutcomes
import Exec.Theorems.Api.ExecutableInv
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- A checked root Wasm call prepares an ordinary entry world or reports an
actual resource/interrupt cause. No host callback is invoked by this entry. -/
theorem prepare_defined_entry {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform Unit M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before : runtime.interp.Execution) (store : runtime.store.Store M) (platform : Unit)
    (held : ExecutableInv view code store) (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (instanceIndex functionIndex : Usize) (args : Slice runtime.Value)
    (empty : before.frames.val=[]) (identity : before.store=store.id)
    (arguments : ValuesAt before.slots.val 0 (args.val.map sourceValue))
    (accepted : runtime.interp.check_values memory store args signature.params.deref=.ok (.Ok ()))
    (owned : ∀value∈args.val,Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]?=some function) (hs : store.types.val[function.signature.val]?=some signature)
    (hw : function.code=.Wasm instanceIndex functionIndex) :
    prepareCall memory hooks floats allocator before store platform address 0#usize ⦃phase=>
      ∃out,phase=.done out ∧ out.2.2.1=store ∧
        (out.1=.Ok () → ∃entry,
          StructuredMachine.Execution Executable.emission (Abs.SupportedState Abs.ExecutableInstr)
            view code store out.2.1 entry (signature.results.val.map sourceType) 0 false ∧
          Abs.Ownership.StatefulOwned (Store.ownershipBounds store) entry ∧ entry.ambient=ambient ∧
          StepH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ [] (Abs.decode entry)) ∧
        (∀error,out.1=.Err error → ∃inst compiled,store.instances.val[instanceIndex.val]?=some inst ∧
          inst.module.functions.val[functionIndex.val]?=some compiled ∧ CallCause allocator hooks before store platform 0#usize compiled error) ⦄ := by
  have certified := held.toCertifiedApiStore.toCertifiedSupportedStore
  obtain ⟨out,actual,unchanged,entered,errors⟩ := WP.spec_imp_exists
    (call_defined_supported_entry_outcomes memory hooks floats allocator allocation interrupts view code before store platform
      certified.shape certified.storeSyntax certified.segmentBounds certified.typed certified.supported certified.compiled ambient ambientWf
      address function signature instanceIndex functionIndex args empty identity arguments accepted owned hf hs hw)
  rw [prepareCall_wasm memory hooks floats allocator before store platform address 0#usize function instanceIndex functionIndex hf hw (interrupts platform)]
  simp only [completed,actual,bind_ok]
  exact WP.spec.ret ⟨out,rfl,unchanged,entered,errors⟩
end Exec.Theorems.OpenReentrantControl
