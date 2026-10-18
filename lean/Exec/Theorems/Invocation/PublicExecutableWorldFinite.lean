import Exec.Theorems.Progress.ExecutableWorldEntryFinite
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Finite progress for an issued public defined-call prefix. The premises
record the actual signature/argument checks and prepared slot state; all raw
function/signature lookup and source-entry certificates are derived internally.
The count is interpreter-loop dispatches, excluding public setup/readback. -/
theorem call_executable_world_issued_finite_progress {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (prepared : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀ value ∈ args.val, Store.IssuedValue store value)
    (signature : Itasca.types.FuncType)
    (lookup : runtime.store.Store.func_type memory store address = .ok (.Ok signature))
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (instanceIndex functionIndex : Usize)
    (defined : (store.funcs.val[address.index.val]?).map (fun f => f.code) = some (.Wasm instanceIndex functionIndex))
    (empty : prepared.frames.val = []) (identity : prepared.store = store.id)
    (arguments : ValuesAt prepared.slots.val 0 (args.val.map sourceValue))
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    runtime.interp.call memory hooks floats allocator prepared store platform address 0#usize ⦃ out =>
      out.2.2.1 = store ∧ (out.1 = .Ok () → ∀dispatches last,
        ContinuingTrace (executionBody memory hooks floats allocator) dispatches
          (out.2.1,out.2.2.1,out.2.2.2,.Ok ()) last →
        ∃target events count, Spec.StepsHN count initial events target ∧
          dispatches / (2 * U32.max + 3) ≤ count) ⦄ := by
  have owner : address.store = store.id := by
    by_contra foreign
    simp [runtime.store.Store.func_type,runtime.store.Store.check,foreign,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,bind_ok] at lookup
  have bound : address.index.val < store.funcs.val.length := issued owner
  let function := store.funcs.val[address.index.val]
  have hf : store.funcs.val[address.index.val]? = some function := List.getElem?_eq_getElem bound
  have signatureBound : function.signature.val < store.types.val.length :=
    (valid.shape.functions function (List.mem_of_getElem? hf)).1
  let actualSignature := store.types.val[function.signature.val]
  have hs : store.types.val[function.signature.val]? = some actualSignature := List.getElem?_eq_getElem signatureBound
  have same := func_type_lookup memory store address function actualSignature owner hf hs
  rw [lookup] at same
  have eqSig : signature = actualSignature := by simpa only [WP.spec_ok,core.result.Result.Ok.injEq] using same
  have hsSignature : store.types.val[function.signature.val]? = some signature :=
    hs.trans (congrArg some eqSig.symm)
  have hw : function.code = .Wasm instanceIndex functionIndex := by simpa only [hf,Option.map_some,Option.some.injEq] using defined
  have owned := Store.checked_arguments_owned memory view code store valid.well_formed
    args (alloc.vec.Vec.deref signature.params) argumentIssued accepted
  have result := call_defined_executable_world_finite_progress memory hooks floats allocator correct allocation
    interrupts view laws code sound preserve externs issuedResults prepared store platform valid
    Spec.invocationFrame (Spec.invocation_frame_wf invoked) address function signature instanceIndex functionIndex args
    empty identity arguments accepted owned hf hsSignature hw
  simpa only [Spec.invocation_config invoked] using result
end Exec.Theorems
