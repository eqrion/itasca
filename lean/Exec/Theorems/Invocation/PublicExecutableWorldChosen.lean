import Exec.Theorems.Invocation.PublicExecutableWorldDivergence
import Exec.Theorems.Invocation.PublicExecutableWorldSourceTyping

/-! Concrete divergence from a typed public entry admits a single fixed source
policy. The policy is existential; compatibility with a specified platform
policy and termination of that one selected source run remain separate. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem invoke_executable_world_infinite_choices {M P F A : Type}
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
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (sourceFunction : funcinst) (params resultsTypes : List valtype)
    (sourceAt : (Store.decodeStore view code store).FUNCS[address.index.val]?=some sourceFunction)
    (sourceType : sourceFunction.TYPE=.mk_functype (.mk_list params) (.mk_list resultsTypes))
    (typedArguments : ResultsTyped (Store.decodeStore view code store) params (args.val.map sourceValue))
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results=.div) :
    ∃ choices : Spec.SourceChoices, choices.Admissible ∧ Spec.InfiniteChosenSource choices 0 initial := by
  have typed := valid.invoked_config_typed invoked sourceAt sourceType typedArguments
  have infinite := invoke_executable_world_infinite_source memory hooks floats allocator correct allocation
    interrupts view laws code sound preserve externs issuedResults exec store platform valid address args results
    issued argumentIssued initial invoked divergent
  exact Spec.typed_infinite_choices typed infinite

end Exec.Theorems
