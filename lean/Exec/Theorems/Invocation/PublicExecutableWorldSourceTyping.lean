import Exec.Theorems.Invocation.PublicExecutableWorldResources
import Exec.Spec.Typing.InvocationTyping
import Exec.Spec.Typing.ChoiceTypingPreservation

/-! Public typed invocation entries retain source configuration typing and
admit coherent source policies for their entire recorded correspondence. -/

/-! Source typing derived from the public invariant and recorded correspondence.
No source-store typing certificate field is added. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem ExecutableInv.invoked_config_typed {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (valid : ExecutableInv view code store) {address : Nat} {args : List val} {initial : config}
    (invoked : fun_invoke (Store.decodeStore view code store) address args initial)
    {sourceFunction : funcinst} {params results : List valtype}
    (sourceAt : (Store.decodeStore view code store).FUNCS[address]?=some sourceFunction)
    (sourceType : sourceFunction.TYPE=.mk_functype (.mk_list params) (.mk_list results))
    (arguments : ResultsTyped (Store.decodeStore view code store) params args) :
    Config_ok initial (.mk_list results) := by
  have bound := (List.getElem?_eq_some_iff.mp sourceAt).1
  have signature : (Store.decodeStore view code store).FUNCS[address]!.TYPE=.mk_functype (.mk_list params) (.mk_list results) := by
    simp only [List.getElem!_eq_getElem?_getD,sourceAt,Option.getD_some,sourceType]
  exact Spec.invoked_config_ok valid.source_typed bound signature arguments invoked

theorem ExecutableInv.invocation_prefix_typed {M : Type} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    (valid : ExecutableInv view code store) {address : Nat} {args : List val} {initial : config}
    (invoked : fun_invoke (Store.decodeStore view code store) address args initial)
    {sourceFunction : funcinst} {params results : List valtype}
    (sourceAt : (Store.decodeStore view code store).FUNCS[address]?=some sourceFunction)
    (sourceType : sourceFunction.TYPE=.mk_functype (.mk_list params) (.mk_list results))
    (arguments : ResultsTyped (Store.decodeStore view code store) params args)
    {events : List HostEvent} {after : config} (history : StepsH initial events after) :
    Config_ok after (.mk_list results) :=
  Spec.stepsH_config_preserved history (valid.invoked_config_typed invoked sourceAt sourceType arguments)

/-- The exact recorded successful invocation has a source-typed final
configuration and one admissible policy for its complete eventful source run. -/
theorem ExecutableWorldRecordedOutcome.success_typed_choices {M P : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {before : runtime.store.Store M}
    {exec : runtime.interp.Execution} {platform : P} {buffer : alloc.vec.Vec runtime.Value}
    {initial : config} {out} {events : List HostEvent}
    (outcome : ExecutableWorldRecordedOutcome view code before exec platform buffer initial out events)
    {types : resulttype} (typed : Config_ok initial types) (returned : out.1=.Ok ()) (occurrence : Nat) :
    ∃ afterCode, Store.CodeAgreesOn before code afterCode ∧ ExecutableInv view afterCode out.2.2.1 ∧
      Config_ok ⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,
        vals (out.2.2.2.2.val.map sourceValue)⟩ types ∧
      ∃ choices : Spec.SourceChoices, choices.Admissible ∧
        Spec.ChoiceSteps choices occurrence initial events
          ⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩ := by
  obtain ⟨afterCode,agrees,valid,_,_,_,success,_⟩ := outcome
  have run := (success returned).1
  exact ⟨afterCode,agrees,valid,Spec.stepsH_config_preserved run typed,Spec.typed_run_choices run typed occurrence⟩
end Exec.Theorems
