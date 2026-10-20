import Exec.Theorems.Host.Chosen.PureChosenCallbacks
import Exec.Store.Invariant.IssuedArguments
import Exec.Interp.Relations.TypedArguments
namespace Exec.Theorems.PureCallbacks
open Aeneas Aeneas.Std Exec.Interp SpecExt

/-- Source replies fold the callback syntax independently of its native
Platform evaluator. Ill-typed literal returns become source host traps. -/
def Program.sourceResult : Program → Option (List val)
  | .returned values => some (values.val.map (fun literal=>sourceValue literal.value))
  | .trapped => none
  | .branch condition yes no => if condition then yes.sourceResult else no.sourceResult

noncomputable def Program.sourceReply (program : Program) (before : store) (expected : List valtype) : Spec.HostReply := by
  classical
  exact ⟨before,match program.sourceResult with
    | none=>none
    | some values=>if ResultsTyped before expected values then some values else none⟩

noncomputable def Program.hostChoices (program : Program) : Spec.HostChoices :=
  fun _ before _ _ _ results _=>program.sourceReply before results

theorem Program.hostChoices_admissible (program : Program) : program.hostChoices.Admissible := by
  classical
  intro occurrence before address identity params results args typed host arguments
  have wf : wf_store before := by cases typed; assumption
  refine ⟨Spec.extend_store_refl before wf,typed,?_⟩
  intro values same
  simp only [Program.hostChoices,Program.sourceReply] at same
  cases selected : program.sourceResult with
  | none => simp [selected] at same
  | some returned =>
    by_cases accepted : ResultsTyped before results returned
    · simp only [selected,if_pos accepted,Option.some.injEq] at same
      exact same ▸ accepted
    · simp [selected,accepted] at same

theorem Program.ownedFits (program : Program) (identity : Usize) :
    ∀value∈program.evaluate.2.val,ValueOwnedFits identity value := by
  induction program with
  | returned values =>
    intro value member
    simp only [Program.evaluate,Slice.from_val,List.mem_map] at member
    obtain ⟨literal,_,rfl⟩ := member
    cases literal <;> trivial
  | trapped => simp [Program.evaluate]
  | branch condition yes no hy hn => cases condition <;> assumption

private theorem vec_deref_slice {T : Type} (values : alloc.vec.Vec T) : values.deref=values.slice := by
  apply Slice.ext
  simp only [alloc.vec.Vec.deref,Slice.from_val,alloc.vec.Vec.val]

private theorem checked_source_iff {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (wf : wf_store (Store.decodeStore view code store))
    (program : Program) (signature : Itasca.types.FuncType) :
    runtime.interp.check_values memory store program.evaluate.2 signature.results.slice=.ok (.Ok ()) ↔
      ResultsTyped (Store.decodeStore view code store) (signature.results.val.map sourceType) (program.evaluate.2.val.map sourceValue) := by
  constructor
  · intro accepted
    have post := Store.check_values_source_typed memory view code store wf program.evaluate.2 signature.results.slice (program.issued store)
    rw [accepted,WP.spec_ok] at post
    exact (post rfl).1
  · intro typed
    have accepted := typed_arguments_accepted memory store (Store.decodeStore view code store) program.evaluate.2 signature.results typed (program.ownedFits store.id)
    simpa only [vec_deref_slice] using accepted

private theorem Program.sourceResult_evaluate (program : Program) : program.sourceResult=
    match program.evaluate.1 with | .Ok _=>some (program.evaluate.2.val.map sourceValue) | .Err _=>none := by
  induction program with
  | returned values => simp only [Program.sourceResult,Program.evaluate,Slice.from_val,List.map_map,Function.comp_def]
  | trapped => rfl
  | branch condition yes no hy hn => cases condition <;> assumption

theorem Program.sourceReply_matches {M : Type} (program : Program) (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (wf : wf_store (Store.decodeStore view code store)) (signature : Itasca.types.FuncType) :
    program.sourceReply (Store.decodeStore view code store) (signature.results.val.map sourceType)=
      checkedHostReply memory view code store signature ⟨program.evaluate.2⟩ program.evaluate.1 := by
  classical
  have checked := checked_source_iff memory view code store wf program signature
  unfold Program.sourceReply checkedHostReply
  rw [Program.sourceResult_evaluate]
  cases status : program.evaluate.1 with
  | Err error => simp [status]
  | Ok unit =>
    cases unit
    simp only [true_and,alloc.vec.Vec.val]
    rw [checked]
    rfl

/-- Constant finite pure callbacks match a preselected independent source
policy, including typed numeric/null returns, branches and dynamic rejection. -/
theorem program_chosen_sound {M : Type} (memory : runtime.platform.MemoryBuffer M) (program : Program)
    (view : M → Slice U8) (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (typed : ∀code store,Inv code store → Store_ok (Store.decodeStore view code store))
    (choices : Spec.SourceChoices) (selected : choices.host=program.hostChoices) :
    HostWorldChosenSound memory (platform memory (fun _ _=>program)) view Inv choices := by
  intro occurrence code store held token identity args defaults
  have sourceTyped := typed code store held
  have wf : wf_store (Store.decodeStore view code store) := by cases sourceTyped; assumption
  refine WP.spec.ret ⟨code,(by intro index inst found fn; rfl),held,Spec.extend_store_refl _ wf,sourceTyped,?_⟩
  intro address function signature found host signatureFound
  rw [selected]
  exact program.sourceReply_matches memory view code store wf signature
end Exec.Theorems.PureCallbacks
