import Exec.Spec.Choices.NumericDeterminism
import Exec.Spec.Wf

/-! Choice-indexed scalar numeric reductions. The permitted result list comes
from the source operator rules, independently of any concrete interpreter. -/
namespace Exec.Spec

inductive NumericRequest where
  | unary (type : numtype) (op : unop_) (input : num_)
  | binary (type : numtype) (op : binop_) (left right : num_)
  | convert (source target : numtype) (op : cvtop__) (input : num_)

def NumericRequest.type : NumericRequest → numtype
  | .unary type _ _ => type
  | .binary type _ _ _ => type
  | .convert _ target _ _ => target

def NumericRequest.instructions : NumericRequest → List admininstr
  | .unary type op input => [.CONST type input,.UNOP type op]
  | .binary type op left right => [.CONST type left,.CONST type right,.BINOP type op]
  | .convert source target op input => [.CONST source input,.CVTOP target source op]

/-- Independent generated operator judgment, including well-formed redex and
result representations. An empty permitted list denotes the specified trap. -/
inductive NumericRequest.Allowed : NumericRequest → List num_ → Prop
  | unary {type op input results}
      (source : fun_unop_ type op input (some results))
      (inputWf : wf_admininstr (.CONST type input)) (opWf : wf_admininstr (.UNOP type op))
      (resultsWf : ∀ value ∈ results, wf_admininstr (.CONST type value)) :
      Allowed (.unary type op input) results
  | binary {type op left right results}
      (source : fun_binop_ type op left right (some results))
      (leftWf : wf_admininstr (.CONST type left)) (rightWf : wf_admininstr (.CONST type right))
      (opWf : wf_admininstr (.BINOP type op))
      (resultsWf : ∀ value ∈ results, wf_admininstr (.CONST type value)) :
      Allowed (.binary type op left right) results
  | convert {source target op input results}
      (relation : fun_cvtop__ source target op input (some results))
      (inputWf : wf_admininstr (.CONST source input)) (opWf : wf_admininstr (.CVTOP target source op))
      (resultsWf : ∀ value ∈ results, wf_admininstr (.CONST target value)) :
      Allowed (.convert source target op input) results

theorem NumericRequest.allowed_unique {request : NumericRequest} {left right : List num_}
    (first : request.Allowed left) (second : request.Allowed right) : left = right := by
  cases first <;> cases second
  · exact numeric_unop_results_unique (by assumption) (by assumption)
  · exact numeric_binop_results_unique (by assumption) (by assumption)
  · exact numeric_cvtop_results_unique (by assumption) (by assumption)

/-- A policy sees the operation, its occurrence, and its independently
permitted results. This permits different NaN choices at repeated operations. -/
abbrev NumericChoices := Nat → NumericRequest → List num_ → Option num_

def NumericChoices.Admissible (choices : NumericChoices) : Prop :=
  ∀ occurrence request allowed, request.Allowed allowed →
    (choices occurrence request allowed = none ↔ allowed = []) ∧
    ∀ value, choices occurrence request allowed = some value → value ∈ allowed

def numericOutput (type : numtype) : Option num_ → List admininstr
  | none => [.TRAP]
  | some value => [.CONST type value]

/-- The policy must consume the permitted list of this exact source redex. -/
inductive ChosenNumeric (choices : NumericChoices) (occurrence : Nat) (request : NumericRequest) :
    Option num_ → Prop
  | selected (allowed : List num_) (source : request.Allowed allowed) :
      ChosenNumeric choices occurrence request (choices occurrence request allowed)

/-- Selected source choices erase to the ordinary scalar numeric reduction. -/
theorem ChosenNumeric.erases {choices : NumericChoices} (admissible : choices.Admissible)
    {occurrence request result} (chosen : ChosenNumeric choices occurrence request result) :
    Step_pure request.instructions (numericOutput request.type result) := by
  cases chosen with
  | selected allowed source =>
    obtain ⟨empty,member⟩ := admissible occurrence request allowed source
    generalize selected : choices occurrence request allowed = result at empty member ⊢
    cases source with
    | unary source inputWf opWf resultsWf =>
      cases result with
      | none =>
        have nil := empty.mp rfl
        subst allowed
        exact .unop_trap _ _ _ (some []) source (by simp) rfl inputWf opWf .admininstr_case_73
      | some value =>
        have permitted := member value rfl
        exact .unop_val _ _ _ _ (some allowed) source (List.length_pos_of_mem permitted)
          (by simp) (by simpa only [Option.get!_some,List.contains_iff_mem] using permitted)
          inputWf opWf (resultsWf value permitted)
    | binary source leftWf rightWf opWf resultsWf =>
      cases result with
      | none =>
        have nil := empty.mp rfl
        subst allowed
        exact .binop_trap _ _ _ _ (some []) source (by simp) rfl leftWf rightWf opWf .admininstr_case_73
      | some value =>
        have permitted := member value rfl
        exact .binop_val _ _ _ _ _ (some allowed) source (List.length_pos_of_mem permitted)
          (by simp) (by simpa only [Option.get!_some,List.contains_iff_mem] using permitted)
          leftWf rightWf opWf (resultsWf value permitted)

    | convert source inputWf opWf resultsWf =>
      cases result with
      | none =>
        have nil := empty.mp rfl
        subst allowed
        exact .cvtop_trap _ _ _ _ (some []) source (by simp) rfl inputWf opWf .admininstr_case_73
      | some value =>
        have permitted := member value rfl
        exact .cvtop_val _ _ _ _ _ (some allowed) source (List.length_pos_of_mem permitted)
          (by simp) (by simpa only [Option.get!_some,List.contains_iff_mem] using permitted)
          inputWf opWf (resultsWf value permitted)

/-- Fixed policies and occurrences determine the selected outcome, even when
floating-point source rules permit multiple bit patterns. -/
theorem ChosenNumeric.deterministic {choices : NumericChoices} {occurrence request left right}
    (first : ChosenNumeric choices occurrence request left)
    (second : ChosenNumeric choices occurrence request right) : left = right := by
  cases first with
  | selected xs first =>
    cases second with
    | selected ys second => rw [NumericRequest.allowed_unique first second]

/-- A concrete source policy witnesses that the admissibility condition is
inhabited: choose the first permitted representation, or the specified trap. -/
def firstNumericChoice : NumericChoices := fun _ _ allowed => allowed.head?

theorem firstNumericChoice_admissible : firstNumericChoice.Admissible := by
  intro occurrence request allowed _
  cases allowed <;> simp [firstNumericChoice]

end Exec.Spec
