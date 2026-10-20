import Exec.Spec.Wf

/-! SIMD choices include lane-wise floating-point alternatives. In the pinned
source, vector conversion selects a permitted result inside `fun_vcvtop__`,
whereas unary/binary operators expose a list. Both forms need explicit choices. -/
namespace Exec.Spec

inductive VectorRequest where
  | unary (shape : _root_.shape) (op : vunop_) (input : vec_)
  | binary (shape : _root_.shape) (op : vbinop_) (left right : vec_)
  | convert (source target : _root_.shape) (op : vcvtop__) (input : vec_)

def VectorRequest.instructions : VectorRequest → List admininstr
  | .unary shape op input => [.VCONST .V128 input,.VUNOP shape op]
  | .binary shape op left right => [.VCONST .V128 left,.VCONST .V128 right,.VBINOP shape op]
  | .convert source target op input => [.VCONST .V128 input,.VCVTOP target source op]

def vectorOutput : Option vec_ → List admininstr
  | none => [.TRAP]
  | some value => [.VCONST .V128 value]

/-- Admissible results refer directly to independent generated numeric rules,
including lane products and permitted NaN representations. -/
inductive VectorResultAllowed : VectorRequest → Option vec_ → Prop
  | unary {shape op input allowed value}
      (source : fun_vunop_ shape op input (some allowed)) (member : value ∈ allowed)
      (inputWf : wf_admininstr (.VCONST .V128 input)) (opWf : wf_admininstr (.VUNOP shape op))
      (resultWf : wf_admininstr (.VCONST .V128 value)) :
      VectorResultAllowed (.unary shape op input) (some value)
  | unary_trap {shape op input}
      (source : fun_vunop_ shape op input (some []))
      (inputWf : wf_admininstr (.VCONST .V128 input)) (opWf : wf_admininstr (.VUNOP shape op)) :
      VectorResultAllowed (.unary shape op input) none
  | binary {shape op left right allowed value}
      (source : fun_vbinop_ shape op left right (some allowed)) (member : value ∈ allowed)
      (leftWf : wf_admininstr (.VCONST .V128 left)) (rightWf : wf_admininstr (.VCONST .V128 right))
      (opWf : wf_admininstr (.VBINOP shape op)) (resultWf : wf_admininstr (.VCONST .V128 value)) :
      VectorResultAllowed (.binary shape op left right) (some value)
  | binary_trap {shape op left right}
      (source : fun_vbinop_ shape op left right (some []))
      (leftWf : wf_admininstr (.VCONST .V128 left)) (rightWf : wf_admininstr (.VCONST .V128 right))
      (opWf : wf_admininstr (.VBINOP shape op)) :
      VectorResultAllowed (.binary shape op left right) none
  | convert {source target op input value}
      (relation : fun_vcvtop__ source target op input (some value))
      (inputWf : wf_admininstr (.VCONST .V128 input)) (opWf : wf_admininstr (.VCVTOP target source op))
      (resultWf : wf_admininstr (.VCONST .V128 value)) :
      VectorResultAllowed (.convert source target op input) (some value)

abbrev VectorChoices := Nat → VectorRequest → Option vec_

def VectorChoices.AdmissibleAt (choices : VectorChoices) (occurrence : Nat) (request : VectorRequest) : Prop :=
  VectorResultAllowed request (choices occurrence request)

/-- A policy supplies an admissible result whenever the independent source
numeric judgment admits one for the request. -/
def VectorChoices.Admissible (choices : VectorChoices) : Prop :=
  ∀ occurrence request, (∃ result, VectorResultAllowed request result) →
    choices.AdmissibleAt occurrence request

/-- A mathematical source policy witnesses inhabitance without consulting an
interpreter or native platform. It is not an executable platform adapter. -/
noncomputable def sourceVectorChoice : VectorChoices := by
  classical
  exact fun _ request => if possible : ∃ result, VectorResultAllowed request result then
    Classical.choose possible else none

theorem sourceVectorChoice_admissible : sourceVectorChoice.Admissible := by
  intro occurrence request possible
  classical
  simp only [VectorChoices.AdmissibleAt,sourceVectorChoice,dif_pos possible]
  exact Classical.choose_spec possible

inductive ChosenVector (choices : VectorChoices) (occurrence : Nat) (request : VectorRequest) : Option vec_ → Prop
  | selected (allowed : choices.AdmissibleAt occurrence request) :
      ChosenVector choices occurrence request (choices occurrence request)

/-- Independent SIMD admissibility yields an ordinary source numeric step. -/
theorem VectorResultAllowed.erases {request result} (allowed : VectorResultAllowed request result) :
    Step_pure request.instructions (vectorOutput result) := by
  cases allowed with
  | unary source member inputWf opWf resultWf =>
    exact .vunop _ _ _ _ _ source (List.length_pos_of_mem member) (by simp)
      (by simpa only [Option.get!_some,List.contains_iff_mem] using member) inputWf opWf resultWf
  | unary_trap source inputWf opWf =>
    exact .vunop_trap _ _ _ _ source (by simp) rfl inputWf opWf .admininstr_case_73
  | binary source member leftWf rightWf opWf resultWf =>
    exact .vbinop_val _ _ _ _ _ _ source (List.length_pos_of_mem member) (by simp)
      (by simpa only [Option.get!_some,List.contains_iff_mem] using member) leftWf rightWf opWf resultWf
  | binary_trap source leftWf rightWf opWf =>
    exact .vbinop_trap _ _ _ _ _ source (by simp) rfl leftWf rightWf opWf .admininstr_case_73
  | convert source inputWf opWf resultWf =>
    exact .vcvtop _ _ _ _ _ _ source (by simp) rfl inputWf opWf resultWf

theorem ChosenVector.erases {choices occurrence request result}
    (chosen : ChosenVector choices occurrence request result) :
    Step_pure request.instructions (vectorOutput result) := by
  cases chosen with
  | selected allowed => exact allowed.erases

/-- A fixed request and occurrence select one complete vector bit pattern. -/
theorem ChosenVector.deterministic {choices occurrence request left right}
    (first : ChosenVector choices occurrence request left)
    (second : ChosenVector choices occurrence request right) : left = right := by
  cases first
  cases second
  rfl

end Exec.Spec
