import Exec.Abs.Numeric.Unary
import Exec.Spec.IntegerCompareSigned

namespace Exec.Abs.Numeric
open SpecExt Exec.Spec

theorem compare_bound (ty : Inn) (op : relop_Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    compare ty op a b < 2 ^ integerWidth .I32 := by
  unfold compare
  split <;> split <;> decide

theorem compare_relation (ty : Inn) (op : relop_Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty op)
      (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))
      (some (.mk_num__0 .I32 (.mk_uN (compare ty op a b)))) := by
  cases op with
  | EQ => exact integer_eq_relation ty _ _
  | NE => exact integer_ne_relation ty _ _
  | LT sign => cases sign with
    | U => exact integer_ltu_relation ty _ _
    | S => exact integer_lts_relation ty a b
  | GT sign => cases sign with
    | U => exact integer_gtu_relation ty _ _
    | S => exact integer_gts_relation ty a b
  | LE sign => cases sign with
    | U => exact integer_leu_relation ty _ _
    | S => exact integer_les_relation ty a b
  | GE sign => cases sign with
    | U => exact integer_geu_relation ty _ _
    | S => exact integer_ges_relation ty a b

theorem compare_pure (ty : Inn) (op : relop_Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    Step_pure [admininstr_val (integerVal ty a.toNat), admininstr_val (integerVal ty b.toNat),
      admininstr_instr (.RELOP (numtype_Inn ty) (.mk_relop__0 ty op))]
      [admininstr_val (integerVal .I32 (compare ty op a b))] :=
  integer_relop_pure ty op a.toNat b.toNat _ (word_bound ty a) (word_bound ty b)
    (compare_bound ty op a b) (compare_relation ty op a b)

theorem compare_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (ty : Inn) (op : relop_Inn) (a b : BitVec (sizenn (numtype_Inn ty)))
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .RELOP (numtype_Inn ty) (.mk_relop__0 ty op) :: after, vals := baseValues ++ [integerVal ty a.toNat, integerVal ty b.toNat] } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := baseValues ++ [integerVal .I32 (compare ty op a b)] } :: rest, []⟩) := by
  exact integer_relop_simulation s ambient f rest after baseValues ty op _ _ _
    (word_bound ty a) (word_bound ty b) (compare_bound ty op a b) (compare_relation ty op a b)
    hs ha hf hl hv hc hr heights

end Exec.Abs.Numeric
