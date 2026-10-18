import Exec.Abs.Sim.Basic
import Exec.Abs.Typing
import Exec.Spec.Integer

namespace Exec.Abs
open SpecExt Exec.Spec

theorem integer_add_relation (ty : Inn) (a b : Nat) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty .ADD)
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some [.mk_num__0 ty (.mk_uN ((a + b) % 2 ^ integerWidth ty))]) := by
  have hbnd : (a + b) % 2 ^ integerWidth ty < 2 ^ integerWidth ty :=
    Nat.mod_lt _ (by positivity)
  have hn := integer_num_wf ty _ hbnd
  have hu := integer_uN_wf ty _ hbnd
  cases ty with
  | I32 => exact .fun_binop__case_0 _ _ _ (.fun_iadd__case_0 _ _ _ hu) hn
  | I64 => exact .fun_binop__case_1 _ _ _ (.fun_iadd__case_0 _ _ _ hu) hn

/-- Integer addition's exact modular result is a permitted generated reduction. -/
theorem integer_add_pure (ty : Inn) (a b : Nat)
    (ha : a < 2 ^ integerWidth ty) (hb : b < 2 ^ integerWidth ty) :
    Step_pure
      [admininstr_val (integerVal ty a), admininstr_val (integerVal ty b),
        admininstr_instr (.BINOP (numtype_Inn ty) (.mk_binop__0 ty .ADD))]
      [admininstr_val (integerVal ty ((a + b) % 2 ^ integerWidth ty))] := by
  have hc : (a + b) % 2 ^ integerWidth ty < 2 ^ integerWidth ty :=
    Nat.mod_lt _ (by positivity)
  apply Step_pure.binop_val (numtype_Inn ty)
    (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
    (.mk_binop__0 ty .ADD) (.mk_num__0 ty (.mk_uN ((a + b) % 2 ^ integerWidth ty)))
    (some [.mk_num__0 ty (.mk_uN ((a + b) % 2 ^ integerWidth ty))])
  · exact integer_add_relation ty a b
  · simp
  · simp
  · simp
  · exact wf_admininstr_val (integer_val_wf ty a ha)
  · exact wf_admininstr_val (integer_val_wf ty b hb)
  · exact wf_admininstr_instr (.instr_case_15 _ _ (.binop__case_0 _ _ _ rfl))
  · exact wf_admininstr_val (integer_val_wf ty _ hc)

/-- Both i32.add and i64.add simulate under all saved labels and frames. -/
theorem integer_add_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (ty : Inn) (a b : Nat) (ha' : a < 2 ^ integerWidth ty) (hb' : b < 2 ^ integerWidth ty)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty .ADD) :: after, vals := baseValues ++ [integerVal ty a, integerVal ty b] } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := baseValues ++ [integerVal ty ((a + b) % 2 ^ integerWidth ty)] } :: rest, []⟩) := by
  apply pure_stack_simulation s ambient f rest _ after baseValues _ _ hs ha hf hl hv hc hr heights
  · intro value h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact integer_val_wf ty a ha'
    · exact integer_val_wf ty b hb'
  · intro value h
    simp only [List.mem_singleton] at h
    subst value
    exact integer_val_wf ty _ (Nat.mod_lt _ (by positivity))
  · exact .instr_case_15 _ _ (.binop__case_0 _ _ _ rfl)
  · exact integer_add_pure ty a b ha' hb'

theorem integer_sub_relation (ty : Inn) (a b : Nat) (hb : b < 2 ^ integerWidth ty) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty .SUB)
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some [.mk_num__0 ty (.mk_uN ((a + 2 ^ integerWidth ty - b) % 2 ^ integerWidth ty))]) := by
  let width := integerWidth ty
  change b < 2 ^ width at hb
  have hbnd : (a + 2 ^ width - b) % 2 ^ width < 2 ^ width := Nat.mod_lt _ (by positivity)
  have hn := integer_num_wf ty _ hbnd
  have hu := integer_uN_wf ty _ hbnd
  have subcast : ((2 ^ width + a : Nat) : Int) - (b : Int) = ((a + 2 ^ width - b : Nat) : Int) := by
    have hle : b ≤ a + 2 ^ width := by omega
    rw [Int.ofNat_sub hle]
    omega
  have encoding : (((((2 ^ width + a : Nat) : Int) - (b : Int)) % (2 ^ width : Nat)).toNat) =
      (a + 2 ^ width - b) % 2 ^ width := by
    rw [subcast, Int.toNat_emod (by positivity) (by positivity)]
    simp [Int.toNat_pow_of_nonneg (by decide : (0 : Int) ≤ 2)]
  have rawEncoding : (((2 : Int) ^ width + a - b) % (2 : Int) ^ width).toNat =
      (a + 2 ^ width - b) % 2 ^ width := by
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using encoding
  have rel : fun_isub_ width (.mk_uN a) (.mk_uN b)
      (.mk_uN ((a + 2 ^ width - b) % 2 ^ width)) := by
    have raw := fun_isub_.fun_isub__case_0 width (.mk_uN a) (.mk_uN b)
    simpa only [proj_uN_0, rawEncoding] using raw (by
      simpa only [proj_uN_0, rawEncoding] using hu)
  cases ty with
  | I32 => exact .fun_binop__case_2 _ _ _ rel hn
  | I64 => exact .fun_binop__case_3 _ _ _ rel hn

/-- Integer subtraction's exact modular result is a permitted generated reduction. -/
theorem integer_sub_pure (ty : Inn) (a b : Nat)
    (ha : a < 2 ^ integerWidth ty) (hb : b < 2 ^ integerWidth ty) :
    Step_pure
      [admininstr_val (integerVal ty a), admininstr_val (integerVal ty b),
        admininstr_instr (.BINOP (numtype_Inn ty) (.mk_binop__0 ty .SUB))]
      [admininstr_val (integerVal ty ((a + 2 ^ integerWidth ty - b) % 2 ^ integerWidth ty))] := by
  have hc : (a + 2 ^ integerWidth ty - b) % 2 ^ integerWidth ty < 2 ^ integerWidth ty :=
    Nat.mod_lt _ (by positivity)
  apply Step_pure.binop_val (numtype_Inn ty)
    (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
    (.mk_binop__0 ty .SUB) (.mk_num__0 ty (.mk_uN ((a + 2 ^ integerWidth ty - b) % 2 ^ integerWidth ty)))
    (some [.mk_num__0 ty (.mk_uN ((a + 2 ^ integerWidth ty - b) % 2 ^ integerWidth ty))])
  · exact integer_sub_relation ty a b hb
  · simp
  · simp
  · simp
  · exact wf_admininstr_val (integer_val_wf ty a ha)
  · exact wf_admininstr_val (integer_val_wf ty b hb)
  · exact wf_admininstr_instr (.instr_case_15 _ _ (.binop__case_0 _ _ _ rfl))
  · exact wf_admininstr_val (integer_val_wf ty _ hc)

/-- Both i32.sub and i64.sub simulate under all saved labels and frames. -/
theorem integer_sub_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (ty : Inn) (a b : Nat) (ha' : a < 2 ^ integerWidth ty) (hb' : b < 2 ^ integerWidth ty)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty .SUB) :: after, vals := baseValues ++ [integerVal ty a, integerVal ty b] } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := baseValues ++ [integerVal ty ((a + 2 ^ integerWidth ty - b) % 2 ^ integerWidth ty)] } :: rest, []⟩) := by
  apply pure_stack_simulation s ambient f rest _ after baseValues _ _ hs ha hf hl hv hc hr heights
  · intro value h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact integer_val_wf ty a ha'
    · exact integer_val_wf ty b hb'
  · intro value h
    simp only [List.mem_singleton] at h
    subst value
    exact integer_val_wf ty _ (Nat.mod_lt _ (by positivity))
  · exact .instr_case_15 _ _ (.binop__case_0 _ _ _ rfl)
  · exact integer_sub_pure ty a b ha' hb'

theorem boolean_i32_bound (answer : Prop) [Decidable answer] :
    (if answer then 1 else 0) < 2 ^ integerWidth .I32 := by
  split <;> norm_num [integerWidth]

theorem integer_eqz_relation (ty : Inn) (bits : Nat) :
    fun_testop_ (numtype_Inn ty) (.mk_testop__0 ty .EQZ)
      (.mk_num__0 ty (.mk_uN bits))
      (some (.mk_num__0 .I32 (.mk_uN (if bits = 0 then 1 else 0)))) := by
  have hn := integer_num_wf .I32 _ (boolean_i32_bound (bits = 0))
  have hu := integer_uN_wf .I32 _ (boolean_i32_bound (bits = 0))
  have hbool : nat_of_bool (bits == 0) = (if bits = 0 then 1 else 0) := by
    cases bits <;> rfl
  have hi : fun_ieqz_ (integerWidth ty) (.mk_uN bits)
      (.mk_uN (if bits = 0 then 1 else 0)) := by
    simpa only [proj_uN_0, hbool] using
      (fun_ieqz_.fun_ieqz__case_0 (integerWidth ty) (.mk_uN bits) (by
        simpa only [proj_uN_0, hbool, integerWidth] using hu))
  cases ty with
  | I32 => exact .fun_testop__case_0 _ _ hi hn
  | I64 => exact .fun_testop__case_1 _ _ hi hn

/-- The generated test rule agrees with the abstract integer-zero predicate. -/
theorem integer_eqz_pure (ty : Inn) (bits : Nat)
    (hb : bits < 2 ^ integerWidth ty) :
    Step_pure
      [admininstr_val (integerVal ty bits),
        admininstr_instr (.TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ))]
      [admininstr_val (integerVal .I32 (if bits = 0 then 1 else 0))] := by
  apply Step_pure.testop (numtype_Inn ty) (.mk_num__0 ty (.mk_uN bits))
    (.mk_testop__0 ty .EQZ) (.mk_num__0 .I32 (.mk_uN (if bits = 0 then 1 else 0)))
    (some (.mk_num__0 .I32 (.mk_uN (if bits = 0 then 1 else 0))))
  · exact integer_eqz_relation ty bits
  · simp
  · rfl
  · exact integer_num_wf .I32 _ (boolean_i32_bound (bits = 0))
  · exact wf_admininstr_val (integer_val_wf ty bits hb)
  · exact wf_admininstr_instr (.instr_case_16 _ _ (.testop__case_0 _ _ _ rfl))
  · exact wf_admininstr_val (integer_val_wf .I32 _ (boolean_i32_bound (bits = 0)))

theorem integer_eqz_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (ty : Inn) (bits : Nat) (hb : bits < 2 ^ integerWidth ty)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: after, vals := baseValues ++ [integerVal ty bits] } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := baseValues ++ [integerVal .I32 (if bits = 0 then 1 else 0)] } :: rest, []⟩) := by
  apply pure_stack_simulation s ambient f rest _ after baseValues _ _ hs ha hf hl hv hc hr heights
  · intro value h; simp only [List.mem_singleton] at h; subst value
    exact integer_val_wf ty bits hb
  · intro value h; simp only [List.mem_singleton] at h; subst value
    exact integer_val_wf .I32 _ (boolean_i32_bound (bits = 0))
  · exact .instr_case_16 _ _ (.testop__case_0 _ _ _ rfl)
  · exact integer_eqz_pure ty bits hb

/-- A generated integer comparison relation lifts to its source reduction. -/
theorem integer_relop_pure (ty : Inn) (op : relop_Inn) (a b result : Nat)
    (ha : a < 2 ^ integerWidth ty) (hb : b < 2 ^ integerWidth ty)
    (hr : result < 2 ^ integerWidth .I32)
    (relation : fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty op)
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some (.mk_num__0 .I32 (.mk_uN result)))) :
    Step_pure
      [admininstr_val (integerVal ty a), admininstr_val (integerVal ty b),
        admininstr_instr (.RELOP (numtype_Inn ty) (.mk_relop__0 ty op))]
      [admininstr_val (integerVal .I32 result)] := by
  apply Step_pure.relop (numtype_Inn ty) (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
    (.mk_relop__0 ty op) (.mk_num__0 .I32 (.mk_uN result)) (some (.mk_num__0 .I32 (.mk_uN result)))
  · exact relation
  · simp
  · rfl
  · exact integer_num_wf .I32 result hr
  · exact wf_admininstr_val (integer_val_wf ty a ha)
  · exact wf_admininstr_val (integer_val_wf ty b hb)
  · exact wf_admininstr_instr (.instr_case_17 _ _ (.relop__case_0 _ _ _ rfl))
  · exact wf_admininstr_val (integer_val_wf .I32 result hr)

theorem integer_relop_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (ty : Inn) (op : relop_Inn) (a b result : Nat)
    (ha' : a < 2 ^ integerWidth ty) (hb' : b < 2 ^ integerWidth ty)
    (hbResult : result < 2 ^ integerWidth .I32)
    (relation : fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty op)
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some (.mk_num__0 .I32 (.mk_uN result))))
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .RELOP (numtype_Inn ty) (.mk_relop__0 ty op) :: after, vals := baseValues ++ [integerVal ty a, integerVal ty b] } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := baseValues ++ [integerVal .I32 result] } :: rest, []⟩) := by
  apply pure_stack_simulation s ambient f rest _ after baseValues _ _ hs ha hf hl hv hc hr heights
  · intro value h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact integer_val_wf ty a ha'
    · exact integer_val_wf ty b hb'
  · intro value h; simp only [List.mem_singleton] at h; subst value
    exact integer_val_wf .I32 result hbResult
  · exact .instr_case_17 _ _ (.relop__case_0 _ _ _ rfl)
  · exact integer_relop_pure ty op a b result ha' hb' hbResult relation

theorem integer_eq_pure (ty : Inn) (a b : Nat)
    (ha : a < 2 ^ integerWidth ty) (hb : b < 2 ^ integerWidth ty) :
    Step_pure
      [admininstr_val (integerVal ty a), admininstr_val (integerVal ty b),
        admininstr_instr (.RELOP (numtype_Inn ty) (.mk_relop__0 ty .EQ))]
      [admininstr_val (integerVal .I32 (if a = b then 1 else 0))] :=
  integer_relop_pure ty .EQ a b _ ha hb (boolean_i32_bound _) (Exec.Spec.integer_eq_relation ty a b)

theorem integer_ltu_pure (ty : Inn) (a b : Nat)
    (ha : a < 2 ^ integerWidth ty) (hb : b < 2 ^ integerWidth ty) :
    Step_pure
      [admininstr_val (integerVal ty a), admininstr_val (integerVal ty b),
        admininstr_instr (.RELOP (numtype_Inn ty) (.mk_relop__0 ty (.LT .U)))]
      [admininstr_val (integerVal .I32 (if a < b then 1 else 0))] :=
  integer_relop_pure ty (.LT .U) a b _ ha hb (boolean_i32_bound _) (Exec.Spec.integer_ltu_relation ty a b)

end Exec.Abs
