import Itasca.Runtime.SourceMachine.Typing
import Itasca.Runtime.Spec.Integer
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.SourceMachine.CallSafety
import Itasca.Runtime.Spec.SegmentInitCases

/-!
Sections, each formerly its own module: Context, Basic, Int, Typing, Trace, Trap, Control.
-/

/-! ## Context -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- Syntactic well-formedness of the suspended continuations. -/
def LabelsWf (labels : List Label) : Prop :=
  Forall (fun label => Forall wf_instr label.cont ∧ Forall wf_instr label.after) labels

private theorem forall_take {α : Type} {P : α → Prop} {xs : List α}
    (h : Forall P xs) (n : Nat) : Forall P (xs.take n) := by
  intro x hx
  exact h x (List.mem_of_mem_take hx)

private theorem forall_drop {α : Type} {P : α → Prop} {xs : List α}
    (h : Forall P xs) (n : Nat) : Forall P (xs.drop n) := by
  intro x hx
  exact h x (List.mem_of_mem_drop hx)

/-- Lift a redex through the entire explicit label stack. -/
theorem step_h_decode_labels {z z' : state} {code code' : List admininstr}
    {events : List HostEvent} (h : StepH ⟨z, code⟩ events ⟨z', code'⟩)
    (labels : List Label) (values : List val)
    (hl : LabelsWf labels) (hv : Forall wf_val values) :
    StepH ⟨z, decodeLabels labels values code⟩ events
      ⟨z', decodeLabels labels values code'⟩ := by
  induction labels generalizing values code code' with
  | nil =>
    simpa [instrContext, decodeLabels] using step_h_instrs h values [] hv (forall_nil _)
  | cons label labels ih =>
    have hc := (hl label (by simp)).1
    have ha := (hl label (by simp)).2
    have hr : LabelsWf labels := fun x hx => hl x (by simp [hx])
    have h₁ := step_h_instrs h (values.drop label.height) []
      (forall_drop hv _) (forall_nil _)
    have h₂ := step_h_label h₁ label.arity label.cont hc
    have h₃ := step_h_instrs h₂ [] (label.after.map admininstr_instr)
      (forall_nil _) (wf_instrs ha)
    have h₄ := ih h₃ (values.take label.height) hr (forall_take hv _)
    simpa [decodeLabels, instrContext, labelContext, vals] using h₄

/-- Moving values from code into the flat stack changes no decoded instructions,
provided the moved values remain above the innermost label's saved height. -/
theorem decode_labels_move_values (labels : List Label) (values extra : List val)
    (code : List admininstr)
    (heights : ∀ label ∈ labels, label.height ≤ values.length) :
    decodeLabels labels (values ++ extra) code =
      decodeLabels labels values (vals extra ++ code) := by
  cases labels with
  | nil => simp [decodeLabels, vals, List.map_append, List.append_assoc]
  | cons label labels =>
    have h := heights label (by simp)
    simp only [decodeLabels, List.take_append_of_le_length h,
      List.drop_append_of_le_length h, vals, List.map_append, List.append_assoc]

/-- Syntactic requirements for suspended callers, separate from semantic typing. -/
def FrameWf (f : AFrame) : Prop :=
  wf_frame f.toFrame ∧ LabelsWf f.labels ∧ Forall wf_val f.vals ∧ Forall wf_instr f.code

def activeFrame (ambient : frame) : List AFrame → frame
  | [] => ambient
  | f :: _ => f.toFrame

theorem active_frame_wf {ambient : frame} {frames : List AFrame}
    (ha : wf_frame ambient) (hf : Forall FrameWf frames) :
    wf_frame (activeFrame ambient frames) := by
  cases frames with
  | nil => exact ha
  | cons f rest => exact (hf f (by simp)).1

/-- Lift through all suspended callers, each in its own local/module context. -/
theorem step_h_decode_frames {s s' : store} (ambient : frame) (frames : List AFrame)
    {code code' : List admininstr} {events : List HostEvent}
    (h : StepH ⟨⟨s, activeFrame ambient frames⟩, code⟩ events
      ⟨⟨s', activeFrame ambient frames⟩, code'⟩)
    (ha : wf_frame ambient) (hf : Forall FrameWf frames) :
    StepH ⟨⟨s, ambient⟩, decodeFrames frames code⟩ events
      ⟨⟨s', ambient⟩, decodeFrames frames code'⟩ := by
  induction frames generalizing code code' with
  | nil => exact h
  | cons f rest ih =>
    obtain ⟨_, hl, hv, hc⟩ := hf f (by simp)
    have hr : Forall FrameWf rest := fun x hx => hf x (by simp [hx])
    have h₁ := step_h_instrs h [] (f.code.map admininstr_instr)
      (forall_nil _) (wf_instrs hc)
    have h₂ := step_h_decode_labels h₁ f.labels f.vals hl hv
    have h₃ := step_h_frame h₂ f.arity (activeFrame ambient rest) (active_frame_wf ha hr)
    have h₄ := ih h₃ hr
    simpa [decodeFrames, activeFrame, instrContext, frameContext, vals] using h₄

/-- Lift a transition in the current frame through its frame boundary and callers.
The inner frame may change locals, while its result arity stays fixed. -/
theorem step_h_active {s s' : store} (ambient : frame) (rest : List AFrame)
    (arity : Nat) {inner inner' : frame} {body body' : List admininstr}
    {events : List HostEvent}
    (h : StepH ⟨⟨s, inner⟩, body⟩ events ⟨⟨s', inner'⟩, body'⟩)
    (ha : wf_frame ambient) (hr : Forall FrameWf rest) :
    StepH ⟨⟨s, ambient⟩, decodeFrames rest [.FRAME_ arity inner body]⟩ events
      ⟨⟨s', ambient⟩, decodeFrames rest [.FRAME_ arity inner' body']⟩ := by
  exact step_h_decode_frames ambient rest
    (step_h_frame h arity (activeFrame ambient rest) (active_frame_wf ha hr)) ha hr

end Itasca.Runtime.SourceMachine

end

/-! ## Basic -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- Constants are already values in SpecTec's administrative instruction syntax.
Moving one into the flat stack is therefore an exact decoding equality. -/
theorem decode_const (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (ty : numtype) (value : num_) (after : List instr)
    (heights : ∀ label ∈ f.labels, label.height ≤ f.vals.length) :
    decode ⟨s, ambient, { f with code := .CONST ty value :: after } :: rest, []⟩ =
    decode ⟨s, ambient,
      { f with code := after, vals := f.vals ++ [.CONST ty value] } :: rest, []⟩ := by
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append,
    AFrame.toFrame, List.map_cons, admininstr_instr]
  rw [decode_labels_move_values _ _ _ _ heights]
  rfl

/-- Nop is a real specification step, under arbitrarily many labels and callers. -/
theorem nop_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val f.vals)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest) :
    StepH (decode ⟨s, ambient, { f with code := .NOP :: after } :: rest, []⟩) []
      (decode ⟨s, ambient, { f with code := after } :: rest, []⟩) := by
  have hw : wf_config ⟨⟨s, f.toFrame⟩, [.NOP]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact .admininstr_case_0)
  have hw' : wf_config ⟨⟨s, f.toFrame⟩, []⟩ := wf_config_make hs hf (forall_nil _)
  have h : StepH ⟨⟨s, f.toFrame⟩, [.NOP]⟩ [] ⟨⟨s, f.toFrame⟩, []⟩ :=
    .step (.pure _ _ _ (.nop .admininstr_case_0) hw hw')
  have h₁ := step_h_instrs h [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := step_h_decode_labels h₁ f.labels f.vals hl hv
  have h₃ := step_h_active ambient rest f.arity h₂ ha hr
  simpa [decode, decodeFrames, instrContext, vals, AFrame.toFrame, AFrame.arity, admininstr_instr] using h₃

/-- Reuse a generated pure reduction under the flat operand stack and every
nested execution context. The consumed operands must lie above label heights. -/
theorem pure_stack_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr)
    (baseValues consumed produced : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hb : Forall wf_val consumed) (hp : Forall wf_val produced)
    (hi : wf_instr instruction)
    (h : Step_pure (vals consumed ++ [admininstr_instr instruction]) (vals produced)) :
    StepH (decode ⟨s, ambient,
      { f with code := instruction :: after, vals := baseValues ++ consumed } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := baseValues ++ produced } :: rest, []⟩) := by
  have hw : wf_config ⟨⟨s, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hb)
      (by intro ai hai; simp only [List.mem_singleton] at hai; subst ai; exact wf_admininstr_instr hi))
  have hw' := wf_config_vals hs hf hp
  have step : StepH ⟨⟨s, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨s, f.toFrame⟩, vals produced⟩ := .step (.pure _ _ _ h hw hw')
  have h₁ := step_h_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := step_h_decode_labels h₁ f.labels baseValues hl hv
  have h₃ := step_h_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity]
  rw [decode_labels_move_values _ _ _ _ heights, decode_labels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame] using h₃

/-- Drop discards the top value and leaves the remaining operand stack intact. -/
theorem drop_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val) (value : val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues) (hx : wf_val value)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .DROP :: after, vals := baseValues ++ [value] } :: rest, []⟩) []
      (decode ⟨s, ambient, { f with code := after, vals := baseValues } :: rest, []⟩) := by
  simpa using pure_stack_simulation s ambient f rest .DROP after baseValues [value] []
    hs ha hf hl hv hc hr heights
    (by intro x h; simp only [List.mem_singleton] at h; subst x; exact hx)
    (forall_nil _) .instr_case_2 (.drop value hx .admininstr_case_2)

theorem stack_step_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (after : List instr)
    (baseValues consumed produced : List val)
    (ha : wf_frame ambient)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (step : StepH ⟨⟨s, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨s, f.toFrame⟩, vals produced⟩) :
    StepH (decode ⟨s, ambient,
      { f with code := instruction :: after, vals := baseValues ++ consumed } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := after, vals := baseValues ++ produced } :: rest, []⟩) := by
  have h₁ := step_h_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := step_h_decode_labels h₁ f.labels baseValues hl hv
  have h₃ := step_h_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity]
  rw [decode_labels_move_values _ _ _ _ heights, decode_labels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame] using h₃

/-- Lift a pure source rewrite that replaces the current instruction by a
short instruction sequence, possibly consuming or producing stack values. -/
theorem pure_code_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (instruction : instr) (replacement after : List instr)
    (baseValues consumed produced : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hb : Forall wf_val consumed) (hp : Forall wf_val produced)
    (hi : wf_instr instruction) (hrepl : Forall wf_instr replacement)
    (h : Step_pure (vals consumed ++ [admininstr_instr instruction])
      (vals produced ++ replacement.map admininstr_instr)) :
    StepH (decode ⟨s, ambient,
      { f with code := instruction :: after, vals := baseValues ++ consumed } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := replacement ++ after, vals := baseValues ++ produced } :: rest, []⟩) := by
  have hw : wf_config ⟨⟨s, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hb)
      (by intro ai hai; simp only [List.mem_singleton] at hai; subst ai; exact wf_admininstr_instr hi))
  have hw' : wf_config ⟨⟨s, f.toFrame⟩, vals produced ++ replacement.map admininstr_instr⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hp) (wf_instrs hrepl))
  have step : StepH ⟨⟨s, f.toFrame⟩, vals consumed ++ [admininstr_instr instruction]⟩ []
      ⟨⟨s, f.toFrame⟩, vals produced ++ replacement.map admininstr_instr⟩ := .step (.pure _ _ _ h hw hw')
  have h₁ := step_h_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := step_h_decode_labels h₁ f.labels baseValues hl hv
  have h₃ := step_h_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity, List.map_append]
  rw [decode_labels_move_values _ _ _ _ heights, decode_labels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame] using h₃

end Itasca.Runtime.SourceMachine

end

/-! ## Int -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

theorem integer_add_relation (ty : Inn) (a b : Nat) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty .ADD)
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some [.mk_num__0 ty (.mk_uN ((a + b) % 2 ^ integerWidth ty))]) := by
  have hbnd : (a + b) % 2 ^ integerWidth ty < 2 ^ integerWidth ty :=
    Nat.mod_lt _ (by positivity)
  have hn := integer_num_wf ty _ hbnd
  have hu := integer_u_n_wf ty _ hbnd
  cases ty with
  | I32 => exact .fun_binop__case_0 _ _ _ (.fun_iadd__case_0 _ _ _ hu) hn
  | I64 => exact .fun_binop__case_1 _ _ _ (.fun_iadd__case_0 _ _ _ hu) hn

theorem integer_sub_relation (ty : Inn) (a b : Nat) (hb : b < 2 ^ integerWidth ty) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty .SUB)
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some [.mk_num__0 ty (.mk_uN ((a + 2 ^ integerWidth ty - b) % 2 ^ integerWidth ty))]) := by
  let width := integerWidth ty
  change b < 2 ^ width at hb
  have hbnd : (a + 2 ^ width - b) % 2 ^ width < 2 ^ width := Nat.mod_lt _ (by positivity)
  have hn := integer_num_wf ty _ hbnd
  have hu := integer_u_n_wf ty _ hbnd
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

theorem boolean_i32_bound (answer : Prop) [Decidable answer] :
    (if answer then 1 else 0) < 2 ^ integerWidth .I32 := by
  split <;> norm_num [integerWidth]

theorem integer_eqz_relation (ty : Inn) (bits : Nat) :
    fun_testop_ (numtype_Inn ty) (.mk_testop__0 ty .EQZ)
      (.mk_num__0 ty (.mk_uN bits))
      (some (.mk_num__0 .I32 (.mk_uN (if bits = 0 then 1 else 0)))) := by
  have hn := integer_num_wf .I32 _ (boolean_i32_bound (bits = 0))
  have hu := integer_u_n_wf .I32 _ (boolean_i32_bound (bits = 0))
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

end Itasca.Runtime.SourceMachine

end

/-! ## Typing -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- The semantic label invariant provides syntax well-formedness for every
continuation used while lifting source reductions through nested labels. -/
theorem code_stack_labels_wf {C : context} {labels : List Label}
    {stack results : List valtype} {code : List instr}
    (h : CodeStackTyped C labels stack code results) : LabelsWf labels := by
  induction h with
  | outer _ => exact forall_nil _
  | @label label labels saved operands code results height nesting body cont after ih =>
    intro l hl
    simp only [List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact ⟨(Itasca.DeclarativeComplete.wellFormed cont).2, code_stack_wf after⟩
    · exact ih l hl

theorem frame_typed_wf {s : store} {f : AFrame} {incoming : List valtype}
    (h : FrameTyped s f incoming) : FrameWf f := by
  cases h with
  | mk C bindings localTypes locals values returns code hw =>
    exact ⟨hw, code_stack_labels_wf code, results_typed_wf values, code_stack_wf code⟩

theorem frames_typed_wf {s : store} {frames : List AFrame} {incoming : List valtype}
    (h : FramesTyped s frames incoming) : Forall FrameWf frames := by
  induction h with
  | nil => exact forall_nil _
  | cons hf _ ih =>
    intro f hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact frame_typed_wf hf
    · exact ih f hm

theorem decode_labels_wf (labels : List Label) (values : List val) (code : List admininstr)
    (hl : LabelsWf labels) (hv : Forall wf_val values) (hc : Forall wf_admininstr code) :
    Forall wf_admininstr (decodeLabels labels values code) := by
  induction labels generalizing values code with
  | nil => exact forall_append (wf_vals hv) hc
  | cons label labels ih =>
    have hlabel := hl label (by simp)
    apply ih _ _ (fun l hm => hl l (by simp [hm]))
      (fun value hm => hv value (List.mem_of_mem_take hm))
    apply forall_append ?_ (wf_instrs hlabel.2)
    intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    exact .admininstr_case_71 _ _ _ hlabel.1
      (forall_append (wf_vals (fun value hm => hv value (List.mem_of_mem_drop hm))) hc)

theorem decode_frames_wf (frames : List AFrame) (code : List admininstr)
    (hf : Forall FrameWf frames) (hc : Forall wf_admininstr code) :
    Forall wf_admininstr (decodeFrames frames code) := by
  induction frames generalizing code with
  | nil => exact hc
  | cons f rest ih =>
    obtain ⟨frame, labels, values, body⟩ := hf f (by simp)
    apply ih _ (fun f hm => hf f (by simp [hm]))
    intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    exact .admininstr_case_72 _ _ _ frame
      (decode_labels_wf f.labels f.vals _ labels values (forall_append hc (wf_instrs body)))

/-- Source typing supplies all endpoint well-formedness premises needed by the
generated reduction rules and by zero-step administrative simulations. -/
theorem ATyped.decode_wf {s : AState} (h : ATyped s) : wf_config (decode s) :=
  wf_config_make h.store h.ambient
    (decode_frames_wf s.frames (vals s.results) (frames_typed_wf h.frames) (wf_vals h.results))

end Itasca.Runtime.SourceMachine

end

/-! ## Trace -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

theorem steps_hn_label {n : Nat} {c c' : config} {events : List HostEvent}
    (h : StepsHN n c events c') (arity : Nat) (cont : List instr) (hc : Forall wf_instr cont) :
    StepsHN n (Itasca.Runtime.Spec.labelContext arity cont c) events (Itasca.Runtime.Spec.labelContext arity cont c') := by
  apply h.map ?_ (fun _ _ _ h => step_h_label h arity cont hc)
  intro c hw
  cases c
  exact wf_config_label arity hw hc

theorem steps_hn_frame {n : Nat} {c c' : config} {events : List HostEvent}
    (h : StepsHN n c events c') (arity : Nat) (outer : frame) (hf : wf_frame outer) :
    StepsHN n (frameContext arity outer c) events (frameContext arity outer c') := by
  apply h.map ?_ (fun _ _ _ h => step_h_frame h arity outer hf)
  intro c hw
  cases c with | mk_config z code =>
    cases z
    exact wf_config_frame arity hw hf

theorem steps_hn_instrs {n : Nat} {c c' : config} {events : List HostEvent}
    (h : StepsHN n c events c') (values : List val) (after : List admininstr)
    (hv : Forall wf_val values) (ha : Forall wf_admininstr after) :
    StepsHN n (instrContext values after c) events (instrContext values after c') := by
  apply h.map ?_ (fun _ _ _ h => step_h_instrs h values after hv ha)
  intro c hw
  cases c
  exact wf_config_instrs hw hv ha

theorem steps_hn_decode_labels {n : Nat} {z z' : state} {code code' : List admininstr}
    {events : List HostEvent} (h : StepsHN n ⟨z, code⟩ events ⟨z', code'⟩)
    (labels : List Label) (values : List val)
    (hl : LabelsWf labels) (hv : Forall wf_val values) :
    StepsHN n ⟨z, decodeLabels labels values code⟩ events
      ⟨z', decodeLabels labels values code'⟩ := by
  induction labels generalizing values code code' with
  | nil => simpa [instrContext, decodeLabels] using steps_hn_instrs h values [] hv (forall_nil _)
  | cons label labels ih =>
    have h₁ := steps_hn_instrs h (values.drop label.height) []
      (fun v hm => hv v (List.mem_of_mem_drop hm)) (forall_nil _)
    have h₂ := steps_hn_label h₁ label.arity label.cont (hl label (by simp)).1
    have h₃ := steps_hn_instrs h₂ [] (label.after.map admininstr_instr)
      (forall_nil _) (wf_instrs (hl label (by simp)).2)
    have h₄ := ih h₃ (values.take label.height) (fun l hm => hl l (by simp [hm]))
      (fun v hm => hv v (List.mem_of_mem_take hm))
    simpa [decodeLabels, instrContext, Itasca.Runtime.Spec.labelContext, vals] using h₄

theorem steps_hn_decode_frames {n : Nat} {s s' : store} (ambient : frame) (frames : List AFrame)
    {code code' : List admininstr} {events : List HostEvent}
    (h : StepsHN n ⟨⟨s, activeFrame ambient frames⟩, code⟩ events
      ⟨⟨s', activeFrame ambient frames⟩, code'⟩)
    (ha : wf_frame ambient) (hf : Forall FrameWf frames) :
    StepsHN n ⟨⟨s, ambient⟩, decodeFrames frames code⟩ events
      ⟨⟨s', ambient⟩, decodeFrames frames code'⟩ := by
  induction frames generalizing code code' with
  | nil => exact h
  | cons f rest ih =>
    obtain ⟨_, hl, hv, hc⟩ := hf f (by simp)
    have hr : Forall FrameWf rest := fun x hx => hf x (by simp [hx])
    have h₁ := steps_hn_instrs h [] (f.code.map admininstr_instr) (forall_nil _) (wf_instrs hc)
    have h₂ := steps_hn_decode_labels h₁ f.labels f.vals hl hv
    have h₃ := steps_hn_frame h₂ f.arity (activeFrame ambient rest) (active_frame_wf ha hr)
    have h₄ := ih h₃ hr
    simpa [decodeFrames, activeFrame, instrContext, frameContext, vals] using h₄

end Itasca.Runtime.SourceMachine

end

/-! ## Trap -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

theorem wf_trap : Forall wf_admininstr [admininstr.TRAP] := by
  intro i hi
  simp only [List.mem_singleton] at hi
  subst i
  exact .admininstr_case_73

theorem trap_values (s : store) (f : frame) (values : List val) (after : List admininstr)
    (hs : wf_store s) (hf : wf_frame f)
    (hv : Forall wf_val values) (ha : Forall wf_admininstr after) :
    ∃ n, StepsHN n ⟨⟨s, f⟩, vals values ++ ([.TRAP] ++ after)⟩ [] ⟨⟨s, f⟩, [.TRAP]⟩ := by
  have hw := wf_config_make hs hf wf_trap
  by_cases h : values ≠ [] ∨ after ≠ []
  · have before := wf_config_make hs hf (forall_append (wf_vals hv) (forall_append wf_trap ha))
    have step : StepH ⟨⟨s, f⟩, vals values ++ ([.TRAP] ++ after)⟩ [] ⟨⟨s, f⟩, [.TRAP]⟩ :=
      .step (.pure _ _ _ (.trap_vals values after h hv ha .admininstr_case_73) before hw)
    exact ⟨1, by simpa only [List.nil_append] using StepsHN.cons step (StepsHN.refl hw)⟩
  · have hv : values = [] := by tauto
    have ha : after = [] := by tauto
    subst values
    subst after
    exact ⟨0, by simpa [vals] using StepsHN.refl hw⟩

theorem trap_label (s : store) (f : frame) (arity : Nat) (cont : List instr)
    (hs : wf_store s) (hf : wf_frame f) (hc : Forall wf_instr cont) :
    StepH ⟨⟨s, f⟩, [.LABEL_ arity cont [.TRAP]]⟩ [] ⟨⟨s, f⟩, [.TRAP]⟩ := by
  have hw := wf_config_make hs hf wf_trap
  have hl : wf_admininstr (.LABEL_ arity cont [.TRAP]) := .admininstr_case_71 _ _ _ hc wf_trap
  exact .step (.pure _ _ _ (.trap_label arity cont hl .admininstr_case_73)
    (wf_config_label arity hw hc) hw)

/-- Each label is removed by the generated trap rule after its inner operands
and continuation have been discarded. -/
theorem trap_labels (s : store) (f : frame) (labels : List Label)
    (values : List val) (after : List admininstr)
    (hs : wf_store s) (hf : wf_frame f) (hl : LabelsWf labels)
    (hv : Forall wf_val values) (ha : Forall wf_admininstr after) :
    ∃ n, StepsHN n ⟨⟨s, f⟩, decodeLabels labels values ([.TRAP] ++ after)⟩ []
      ⟨⟨s, f⟩, [.TRAP]⟩ := by
  induction labels generalizing values after with
  | nil => exact trap_values s f values after hs hf hv ha
  | cons label labels ih =>
    have hc := hl label (by simp)
    have hr : LabelsWf labels := fun l hm => hl l (by simp [hm])
    have ht : Forall wf_val (values.take label.height) := fun v hm => hv v (List.mem_of_mem_take hm)
    obtain ⟨n, inner⟩ := trap_values s f (values.drop label.height) after hs hf
      (fun v hm => hv v (List.mem_of_mem_drop hm)) ha
    have first := steps_hn_decode_labels
      (steps_hn_instrs (steps_hn_label inner label.arity label.cont hc.1) []
        (label.after.map admininstr_instr) (forall_nil _) (wf_instrs hc.2))
      labels (values.take label.height) hr ht
    have second := step_h_decode_labels
      (step_h_instrs (trap_label s f label.arity label.cont hs hf hc.1) []
        (label.after.map admininstr_instr) (forall_nil _) (wf_instrs hc.2))
      labels (values.take label.height) hr ht
    obtain ⟨m, tail⟩ := ih (values.take label.height) (label.after.map admininstr_instr) hr ht (wf_instrs hc.2)
    have rest := StepsHN.cons second tail
    have all := first.trans rest
    exact ⟨n + (m + 1), by simpa [decodeLabels, instrContext, Itasca.Runtime.Spec.labelContext, vals] using all⟩

theorem trap_frame (s : store) (outer inner : frame) (arity : Nat)
    (hs : wf_store s) (ho : wf_frame outer) (hi : wf_frame inner) :
    StepH ⟨⟨s, outer⟩, [.FRAME_ arity inner [.TRAP]]⟩ [] ⟨⟨s, outer⟩, [.TRAP]⟩ := by
  have hw := wf_config_make hs ho wf_trap
  have hiw := wf_config_make hs hi wf_trap
  have hf : wf_admininstr (.FRAME_ arity inner [.TRAP]) := .admininstr_case_72 _ _ _ hi wf_trap
  exact .step (.pure _ _ _ (.trap_frame arity inner hf .admininstr_case_73)
    (wf_config_frame arity hiw ho) hw)

/-- Trap unwinding crosses every suspended caller, with its own frame context. -/
theorem trap_frames (s : store) (ambient : frame) (frames : List AFrame)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : Forall FrameWf frames) :
    ∃ n, StepsHN n ⟨⟨s, ambient⟩, decodeFrames frames [.TRAP]⟩ [] ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  induction frames with
  | nil => exact ⟨0, .refl (wf_config_make hs ha wf_trap)⟩
  | cons f rest ih =>
    obtain ⟨hw, hl, hv, hc⟩ := hf f (by simp)
    have hr : Forall FrameWf rest := fun f hm => hf f (by simp [hm])
    obtain ⟨n, inner⟩ := trap_labels s f.toFrame f.labels f.vals (f.code.map admininstr_instr)
      hs hw hl hv (wf_instrs hc)
    have first := steps_hn_decode_frames ambient rest
      (steps_hn_frame inner f.arity (activeFrame ambient rest) (active_frame_wf ha hr)) ha hr
    have second := step_h_decode_frames ambient rest
      (trap_frame s (activeFrame ambient rest) f.toFrame f.arity hs (active_frame_wf ha hr) hw) ha hr
    obtain ⟨m, tail⟩ := ih hr
    exact ⟨n + (m + 1), by
      simpa [decodeFrames, frameContext] using first.trans (StepsHN.cons second tail)⟩

/-- An unreachable instruction takes a positive number of specification steps
to the terminal trap, even inside arbitrarily nested labels and calls. -/
theorem unreachable_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val f.vals)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest) :
    ∃ n, 0 < n ∧ StepsHN n
      (decode ⟨s, ambient, { f with code := .UNREACHABLE :: after } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  have hw : wf_config ⟨⟨s, f.toFrame⟩, [.UNREACHABLE]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact .admininstr_case_1)
  have ht := wf_config_make hs hf wf_trap
  have step : StepH ⟨⟨s, f.toFrame⟩, [.UNREACHABLE]⟩ [] ⟨⟨s, f.toFrame⟩, [.TRAP]⟩ :=
    .step (.pure _ _ _ (.unreachable .admininstr_case_1 .admininstr_case_73) hw ht)
  have lifted := step_h_active ambient rest f.arity
    (step_h_decode_labels (step_h_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc))
      f.labels f.vals hl hv) ha hr
  have hframes : Forall FrameWf ({ f with code := after } :: rest) := by
    intro frame hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact ⟨hf, hl, hv, hc⟩
    · exact hr frame hm
  obtain ⟨n, tail⟩ := trap_frames s ambient ({ f with code := after } :: rest) hs ha hframes
  refine ⟨n + 1, by omega, ?_⟩
  simpa [decode, decodeFrames, vals, instrContext, AFrame.arity, AFrame.toFrame, admininstr_instr] using
    StepsHN.cons lifted tail

end Itasca.Runtime.SourceMachine

end

/-! ## Control -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- The abstract conditional selects the same block as the generated rule. -/
theorem if_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (bits : Nat) (bt : blocktype) (yes no : List instr)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hb : bits < 2 ^ integerWidth .I32) (hi : wf_instr (.IFELSE bt yes no)) :
    StepH (decode ⟨s, ambient,
      { f with code := .IFELSE bt yes no :: after, vals := baseValues ++ [integerVal .I32 bits] } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := .BLOCK bt (if bits = 0 then no else yes) :: after, vals := baseValues } :: rest, []⟩) := by
  have hblock : wf_instr (.BLOCK bt (if bits = 0 then no else yes)) := by
    cases hi with
    | instr_case_6 _ _ _ hbt hy hn =>
      apply wf_instr.instr_case_4 _ _ hbt
      split <;> assumption
  have hp : Step_pure [admininstr_val (integerVal .I32 bits), .IFELSE bt yes no]
      [.BLOCK bt (if bits = 0 then no else yes)] := by
    by_cases hz : bits = 0
    · simpa only [integerVal, admininstr_val, numtype_Inn, hz, ite_true] using Step_pure.if_false (.mk_num__0 .I32 (.mk_uN bits)) bt yes no
        (by simp [proj_num__0]) (by simpa [proj_num__0, proj_uN_0] using hz)
        (wf_admininstr_val (integer_val_wf .I32 bits hb)) (wf_admininstr_instr hi)
        (wf_admininstr_instr (i := .BLOCK bt no) (by simpa only [hz, ite_true] using hblock))
    · simpa only [integerVal, admininstr_val, numtype_Inn, hz, ite_false] using Step_pure.if_true (.mk_num__0 .I32 (.mk_uN bits)) bt yes no
        (by simp [proj_num__0]) (by simpa [proj_num__0, proj_uN_0] using hz)
        (wf_admininstr_val (integer_val_wf .I32 bits hb)) (wf_admininstr_instr hi)
        (wf_admininstr_instr (i := .BLOCK bt yes) (by simpa only [hz, ite_false] using hblock))
  simpa only [List.append_nil, List.singleton_append] using
    pure_code_simulation s ambient f rest (.IFELSE bt yes no) [.BLOCK bt (if bits = 0 then no else yes)] after
      baseValues [integerVal .I32 bits] [] hs ha hf hl hv hc hr heights
      (by intro value h; simp only [List.mem_singleton] at h; subst value; exact integer_val_wf .I32 bits hb)
      (forall_nil _) hi
      (by intro op h; simp only [List.mem_singleton] at h; subst op; exact hblock) hp

theorem br_if_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (baseValues : List val)
    (bits index : Nat)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hb : bits < 2 ^ integerWidth .I32) (hi : index < 2 ^ 32) :
    StepH (decode ⟨s, ambient,
      { f with code := .BR_IF (.mk_uN index) :: after, vals := baseValues ++ [integerVal .I32 bits] } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := if bits = 0 then after else .BR (.mk_uN index) :: after, vals := baseValues } :: rest, []⟩) := by
  have hidx := integer_u_n_wf .I32 index hi
  have hi' : wf_instr (.BR_IF (.mk_uN index)) := .instr_case_8 _ hidx
  have hbr : wf_instr (.BR (.mk_uN index)) := .instr_case_7 _ hidx
  let replacement : List instr := if bits = 0 then [] else [.BR (.mk_uN index)]
  have hp : Step_pure [admininstr_val (integerVal .I32 bits), .BR_IF (.mk_uN index)]
      (replacement.map admininstr_instr) := by
    by_cases hz : bits = 0
    · simpa only [integerVal, admininstr_val, numtype_Inn, replacement, hz, ite_true, List.map_nil] using
        Step_pure.br_if_false (.mk_num__0 .I32 (.mk_uN bits)) (.mk_uN index)
          (by simp [proj_num__0]) (by simpa [proj_num__0, proj_uN_0] using hz)
          (wf_admininstr_val (integer_val_wf .I32 bits hb)) (wf_admininstr_instr hi')
    · simpa only [integerVal, admininstr_val, numtype_Inn, replacement, hz, ite_false, List.map_cons, List.map_nil, admininstr_instr] using
        Step_pure.br_if_true (.mk_num__0 .I32 (.mk_uN bits)) (.mk_uN index)
          (by simp [proj_num__0]) (by simpa [proj_num__0, proj_uN_0] using hz)
          (wf_admininstr_val (integer_val_wf .I32 bits hb)) (wf_admininstr_instr hi') (wf_admininstr_instr hbr)
  have hrepl : Forall wf_instr replacement := by
    intro op h
    dsimp [replacement] at h
    split at h
    · contradiction
    · simp only [List.mem_singleton] at h; subst op; exact hbr
  have h := pure_code_simulation s ambient f rest (.BR_IF (.mk_uN index)) replacement after
      baseValues [integerVal .I32 bits] [] hs ha hf hl hv hc hr heights
      (by intro value h; simp only [List.mem_singleton] at h; subst value; exact integer_val_wf .I32 bits hb)
      (forall_nil _) hi' hrepl hp
  by_cases hz : bits = 0 <;> simpa only [integerVal, admininstr_val, numtype_Inn, replacement, hz, ite_true, ite_false,
    List.append_nil, List.nil_append, List.singleton_append] using h


/-- Entering a block installs the generated label with the exact saved stack
height, parameter values, and continuation. -/
theorem block_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after body : List instr) (baseValues args : List val)
    (bt : blocktype) (params results : List valtype)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues) (hargs : Forall wf_val args)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hiOp : wf_instr (.BLOCK bt body))
    (hbt : fun_blocktype ⟨s, f.toFrame⟩ bt = ⟨.mk_list params, .mk_list results⟩)
    (hlen : args.length = params.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .BLOCK bt body :: after, vals := baseValues ++ args } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := body, vals := baseValues ++ args, labels := ⟨results, results, [], baseValues.length, after⟩ :: f.labels } :: rest, []⟩) := by
  have hbody : Forall wf_instr body := by cases hiOp; assumption
  have hlabel : wf_admininstr (.LABEL_ results.length [] (vals args ++ body.map admininstr_instr)) :=
    .admininstr_case_71 _ _ _ (forall_nil _) (forall_append (wf_vals hargs) (wf_instrs hbody))
  have hsource : wf_config ⟨⟨s, f.toFrame⟩, vals args ++ [.BLOCK bt body]⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hargs)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact wf_admininstr_instr hiOp))
  have htarget : wf_config ⟨⟨s, f.toFrame⟩, [.LABEL_ results.length [] (vals args ++ body.map admininstr_instr)]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hlabel)
  have read := Step_read.block ⟨s, f.toFrame⟩ args.length args bt body results.length params results
    hbt hsource hlabel rfl hlen rfl
  have step : StepH ⟨⟨s, f.toFrame⟩, vals args ++ [.BLOCK bt body]⟩ []
      ⟨⟨s, f.toFrame⟩, [.LABEL_ results.length [] (vals args ++ body.map admininstr_instr)]⟩ :=
    .step (.read _ _ _ read hsource htarget)
  have h₁ := step_h_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := step_h_decode_labels h₁ f.labels baseValues hl hv
  have h₃ := step_h_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity]
  rw [decode_labels_move_values _ _ _ _ heights]
  simpa [decodeLabels, Label.arity, instrContext, vals, List.append_assoc, AFrame.arity,
    AFrame.toFrame, admininstr_instr, hlen] using h₃

/-- Entering a loop installs the generated label with the exact saved stack
height, parameter values, and continuation. -/
theorem loop_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after body : List instr) (baseValues args : List val)
    (bt : blocktype) (params results : List valtype)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues) (hargs : Forall wf_val args)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (hiOp : wf_instr (.LOOP bt body))
    (hbt : fun_blocktype ⟨s, f.toFrame⟩ bt = ⟨.mk_list params, .mk_list results⟩)
    (hlen : args.length = params.length) :
    StepH (decode ⟨s, ambient,
      { f with code := .LOOP bt body :: after, vals := baseValues ++ args } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := body, vals := baseValues ++ args, labels := ⟨params, results, [.LOOP bt body], baseValues.length, after⟩ :: f.labels } :: rest, []⟩) := by
  have hbody : Forall wf_instr body := by cases hiOp; assumption
  have hlabel : wf_admininstr (.LABEL_ params.length [.LOOP bt body] (vals args ++ body.map admininstr_instr)) :=
    .admininstr_case_71 _ _ _ (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hiOp) (forall_append (wf_vals hargs) (wf_instrs hbody))
  have hsource : wf_config ⟨⟨s, f.toFrame⟩, vals args ++ [.LOOP bt body]⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hargs)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact wf_admininstr_instr hiOp))
  have htarget : wf_config ⟨⟨s, f.toFrame⟩, [.LABEL_ params.length [.LOOP bt body] (vals args ++ body.map admininstr_instr)]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hlabel)
  have read := Step_read.loop ⟨s, f.toFrame⟩ params.length args bt body params results.length results
    hbt hsource hlabel hlen.symm rfl rfl
  have step : StepH ⟨⟨s, f.toFrame⟩, vals args ++ [.LOOP bt body]⟩ []
      ⟨⟨s, f.toFrame⟩, [.LABEL_ params.length [.LOOP bt body] (vals args ++ body.map admininstr_instr)]⟩ :=
    .step (.read _ _ _ read hsource htarget)
  have h₁ := step_h_instrs step [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₂ := step_h_decode_labels h₁ f.labels baseValues hl hv
  have h₃ := step_h_active ambient rest f.arity h₂ ha hr
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity]
  rw [decode_labels_move_values _ _ _ _ heights]
  simpa [decodeLabels, Label.arity, instrContext, vals, List.append_assoc, AFrame.arity,
    AFrame.toFrame, admininstr_instr, hlen] using h₃

/-- Completing a label removes exactly that administrative wrapper, preserving
the saved prefix and the values produced by its body. -/
theorem label_exit_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (label : Label) (labels : List Label)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf (label :: labels)) (hv : Forall wf_val f.vals)
    (hr : Forall FrameWf rest)
    (hheight : label.height ≤ f.vals.length)
    (heights : ∀ outer ∈ labels, outer.height ≤ label.height) :
    StepH (decode ⟨s, ambient,
      { f with code := [], labels := label :: labels } :: rest, []⟩) []
      (decode ⟨s, ambient,
      { f with code := label.after, labels := labels } :: rest, []⟩) := by
  have hlabel := hl label (by simp)
  have htail : LabelsWf labels := fun l hm => hl l (by simp [hm])
  have hbefore : Forall wf_val (f.vals.take label.height) := fun v hm => hv v (List.mem_of_mem_take hm)
  have hafter : Forall wf_val (f.vals.drop label.height) := fun v hm => hv v (List.mem_of_mem_drop hm)
  have hwrap : wf_admininstr (.LABEL_ label.arity label.cont (vals (f.vals.drop label.height))) :=
    .admininstr_case_71 _ _ _ hlabel.1 (wf_vals hafter)
  have hsource : wf_config ⟨⟨s, f.toFrame⟩, [.LABEL_ label.arity label.cont (vals (f.vals.drop label.height))]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hwrap)
  have htarget := wf_config_vals hs hf hafter
  have step : StepH ⟨⟨s, f.toFrame⟩, [.LABEL_ label.arity label.cont (vals (f.vals.drop label.height))]⟩ []
      ⟨⟨s, f.toFrame⟩, vals (f.vals.drop label.height)⟩ :=
    .step (.pure _ _ _ (.label_vals _ _ _ hwrap) hsource htarget)
  have h₁ := step_h_instrs step [] (label.after.map admininstr_instr) (forall_nil _) (wf_instrs hlabel.2)
  have h₂ := step_h_decode_labels h₁ labels (f.vals.take label.height) htail hbefore
  have h₃ := step_h_active ambient rest f.arity h₂ ha hr
  have hm := decode_labels_move_values labels (f.vals.take label.height) (f.vals.drop label.height)
    (label.after.map admininstr_instr) (by
      intro l hl
      simpa only [List.length_take, Nat.min_eq_left hheight] using heights l hl)
  rw [List.take_append_drop] at hm
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, AFrame.toFrame, AFrame.arity]
  rw [hm]
  simpa [decodeLabels, instrContext, vals, AFrame.arity, AFrame.toFrame] using h₃

end Itasca.Runtime.SourceMachine

end
