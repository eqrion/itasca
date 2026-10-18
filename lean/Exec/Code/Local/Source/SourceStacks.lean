import Exec.Code.Local.Relations.Common.EntryTypedSteps
namespace Exec.Code
open Aeneas Aeneas.Std
open Itasca

/-- A reachable compiler prefix retains concrete validator operands. This is
an invariant of actual steps, not a consequence of source typing alone. -/
def ConcreteStack (values : List code.StackType) : Prop :=
  ∀ value ∈ values, value ≠ .Bot

theorem concreteStack_iff (values : List code.StackType) :
    ConcreteStack values ↔ ∃ types : List Itasca.types.ValueType, values = types.map code.StackType.Val := by
  induction values with
  | nil => simp [ConcreteStack]
  | cons value rest ih =>
    cases value with
    | Bot =>
      simp only [ConcreteStack, List.mem_cons, forall_eq_or_imp, ne_eq, not_true_eq_false, false_and, false_iff, not_exists]
      intro types
      cases types <;> simp
    | Val ty =>
      constructor
      · intro concrete
        obtain ⟨types, rfl⟩ := ih.mp (fun v member => concrete v (by simp [member]))
        exact ⟨ty :: types, rfl⟩
      · rintro ⟨types, equality⟩
        intro v member eq
        subst v
        rw [equality] at member
        simp at member

theorem concreteStack_append {left right : List code.StackType} :
    ConcreteStack (left ++ right) ↔ ConcreteStack left ∧ ConcreteStack right := by
  simp [ConcreteStack, or_imp, forall_and]

theorem wasm1_spine_values {root parents C outer form}
    (spine : Wasm1.Frames.Spine root parents C outer form) :
    outer = parents.flatMap Wasm1.Frames.Saved.vals := by
  induction spine with
  | root => rfl
  | push parents parentC outer parent child spine header base resume notBody ih =>
    simp [List.flatMap_append, ih]

theorem wasm2_spine_values {env root parents C outer form inputs}
    (spine : Wasm2.Frames.Spine env root parents C outer form inputs) :
    outer = parents.flatMap Wasm2.Frames.Saved.vals := by
  induction spine with
  | root => rfl
  | push parents C outer parent child ins spine header base resume notBody ih =>
    simp [List.flatMap_append, ih]

/-- The live source frame has exactly the concrete operand types and base
observed by the compiler, while the parent zipper supplies its label context. -/
theorem wasm1_open_concrete {root st parents current}
    (opened : Wasm1.Frames.Open root st parents current)
    (known : ConcreteStack st.vals.val) :
    ∃ (C : context) (outerTypes currentTypes : List Itasca.types.ValueType),
      Wasm1.Frames.Spine root parents C (outerTypes.map code.StackType.Val) current.form ∧
      Wasm1.Frames.Header C current ∧
      current.ctrl.value_stack_base.val = outerTypes.length ∧
      current.vals = currentTypes.map code.StackType.Val ∧
      st.vals.val = (outerTypes ++ currentTypes).map code.StackType.Val ∧
      st.ctrls.val = parents.map Wasm1.Frames.Saved.ctrl ++ [current.ctrl] ∧
      C.LABELS = Control.labels (parents.map Wasm1.Frames.Saved.ctrl) ++ root.LABELS ∧
      Instrs_ok (Wasm1.Frames.enter C current.form current.ctrl.block_type) current.ops
        (.mk_functype (.mk_list []) (.mk_list (currentTypes.map Translate.valueType))) := by
  obtain ⟨C, outer, spine, header, base, typed, controls, values⟩ := opened
  rw [values] at known
  obtain ⟨outerKnown, currentKnown⟩ := concreteStack_append.mp known
  obtain ⟨outerTypes, rfl⟩ := (concreteStack_iff outer).mp outerKnown
  obtain ⟨currentTypes, currentValues⟩ := (concreteStack_iff current.vals).mp currentKnown
  refine ⟨C, outerTypes, currentTypes, spine, header, by simpa using base,
    currentValues, ?_, controls, spine.labels, ?_⟩
  · simp [values, currentValues]
  · have source := typed.typed _ (Sequence.realizes_default current.ctrl.polymorphic_base current.vals)
    simpa [currentValues, Sequence.stackTypes, List.map_map, Function.comp_def] using source

/-- Multi-value frames retain their resolved parameter/result vectors, exact
base, concrete live operand segment, and generated source typing together. -/
theorem wasm2_open_concrete {env root st parents current}
    (opened : Wasm2.Frames.Open env root st parents current)
    (known : ConcreteStack st.core.vals.val) :
    ∃ (C : context) (outerTypes currentTypes : List Itasca.types.ValueType),
      Wasm2.Frames.Spine env root parents C (outerTypes.map code.StackType.Val) current.form current.ins ∧
      Wasm2.Frames.Header env C current ∧
      current.ctrl.value_stack_base.val = outerTypes.length ∧
      current.vals = currentTypes.map code.StackType.Val ∧
      st.core.vals.val = (outerTypes ++ currentTypes).map code.StackType.Val ∧
      st.core.ctrls.val = parents.map Wasm2.Frames.Saved.ctrl ++ [current.ctrl] ∧
      st.blocks.val = parents.map Wasm2.Frames.Saved.bt ++ [current.bt] ∧
      C.LABELS = Wasm2.Frames.labels parents ++ root.LABELS ∧
      C.TYPES = root.TYPES ∧ C.RETURN = root.RETURN ∧
      Wasm2.resolve env (Wasm2.target current.ctrl.kind current.bt) =
        some (match current.form with | .loop => current.ins | _ => current.outs) ∧
      Instrs_ok (Wasm2.Frames.enter C current.form current.ins current.outs) current.ops
        (.mk_functype (.mk_list ((current.form.params current.ins).map Translate.valueType))
          (.mk_list (currentTypes.map Translate.valueType))) := by
  obtain ⟨C, outer, spine, header, base, typed, controls, blocks, values⟩ := opened
  rw [values] at known
  obtain ⟨outerKnown, currentKnown⟩ := concreteStack_append.mp known
  obtain ⟨outerTypes, rfl⟩ := (concreteStack_iff outer).mp outerKnown
  obtain ⟨currentTypes, currentValues⟩ := (concreteStack_iff current.vals).mp currentKnown
  refine ⟨C, outerTypes, currentTypes, spine, header, by simpa using base,
    currentValues, ?_, controls, blocks, spine.labels, spine.types, spine.returns, header.target, ?_⟩
  · simp [values, currentValues]
  · have source := typed.typed _ (Sequence.realizes_default current.ctrl.polymorphic_base current.vals)
    simpa [currentValues, Sequence.stackTypes, List.map_map, Function.comp_def] using source
end Exec.Code
