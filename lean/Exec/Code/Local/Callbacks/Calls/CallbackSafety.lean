import Exec.Code.Local.Relations.Control.ControlLayout

/-! Raw compiler operand safety, including polymorphic bottom values. These
facts concern every normal observation outcome; they do not assume a final
accepted body or a concrete validator operand stack. -/
namespace Exec.Code
open Aeneas Aeneas.Std

structure ObservedStack {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (values : List Itasca.code.StackType) : Prop where
  offsets : compiler.before.val.map (fun word => word.val) =
    observedOffsets compiler.function.local_slots.val values
  height : compiler.height.val =
    compiler.function.local_slots.val + stackWords values

theorem observedHeight_stackWords (height : Nat) (values : List Itasca.code.StackType) :
    observedHeight height values = height + stackWords values := by
  induction values generalizing height with
  | nil => simp [observedHeight, stackWords]
  | cons ty rest ih => simp [observedHeight, stackWords, ih, Nat.add_assoc]

theorem observedOffsets_length (height : Nat) (values : List Itasca.code.StackType) :
    (observedOffsets height values).length = values.length := by
  induction values generalizing height with
  | nil => rfl
  | cons ty rest ih => simp [observedOffsets, ih]

theorem observedOffsets_get (height : Nat) (values : List Itasca.code.StackType)
    (index : Nat) (bound : index < values.length) :
    (observedOffsets height values)[index]'(by rw [observedOffsets_length]; exact bound) =
      height + stackWords (values.take index) := by
  induction values generalizing height index with
  | nil => simp at bound
  | cons ty rest ih =>
    cases index with
    | zero => simp [observedOffsets, stackWords]
    | succ index =>
      simp only [observedOffsets, List.getElem_cons_succ, List.take_succ_cons]
      rw [ih _ _ (by simpa using bound)]
      simp [stackWords, Nat.add_assoc]

theorem ObservedStack.length {A} {compiler : runtime.compiler.FunctionCompiler A} {values}
    (h : ObservedStack compiler values) : compiler.before.val.length = values.length := by
  have length := congrArg List.length h.offsets
  simpa [observedOffsets_length] using length

theorem ObservedStack.get {A} {compiler : runtime.compiler.FunctionCompiler A} {values}
    (h : ObservedStack compiler values) (index : Nat) (bound : index < compiler.before.val.length) :
    (compiler.before.val[index]).val = compiler.function.local_slots.val +
      stackWords (values.take index) := by
  have mapped := congrArg (fun xs : List Nat => xs[index]?) h.offsets
  have vb : index < values.length := by rw [← h.length]; exact bound
  have ob : index < (observedOffsets compiler.function.local_slots.val values).length := by
    rw [observedOffsets_length]; exact vb
  have result : (compiler.before.val[index]).val =
      (observedOffsets compiler.function.local_slots.val values)[index] := by
    simpa only [List.getElem?_map, List.getElem?_eq_getElem bound, Option.map_some,
      List.getElem?_eq_getElem ob, Option.some.injEq] using mapped
  exact result.trans (observedOffsets_get _ _ _ vb)

theorem ObservedStack.operand_le_height {A} {compiler : runtime.compiler.FunctionCompiler A} {values}
    (h : ObservedStack compiler values) (index : Nat) (bound : index < compiler.before.val.length) :
    (compiler.before.val[index]).val ≤ compiler.height.val := by
  rw [h.get index bound, h.height]
  have length := h.length
  have le := stackWords_take_mono values (a := index) (b := values.length) (by omega)
  simpa using Nat.add_le_add_left le compiler.function.local_slots.val

theorem ObservedStack.ordered {A} {compiler : runtime.compiler.FunctionCompiler A} {values}
    (h : ObservedStack compiler values) (left right : Nat)
    (leftBound : left < compiler.before.val.length)
    (rightBound : right < compiler.before.val.length) (order : left ≤ right) :
    (compiler.before.val[left]).val ≤ (compiler.before.val[right]).val := by
  rw [h.get left leftBound, h.get right rightBound]
  exact Nat.add_le_add_left (stackWords_take_mono values order) _

@[step] theorem compiler_observe_stack {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) :
    runtime.compiler.FunctionCompiler.observe ops compiler state ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  step with compiler_observe ops law compiler state as ⟨out, observed⟩
  rename_i success
  obtain ⟨offsets, height, _, locals, _⟩ := observed success
  exact ⟨by simpa [locals] using offsets,
    by simpa [locals, observedHeight_stackWords] using height⟩

@[step] theorem operand_at_total (before : Slice U32) (depth : Usize) :
    runtime.compiler.operand_at before depth ⦃ out =>
      ∀ word, out = .Ok word → word ∈ before.val ⦄ := by
  by_cases zero : depth = 0#usize
  · simp [runtime.compiler.operand_at, zero, WP.spec_ok]
  · by_cases large : depth > Slice.len before
    · simp [runtime.compiler.operand_at, zero, large, WP.spec_ok]
    · have positive : 0 < depth.val := by scalar_tac
      have fits : depth.val ≤ before.val.length := by scalar_tac
      step with operand_at before depth positive fits as ⟨out, exactValue⟩
      rename_i word success
      rw [success] at exactValue
      cases exactValue
      exact List.getElem_mem _

@[step] theorem observed_stack_height {A} {compiler : runtime.compiler.FunctionCompiler A}
    (values : Slice Itasca.code.StackType) (observed : ObservedStack compiler values.val)
    (count : Usize) (bound : count.val ≤ values.val.length) :
    runtime.compiler.control.stack_height values count compiler.function.local_slots ⦃ out =>
      out.val = compiler.function.local_slots.val + stackWords (values.val.take count.val) ⦄ := by
  apply control_stack_height values count compiler.function.local_slots bound
  have mono := stackWords_take_mono values.val (a := count.val) (b := values.val.length) bound
  have max : compiler.height.val ≤ U32.max := by scalar_tac
  rw [observed.height] at max
  simp only [List.take_length] at mono
  omega

end Exec.Code
