import Itasca.TypeTranslation

open Aeneas Aeneas.Std

namespace Itasca.Control

/-- Wasm 1.0 blocks have zero or one result and no input parameters. -/
def results : code.BlockType → List types.ValueType
  | .Empty => []
  | .Value t => [t]

def blockType : code.BlockType → blocktype
  | .Empty => ._RESULT none
  | .Value t => ._RESULT (some (Translate.valueType t))

def resultTypes (bt : code.BlockType) : List valtype :=
  (results bt).map Translate.valueType

/-- A loop label takes its inputs, which are empty in Wasm 1.0. -/
def targetBlockType (c : code.Ctrl) : code.BlockType :=
  match c.kind with
  | .Loop => .Empty
  | _ => c.block_type

def targetTypes (c : code.Ctrl) : List types.ValueType := results (targetBlockType c)

/-- Rust appends frames; the specification puts the innermost label first. -/
def labels (cs : List code.Ctrl) : List resulttype :=
  cs.reverse.map (fun c => .mk_list ((targetTypes c).map Translate.valueType))

def frame (st : code.OpIterState) (kind : code.LabelKind) (bt : code.BlockType) : code.Ctrl :=
  ⟨kind, bt, alloc.vec.Vec.len st.vals, false⟩

def base (st : code.OpIterState) : Usize :=
  match st.ctrls.val.getLast? with
  | none => 0#usize
  | some c => c.value_stack_base

def polymorphic (st : code.OpIterState) : Bool :=
  match st.ctrls.val.getLast? with
  | none => false
  | some c => c.polymorphic_base

/-- Structural stack bounds, separate from the eventual instruction-typing invariant. -/
structure Shape (st : code.OpIterState) : Prop where
  ordered : st.ctrls.val.Pairwise (fun c d => c.value_stack_base.val ≤ d.value_stack_base.val)
  bounded : ∀ c ∈ st.ctrls.val, c.value_stack_base.val ≤ st.vals.val.length

theorem blockType_wf (bt : code.BlockType) : wf_blocktype (blockType bt) := by
  cases bt <;> exact .blocktype_case_0 _

theorem blockType_ok (C : context) (hC : wf_context C) (bt : code.BlockType) :
    Blocktype_ok C (blockType bt) (.mk_functype (.mk_list []) (.mk_list (resultTypes bt))) := by
  cases bt <;> exact .valtype C _ hC (.blocktype_case_0 _)

theorem labels_push (cs : List code.Ctrl) (c : code.Ctrl) :
    labels (cs ++ [c]) = .mk_list ((targetTypes c).map Translate.valueType) :: labels cs := by
  simp [labels]

theorem Shape.base_le {st : code.OpIterState} (h : Shape st) :
    (base st).val ≤ st.vals.val.length := by
  unfold base
  split
  · simp
  · rename_i c hc
    exact h.bounded c (List.mem_of_getLast? hc)

theorem Shape.push {st st' : code.OpIterState} (h : Shape st)
    (kind : code.LabelKind) (bt : code.BlockType)
    (hctrls : st'.ctrls.val = st.ctrls.val ++ [frame st kind bt])
    (hvals : st'.vals = st.vals) : Shape st' := by
  constructor
  · rw [hctrls, List.pairwise_append]
    exact ⟨h.ordered, by simp, by simpa [frame] using h.bounded⟩
  · intro c hc
    rw [hctrls] at hc
    rcases List.mem_append.mp hc with hc | hc
    · simpa [hvals] using h.bounded c hc
    · have heq : c = frame st kind bt := by simpa using hc
      simp [heq, frame, hvals]

theorem labels_lookup (cs : List code.Ctrl) (depth : Nat) (h : depth < cs.length) :
    (labels cs)[depth]'(by simpa [labels] using h) =
      .mk_list ((targetTypes (cs[cs.length - 1 - depth]'(by omega))).map Translate.valueType) := by
  simp [labels, List.getElem_reverse]

theorem Shape.unreachable {st st' : code.OpIterState} (h : Shape st)
    (cs : List code.Ctrl) (c : code.Ctrl)
    (hctrls : st.ctrls.val = cs ++ [c])
    (hctrls' : st'.ctrls.val = cs ++ [{ c with polymorphic_base := true }])
    (hlen : st'.vals.val.length = c.value_stack_base.val) : Shape st' := by
  have hord := h.ordered
  rw [hctrls, List.pairwise_append] at hord
  constructor
  · simpa [hctrls', List.pairwise_append] using hord
  · intro d hd
    rw [hctrls'] at hd
    rcases List.mem_append.mp hd with hd | hd
    · rw [hlen]
      exact hord.2.2 d hd c (by simp)
    · have heq : d = { c with polymorphic_base := true } := by simpa using hd
      simp [heq, hlen]

end Itasca.Control

namespace Itasca

@[step]
theorem code.block_results.spec (bt : code.BlockType) :
    code.block_results bt ⦃ (v : alloc.vec.Vec types.ValueType) => v.val = Control.results bt ⦄ := by
  cases bt with
  | Empty => simp [code.block_results, Control.results]
  | Value t =>
    unfold code.block_results
    step*
    simp_all [Control.results]

@[step]
theorem code.branch_target_bt.spec (c : code.Ctrl) :
    code.branch_target_bt c ⦃ (bt : code.BlockType) => bt = Control.targetBlockType c ⦄ := by
  cases c with
  | mk kind bt base poly => cases kind <;> simp [code.branch_target_bt, Control.targetBlockType]

@[step]
theorem code.branch_target_types.spec (c : code.Ctrl) :
    code.branch_target_types c ⦃ (v : alloc.vec.Vec types.ValueType) => v.val = Control.targetTypes c ⦄ := by
  unfold code.branch_target_types
  step*
  simp_all [Control.targetTypes]

@[step]
theorem code.push_ctrl.spec (st : code.OpIterState) (kind : code.LabelKind) (bt : code.BlockType)
    (hsize : st.ctrls.val.length < Usize.max) :
    code.push_ctrl st kind bt ⦃ (st' : code.OpIterState) =>
      st'.ctrls.val = st.ctrls.val ++ [Control.frame st kind bt] ∧
      st'.vals = st.vals ∧ st'.pos = st.pos ⦄ := by
  unfold code.push_ctrl
  step*
  simp_all [Control.frame]

@[step]
theorem code.cur_base.spec (st : code.OpIterState) :
    code.cur_base st ⦃ (b : Usize) => b = Control.base st ⦄ := by
  rcases List.eq_nil_or_concat' st.ctrls.val with h | ⟨cs, c, h⟩
  · unfold code.cur_base
    have hn : alloc.vec.Vec.len st.ctrls = 0#usize := by scalar_tac
    simp only [hn, ↓reduceIte]
    simp [Control.base, h]
  · unfold code.cur_base
    have hn : alloc.vec.Vec.len st.ctrls ≠ 0#usize := by scalar_tac
    simp only [hn, ↓reduceIte]
    step*
    simp_all [Control.base]

@[step]
theorem code.cur_polymorphic.spec (st : code.OpIterState) :
    code.cur_polymorphic st ⦃ (b : Bool) => b = Control.polymorphic st ⦄ := by
  rcases List.eq_nil_or_concat' st.ctrls.val with h | ⟨cs, c, h⟩
  · unfold code.cur_polymorphic
    have hn : alloc.vec.Vec.len st.ctrls = 0#usize := by scalar_tac
    simp only [hn, ↓reduceIte]
    simp [Control.polymorphic, h]
  · unfold code.cur_polymorphic
    have hn : alloc.vec.Vec.len st.ctrls ≠ 0#usize := by scalar_tac
    simp only [hn, ↓reduceIte]
    step*
    simp_all [Control.polymorphic]

end Itasca
