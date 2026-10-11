import Itasca.Body.StackComplete
import Itasca.Binary.WasmBinaryComplete
import Itasca.Body.ControlFlow
import Itasca.Body.CoreBranch

open Aeneas Aeneas.Std

namespace Itasca

theorem Sequence.Realizes.empty_values {poly : Bool} {vals : List code.StackType}
    (h : Realizes poly vals []) : vals = [] := by
  obtain ⟨front, suffix, _, hp, he⟩ := h
  have hh := List.append_eq_nil_iff.mp he.symm
  rw [hh.2] at hp
  cases hp
  rfl

/-- An independently encoded block header forces successful frame entry. -/
theorem code.read_block.complete (st : code.OpIterState) (data : Slice U8)
    (bt : code.BlockType) (next : Usize)
    (hbytes : Wasm.BytesAt data st.pos [Control.blockByte bt] next)
    (hsize : st.ctrls.val.length < Usize.max) :
    code.read_block st data ⦃ r => r.1 = .Ok bt ∧ r.2.pos = next ∧
      r.2.vals = st.vals ∧
      r.2.ctrls.val = st.ctrls.val ++ [Control.frame st .Block bt] ⦄ := by
  obtain ⟨s, hp, hc, hv, hn⟩ := WP.spec_imp_exists
    (code.push_ctrl.spec { st with pos := next } .Block bt hsize)
  rw [WP.spec_equiv_exists]
  exact ⟨(.Ok bt, s), by simp [code.read_block, hbytes.read_block_type bt, hp,
    core.result.Result.Insts.CoreOpsTry.branch], rfl, hn, hv, hc⟩

theorem code.read_loop.complete (st : code.OpIterState) (data : Slice U8)
    (bt : code.BlockType) (next : Usize)
    (hbytes : Wasm.BytesAt data st.pos [Control.blockByte bt] next)
    (hsize : st.ctrls.val.length < Usize.max) :
    code.read_loop st data ⦃ r => r.1 = .Ok bt ∧ r.2.pos = next ∧
      r.2.vals = st.vals ∧
      r.2.ctrls.val = st.ctrls.val ++ [Control.frame st .Loop bt] ⦄ := by
  obtain ⟨s, hp, hc, hv, hn⟩ := WP.spec_imp_exists
    (code.push_ctrl.spec { st with pos := next } .Loop bt hsize)
  rw [WP.spec_equiv_exists]
  exact ⟨(.Ok bt, s), by simp [code.read_loop, hbytes.read_block_type bt, hp,
    core.result.Result.Insts.CoreOpsTry.branch], rfl, hn, hv, hc⟩

/-- A realizable i32 condition makes `if` succeed, retaining the realizable
parent operand prefix beneath the new frame's fresh operand base. -/
theorem code.read_if.complete (st : code.OpIterState) (data : Slice U8)
    (bt : code.BlockType) (next : Usize) (outer segment : List code.StackType)
    (ts : List valtype)
    (hbytes : Wasm.BytesAt data st.pos [Control.blockByte bt] next)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.ctrls.val.length < Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st) segment (ts ++ [.I32])) :
    code.read_if st data ⦃ r => r.1 = .Ok bt ∧ r.2.pos = next ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
        r.2.ctrls.val = st.ctrls.val ++ [Control.frame r.2 .Then bt] ∧
        Sequence.Realizes (Control.polymorphic st) rest ts ⦄ := by
  obtain ⟨t, popped, rest, hpop, hc, hp, hv, hl, _, ht'⟩ :=
    code.pop_with_type.complete { st with pos := next } outer segment ts .I32
      hvals hbase (by simpa [Control.polymorphic, Translate.valueType] using ht)
  obtain ⟨s, hpush, hcs, hvs, hps⟩ := WP.spec_imp_exists
    (code.push_ctrl.spec popped .Then bt (by simpa [hc] using hsize))
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok bt, s), ?_, rfl, hps.trans hp, rest, ?_, hl, ?_, ht'⟩
  · simp [code.read_if, hbytes.read_block_type bt, hpop, hpush,
      core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hvs] using hv
  · simpa [hc, Control.frame, hvs] using hcs

private theorem pop_results_complete (st : code.OpIterState)
    (cs : List code.Ctrl) (c : code.Ctrl) (outer segment : List code.StackType)
    (rs : alloc.vec.Vec types.ValueType)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (hrs : rs.val = Control.results c.block_type)
    (ht : Sequence.Realizes c.polymorphic_base segment (Control.resultTypes c.block_type)) :
    ∃ s, code.pop_types st (alloc.vec.Vec.deref rs) = .ok (.Ok (), s) ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ s.vals.val = outer := by
  obtain ⟨⟨_, s⟩, hr, rfl, hc, hp, rest, hv, _, ht'⟩ := WP.spec_imp_exists
    (code.pop_types.complete st outer segment [] (alloc.vec.Vec.deref rs) hvals
      (by simp [Control.base, hctrls, hbase])
      (by simpa [Control.polymorphic, hctrls, alloc.vec.Vec.deref, hrs,
        Control.resultTypes] using ht))
  have hn := ht'.empty_values
  exact ⟨s, hr, hc, hp, by simpa [hn] using hv⟩

/-- Declaratively matching frame results suffice for closing a frame, even
when its operands contain explicit or implicit Bot values. -/
theorem code.read_end.complete (st : code.OpIterState) (cs : List code.Ctrl)
    (c : code.Ctrl) (outer segment : List code.StackType)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (hthen : c.kind = .Then → c.block_type = .Empty)
    (hsize : outer.length + (Control.results c.block_type).length ≤ Usize.max)
    (ht : Sequence.Realizes c.polymorphic_base segment (Control.resultTypes c.block_type)) :
    code.read_end st ⦃ r => r.1 = .Ok (c.kind, c.block_type) ∧
      r.2.ctrls.val = cs ∧
      r.2.vals.val = outer ++ (Control.results c.block_type).map code.StackType.Val ∧
      r.2.pos = st.pos ⦄ := by
  obtain ⟨rs, hrs, hrsv⟩ := WP.spec_imp_exists (code.block_results.spec c.block_type)
  obtain ⟨popped, hpop, hc, hp, hv⟩ :=
    pop_results_complete st cs c outer segment rs hctrls hvals hbase hrsv ht
  have hlen : popped.vals.val.length = c.value_stack_base.val := by rw [hv, hbase]
  have hcap : popped.vals.val.length + rs.val.length ≤ Usize.max := by simpa [hv, hrsv] using hsize
  have hn : alloc.vec.Vec.len st.ctrls ≠ 0#usize := by scalar_tac
  unfold code.read_end
  simp only [hn, ↓reduceIte]
  step
  step
  have heq : frame = c := by simp_all
  rw [heq, hrs]
  simp only [bind_ok]
  cases hk : c.kind <;>
    simp [code.is_then, alloc.vec.Vec.is_empty, hthen, hk, hpop,
      core.result.Result.Insts.CoreOpsTry.branch, hlen]
  all_goals step*
  all_goals simp_all [alloc.vec.Vec.deref, Control.results]

/-- A typed then-arm closes successfully and starts an empty, reachable else-arm. -/
theorem code.read_else.complete (st : code.OpIterState) (cs : List code.Ctrl)
    (c : code.Ctrl) (outer segment : List code.StackType)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length) (hkind : c.kind = .Then)
    (ht : Sequence.Realizes c.polymorphic_base segment (Control.resultTypes c.block_type)) :
    code.read_else st ⦃ r => r.1 = .Ok c.block_type ∧
      r.2.ctrls.val = cs ++ [{ c with kind := .Else, polymorphic_base := false }] ∧
      r.2.vals.val = outer ∧ r.2.pos = st.pos ⦄ := by
  obtain ⟨rs, hrs, hrsv⟩ := WP.spec_imp_exists (code.block_results.spec c.block_type)
  obtain ⟨popped, hpop, hc, hp, hv⟩ :=
    pop_results_complete st cs c outer segment rs hctrls hvals hbase hrsv ht
  have hlen : popped.vals.val.length = c.value_stack_base.val := by rw [hv, hbase]
  have hn : alloc.vec.Vec.len st.ctrls ≠ 0#usize := by scalar_tac
  unfold code.read_else
  simp only [hn, ↓reduceIte]
  step
  step
  have heq : frame = c := by simp_all
  rw [heq]
  simp [code.is_then, hkind, hrs, hpop, core.result.Result.Insts.CoreOpsTry.branch, hlen]
  have hi : i.val = cs.length := by simpa [hctrls] using i_post
  step*
  all_goals simp_all [alloc.vec.Vec.set]

theorem code.read_return.complete (st : code.OpIterState) (ctx : code.Context)
    (cs : List code.Ctrl) (c : code.Ctrl) (outer segment : List code.StackType)
    (front : List valtype)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (ht : Sequence.Realizes c.polymorphic_base segment
      (front ++ ctx.results.val.map Translate.valueType)) :
    code.read_return st ctx ⦃ r => r.1 = .Ok () ∧ r.2.vals.val = outer ∧
      r.2.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧ r.2.pos = st.pos ⦄ := by
  obtain ⟨⟨_, s⟩, hr, rfl, hc, hp, rest, hv, _, _⟩ := WP.spec_imp_exists
    (code.pop_types.complete st outer segment front (alloc.vec.Vec.deref ctx.results) hvals
      (by simp [Control.base, hctrls, hbase])
      (by simpa [Control.polymorphic, hctrls, alloc.vec.Vec.deref] using ht))
  dsimp only at hc hp hv
  obtain ⟨s', hm, hv', _, hc', hp'⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec s cs c (by simpa [hc] using hctrls)
      (by simp [hv, hbase]))
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (), s'), ?_, rfl, ?_, hc', hp'.trans hp⟩
  · simp [code.read_return, hr, hm, core.result.Result.Insts.CoreOpsTry.branch]
  · simpa [hv, hbase] using hv'

/-- An encoded in-range branch with realizable target operands succeeds and
discards the current frame's operands. Loop targets use their empty signature. -/
theorem code.read_br.complete (st : code.OpIterState) (data : Slice U8)
    (depth : U32) (next : Usize) (target : code.Ctrl)
    (cs : List code.Ctrl) (c : code.Ctrl) (outer segment : List code.StackType)
    (front : List valtype) (hdecoded : Leb128.Decoded data st.pos depth next)
    (hdepth : depth.val < st.ctrls.val.length)
    (htarget : st.ctrls.val[st.ctrls.val.length - 1 - depth.val]'(by omega) = target)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (ht : Sequence.Realizes c.polymorphic_base segment
      (front ++ (Control.targetTypes target).map Translate.valueType)) :
    code.read_br st data ⦃ r => r.1 = .Ok (depth, Control.targetBlockType target) ∧
      r.2.vals.val = outer ∧
      r.2.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧ r.2.pos = next ⦄ := by
  obtain ⟨_, hlabel, rfl⟩ := WP.spec_imp_exists
    (code.read_label.from_leb st data depth next
      (reader.read_u32_leb.complete data st.pos depth next hdecoded) hdepth)
  rw [htarget] at hlabel
  obtain ⟨rs, hrs, hrsv⟩ := WP.spec_imp_exists (code.branch_target_types.spec target)
  obtain ⟨⟨_, s⟩, hr, rfl, hc, hp, rest, hv, _, _⟩ := WP.spec_imp_exists
    (code.pop_types.complete { st with pos := next } outer segment front (alloc.vec.Vec.deref rs) hvals
      (by simp [Control.base, hctrls, hbase])
      (by simpa [Control.polymorphic, hctrls, alloc.vec.Vec.deref, hrsv] using ht))
  dsimp only at hc hp hv
  obtain ⟨s', hm, hv', _, hc', hp'⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec s cs c (by simpa [hc] using hctrls)
      (by simp [hv, hbase]))
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (depth, Control.targetBlockType target), s'), ?_, rfl, ?_, hc', hp'.trans hp⟩
  · simp [code.read_br, hlabel, hrs, hr, hm, core.result.Result.Insts.CoreOpsTry.branch, code.branch_target_bt.eq]
  · simpa [hv, hbase] using hv'

/-- Conditional branching consumes its condition and restores the checked
target operands, retaining a realization of the declarative fallthrough stack. -/
theorem code.read_br_if.complete (st : code.OpIterState) (data : Slice U8)
    (depth : U32) (next : Usize) (target : code.Ctrl)
    (outer segment : List code.StackType) (front : List valtype)
    (hdecoded : Leb128.Decoded data st.pos depth next)
    (hdepth : depth.val < st.ctrls.val.length)
    (htarget : st.ctrls.val[st.ctrls.val.length - 1 - depth.val]'(by omega) = target)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st) segment
      ((front ++ (Control.targetTypes target).map Translate.valueType) ++ [.I32])) :
    code.read_br_if st data ⦃ r => r.1 = .Ok (depth, Control.targetBlockType target) ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = next ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
        Sequence.Realizes (Control.polymorphic st) rest
          (front ++ (Control.targetTypes target).map Translate.valueType) ⦄ := by
  obtain ⟨_, hlabel, rfl⟩ := WP.spec_imp_exists
    (code.read_label.from_leb st data depth next
      (reader.read_u32_leb.complete data st.pos depth next hdecoded) hdepth)
  rw [htarget] at hlabel
  obtain ⟨rs, hrs, hrsv⟩ := WP.spec_imp_exists (code.branch_target_types.spec target)
  obtain ⟨t, s, middle, hpop, hc, hp, hv, hlen, _, hmiddle⟩ :=
    code.pop_with_type.complete { st with pos := next } outer segment
      (front ++ (Control.targetTypes target).map Translate.valueType) .I32 hvals hbase
      (by simpa [Control.polymorphic, Translate.valueType] using ht)
  have hpoly : Control.polymorphic s = Control.polymorphic st := by simp [Control.polymorphic, hc]
  obtain ⟨⟨_, s'⟩, hr, rfl, hc', hp', rest, hv', hlen', ht'⟩ := WP.spec_imp_exists
    (code.pop_types.complete s outer middle front (alloc.vec.Vec.deref rs) hv
      (by simpa [Control.base, hc] using hbase)
      (by simpa [Control.polymorphic, hc, alloc.vec.Vec.deref, hrsv] using hmiddle))
  dsimp only at hc' hp' hv' hlen' ht'
  have hrslen : rs.val.length ≤ 1 := by simpa [hrsv] using Control.targetTypes_length target
  have hcap : s'.vals.val.length + (alloc.vec.Vec.deref rs).val.length ≤ Usize.max := by
    simp only [hvals, List.length_append] at hsize
    simp [hv', alloc.vec.Vec.deref]
    omega
  obtain ⟨s'', hpush, hv'', hc'', hp''⟩ := WP.spec_imp_exists
    (code.push_types.spec s' (alloc.vec.Vec.deref rs) hcap)
  rw [WP.spec_equiv_exists]
  refine ⟨(.Ok (depth, Control.targetBlockType target), s''), ?_, rfl,
    hc''.trans (hc'.trans hc), hp''.trans (hp'.trans hp),
    rest ++ rs.val.map code.StackType.Val, ?_, ?_, ?_⟩
  · simp [code.read_br_if, hlabel, hrs, hpop, hr, hpush, core.result.Result.Insts.CoreOpsTry.branch, code.branch_target_bt.eq]
  · simpa [hv', alloc.vec.Vec.deref, List.append_assoc] using hv''
  · simp only [List.length_append, List.length_map]
    omega
  · apply (Frames.realizes_append_concrete _ _ _ _).mpr
    exact ⟨front, by simpa [hpoly] using ht', by simp [hrsv]⟩

end Itasca
