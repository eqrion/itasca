import Itasca.Support.Result
import Itasca.Binary.Leb128

/-!
Sections, each formerly its own module: Control, Unreachable, EnvReaders.
-/

/-! ## Control -/

section

/-!
# Control frames

Control-frame vocabulary over the extracted `code.OpIterState`: `base`, `polymorphic`, and the
structural invariant `Control.Shape`, with specifications for `code.cur_base` and
`code.cur_polymorphic`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Control

/-- The operand stack base of the innermost frame, or `0` with no frames. -/
def base (st : code.OpIterState) : Usize :=
  match st.ctrls.val.getLast? with
  | none => 0#usize
  | some c => c.value_stack_base

/-- Whether the innermost frame is unreachable; `false` with no frames. -/
def polymorphic (st : code.OpIterState) : Bool :=
  match st.ctrls.val.getLast? with
  | none => false
  | some c => c.polymorphic_base

/-- The structural invariant of the control stack: frame stack bases are ordered and within the
operand stack. -/
structure Shape (st : code.OpIterState) : Prop where
  ordered : st.ctrls.val.Pairwise (fun c d => c.value_stack_base.val ≤ d.value_stack_base.val)
  bounded : ∀ c ∈ st.ctrls.val, c.value_stack_base.val ≤ st.vals.val.length

/-- The current frame base is within the operand stack. -/
theorem Shape.base_le {st : code.OpIterState} (h : Shape st) :
    (base st).val ≤ st.vals.val.length := by
  unfold base
  split
  · simp
  · rename_i c hc
    exact h.bounded c (List.mem_of_getLast? hc)

/-- Truncating the operands to the innermost frame base and marking it polymorphic preserves
`Shape`. -/
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

end

/-! ## Unreachable -/

section

/-!
# Unreachable code handling

Specifications of `code.mark_unreachable_loop` and `code.mark_unreachable`, which truncate the
operand stack to the innermost frame base and make that frame polymorphic. In such a frame
`code.pop_stack_type` and `code.pop_with_type` return `Bot` at the base without consuming
operands.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `Vec.pop` returns the last element and removes it. -/
@[step]
theorem vec_pop_spec {T : Type} (allocator : Type) (v : alloc.vec.Vec T) :
    alloc.vec.Vec.pop allocator v ⦃ (r : Option T × alloc.vec.Vec T) =>
      r.1 = v.val.getLast? ∧ r.2.val = v.val.dropLast ⦄ := by
  simp [alloc.vec.Vec.pop]

/-- `code.mark_unreachable_loop` terminates and removes exactly the operands above `base`. -/
@[step]
theorem code.mark_unreachable_loop.spec (st : code.OpIterState) (base : Usize)
    (hbase : base.val ≤ st.vals.val.length) :
    code.mark_unreachable_loop st base ⦃ r =>
      r.1.val = st.vals.val.take base.val ∧ r.1.val.length = base.val ∧
      r.2.1 = st.ctrls ∧ r.2.2 = st.pos ⦄ := by
  unfold code.mark_unreachable_loop
  apply loop.spec_decr_nat (fun s => s.vals.val.length)
    (fun s => base.val ≤ s.vals.val.length ∧
      s.vals.val.take base.val = st.vals.val.take base.val ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos)
  · intro s ⟨hlen, htake, hctrls, hpos⟩
    unfold code.mark_unreachable_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : s.vals.val.length = base.val := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨by simpa [← heq] using htake, heq, hctrls, hpos⟩
    · rename_i hmore
      have hlt : base.val < s.vals.val.length := by scalar_tac
      step*
      simp_all only [List.length_dropLast]
      refine ⟨by omega, ?_, trivial, trivial, by omega⟩
      simpa [List.dropLast_eq_take, List.take_take,
        Nat.min_eq_left (by omega : base.val ≤ s.vals.val.length - 1)] using htake
  · exact ⟨hbase, rfl, rfl, rfl⟩

/-- `code.mark_unreachable` drops the operands above the innermost frame base and makes only that
frame polymorphic. -/
@[step]
theorem code.mark_unreachable.spec (st : code.OpIterState) (cs : List code.Ctrl) (c : code.Ctrl)
    (hctrls : st.ctrls.val = cs ++ [c])
    (hbase : c.value_stack_base.val ≤ st.vals.val.length) :
    code.mark_unreachable st ⦃ st' =>
      st'.vals.val = st.vals.val.take c.value_stack_base.val ∧
      st'.vals.val.length = c.value_stack_base.val ∧
      st'.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      st'.pos = st.pos ⦄ := by
  unfold code.mark_unreachable
  have hb : Control.base st = c.value_stack_base := by simp [Control.base, hctrls]
  step*
  simp_all

/-- With no operands above the frame base, `code.pop_stack_type` returns `Bot` in a polymorphic
frame and `EmptyStack` otherwise, leaving the state unchanged. -/
theorem code.pop_stack_type.at_base (st : code.OpIterState)
    (hbase : alloc.vec.Vec.len st.vals = Control.base st) :
    code.pop_stack_type st = .ok
      (if Control.polymorphic st then (.Ok .Bot, st) else (.Err .EmptyStack, st)) := by
  obtain ⟨_, hb, rfl⟩ := WP.spec_imp_exists (code.cur_base.spec st)
  obtain ⟨_, hp, rfl⟩ := WP.spec_imp_exists (code.cur_polymorphic.spec st)
  cases h : Control.polymorphic st <;> simp [code.pop_stack_type, hb, hbase, hp, h]

end Itasca

end

/-! ## EnvReaders -/

section

/-!
# Environment readers

Specifications of the small extracted readers that look up module and function state:
`code.local_type`, `code.global_type`, `code.take_local`, `code.take_global`, `code.take_index`,
`code.read_reserved_zero`, `code.require_memory`, `code.require_single_result`,
`code.read_memarg` and `code.check_memory_and_alignment`. Each states the exact LEB128 byte
provenance, which stacks it leaves alone, and the rejection cases.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `code.local_type` returns the local's type, or `UnknownLocal` for an out-of-range index. -/
theorem code.local_type.spec (ctx : code.Context) (idx : U32) :
    code.local_type ctx idx ⦃ r =>
      match r with
      | .Ok t => ∃ hi : idx.val < ctx.locals.val.length, ctx.locals.val[idx.val] = t
      | .Err e => e = .UnknownLocal ∧ ctx.locals.val.length ≤ idx.val ⦄ := by
  unfold code.local_type
  step*

/-- `code.global_type` returns the global's type, or `UnknownGlobal` for an out-of-range index. -/
theorem code.global_type.spec (env : metadata.Env) (idx : U32) :
    code.global_type env idx ⦃ r =>
      match r with
      | .Ok gt => ∃ hi : idx.val < env.global_types.val.length, env.global_types.val[idx.val] = gt
      | .Err e => e = .UnknownGlobal ∧ env.global_types.val.length ≤ idx.val ⦄ := by
  unfold code.global_type
  step*

/-- `code.take_local` decodes a local index with exact byte provenance and leaves both stacks
alone. It rejects with the LEB128 error or `UnknownLocal`. -/
theorem code.take_local.spec (st : code.OpIterState) (data : Slice U8) (ctx : code.Context) :
    code.take_local st data ctx ⦃ r =>
      r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok (idx, t) => Leb128.Decoded data st.pos idx r.2.pos ∧
          ∃ hi : idx.val < ctx.locals.val.length, ctx.locals.val[idx.val] = t
      | .Err e => (Leb128.Rejected data st.pos e ∧ r.2.pos = st.pos) ∨
          (e = .UnknownLocal ∧ ∃ idx, Leb128.Decoded data st.pos idx r.2.pos ∧
            ctx.locals.val.length ≤ idx.val) ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  cases r with
  | Err e =>
      simp [code.take_local, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact Or.inl hp
  | Ok pair =>
      obtain ⟨idx, next⟩ := pair
      obtain ⟨r, ht, htype⟩ := WP.spec_imp_exists (code.local_type.spec ctx idx)
      cases r with
      | Ok t =>
          simp [code.take_local, hr, ht, core.result.Result.Insts.CoreOpsTry.branch]
          exact ⟨hp, htype⟩
      | Err e =>
          simp [code.take_local, hr, ht, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          exact Or.inr ⟨htype.1, idx, hp, htype.2⟩

/-- `code.take_global` decodes a global index with exact byte provenance and leaves both stacks
alone. It rejects with the LEB128 error or `UnknownGlobal`. -/
theorem code.take_global.spec (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
    code.take_global st data env ⦃ r =>
      r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok (idx, gt) => Leb128.Decoded data st.pos idx r.2.pos ∧
          ∃ hi : idx.val < env.global_types.val.length, env.global_types.val[idx.val] = gt
      | .Err e => (Leb128.Rejected data st.pos e ∧ r.2.pos = st.pos) ∨
          (e = .UnknownGlobal ∧ ∃ idx, Leb128.Decoded data st.pos idx r.2.pos ∧
            env.global_types.val.length ≤ idx.val) ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  cases r with
  | Err e =>
      simp [code.take_global, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact Or.inl hp
  | Ok pair =>
      obtain ⟨idx, next⟩ := pair
      obtain ⟨r, ht, htype⟩ := WP.spec_imp_exists (code.global_type.spec env idx)
      cases r with
      | Ok gt =>
          simp [code.take_global, hr, ht, core.result.Result.Insts.CoreOpsTry.branch]
          exact ⟨hp, htype⟩
      | Err e =>
          simp [code.take_global, hr, ht, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          exact Or.inr ⟨htype.1, idx, hp, htype.2⟩

/-- `code.take_index` decodes an unsigned immediate with exact byte provenance and leaves both
stacks alone. -/
theorem code.take_index.spec (st : code.OpIterState) (data : Slice U8) :
    code.take_index st data ⦃ r =>
      r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok idx => Leb128.Decoded data st.pos idx r.2.pos
      | .Err e => Leb128.Rejected data st.pos e ∧ r.2.pos = st.pos ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  cases r with
  | Err e =>
      simpa [code.take_index, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (show Leb128.Rejected data st.pos e from hp)
  | Ok pair =>
      obtain ⟨idx, next⟩ := pair
      simpa [code.take_index, hr, core.result.Result.Insts.CoreOpsTry.branch] using (show Leb128.Decoded data st.pos idx next from hp)

/-- `code.read_reserved_zero` consumes one byte that is `0`, and otherwise rejects with
`UnexpectedEof` or `ReservedByteNotZero`. -/
theorem code.read_reserved_zero.spec (st : code.OpIterState) (data : Slice U8) :
    code.read_reserved_zero st data ⦃ r =>
      r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok _ => ∃ hp : st.pos.val < data.length,
          data.val[st.pos.val] = 0#u8 ∧ r.2.pos.val = st.pos.val + 1
      | .Err e => r.2 = st ∧
          ((e = .UnexpectedEof ∧ data.length ≤ st.pos.val) ∨
            (e = .ReservedByteNotZero ∧ ∃ hp : st.pos.val < data.length,
              data.val[st.pos.val] ≠ 0#u8)) ⦄ := by
  by_cases hp : st.pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.pos hp)
    by_cases hz : data.val[st.pos.val] = 0#u8
    · simp [code.read_reserved_zero, hr, core.result.Result.Insts.CoreOpsTry.branch, hz]
      exact ⟨hp, hn⟩
    · have hzval : (data.val[st.pos.val]).val ≠ 0 := by scalar_tac
      simp [code.read_reserved_zero, hr, core.result.Result.Insts.CoreOpsTry.branch, hz, hzval]
      exact hp
  · have heof := reader.read_byte.eof data st.pos (by omega)
    simp [code.read_reserved_zero, heof, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    simpa using Nat.le_of_not_gt hp

/-- `code.require_memory` succeeds exactly when the environment has a memory. -/
theorem code.require_memory.spec (env : metadata.Env) :
    code.require_memory env ⦃ r =>
      match r with
      | .Ok _ => 0 < env.mem_types.val.length
      | .Err e => e = .UnknownMemory ∧ env.mem_types.val = [] ⦄ := by
  unfold code.require_memory alloc.vec.Vec.is_empty
  step*
  all_goals simp_all
  exact List.length_pos_iff.mpr (by assumption)

/-- `code.read_memarg` decodes the alignment and offset together. A malformed offset leaves the
state unchanged, even after a successfully decoded alignment. -/
theorem code.read_memarg.spec (st : code.OpIterState) (data : Slice U8) :
    code.read_memarg st data ⦃ r =>
      r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok arg => ∃ middle, Leb128.Decoded data st.pos arg.align middle ∧
          Leb128.Decoded data middle arg.offset r.2.pos
      | .Err e => r.2 = st ∧ (Leb128.Rejected data st.pos e ∨
          ∃ align middle, Leb128.Decoded data st.pos align middle ∧ Leb128.Rejected data middle e) ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  cases r with
  | Err e =>
      simp [code.read_memarg, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact Or.inl hp
  | Ok pair =>
      obtain ⟨align, middle⟩ := pair
      obtain ⟨r, hr', hp'⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data middle)
      cases r with
      | Err e =>
          simp [code.read_memarg, hr, hr', core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          exact Or.inr ⟨align, middle, hp, hp'⟩
      | Ok pair =>
          obtain ⟨offset, next⟩ := pair
          simp [code.read_memarg, hr, hr', core.result.Result.Insts.CoreOpsTry.branch]
          exact ⟨middle, hp, hp'⟩

/-- `code.check_memory_and_alignment` requires a memory and an alignment at most `natural`, and
rejects with `UnknownMemory` or `InvalidAlignment`. -/
theorem code.check_memory_and_alignment.spec (env : metadata.Env) (arg : code.MemArg)
    (natural : U32) :
    code.check_memory_and_alignment env arg natural ⦃ r =>
      match r with
      | .Ok _ => 0 < env.mem_types.val.length ∧ arg.align.val ≤ natural.val
      | .Err e => (e = .UnknownMemory ∧ env.mem_types.val = []) ∨
          (e = .InvalidAlignment ∧ 0 < env.mem_types.val.length ∧ natural.val < arg.align.val) ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.require_memory.spec env)
  cases r with
  | Err e =>
      simp [code.check_memory_and_alignment, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      exact Or.inl hp
  | Ok u =>
      simp only [code.check_memory_and_alignment, hr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      split <;> simp only [WP.spec_ok] <;> scalar_tac

end Itasca

end
