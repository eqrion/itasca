import Itasca.Body.EnvTranslation
import Itasca.Binary.Leb128

open Aeneas Aeneas.Std

namespace Itasca

theorem code.local_type.spec (ctx : code.Context) (idx : U32) :
    code.local_type ctx idx ⦃ r =>
      match r with
      | .Ok t => ∃ hi : idx.val < ctx.locals.val.length, ctx.locals.val[idx.val] = t
      | .Err e => e = .UnknownLocal ∧ ctx.locals.val.length ≤ idx.val ⦄ := by
  unfold code.local_type
  step*

theorem code.global_type.spec (env : module.Env) (idx : U32) :
    code.global_type env idx ⦃ r =>
      match r with
      | .Ok gt => ∃ hi : idx.val < env.global_types.val.length, env.global_types.val[idx.val] = gt
      | .Err e => e = .UnknownGlobal ∧ env.global_types.val.length ≤ idx.val ⦄ := by
  unfold code.global_type
  step*

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

theorem code.take_global.spec (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
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

/-- Unsigned immediates consume their exact encoding and leave both stacks alone. -/
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

theorem code.require_memory.spec (env : module.Env) :
    code.require_memory env ⦃ r =>
      match r with
      | .Ok _ => 0 < env.mem_types.val.length
      | .Err e => e = .UnknownMemory ∧ env.mem_types.val = [] ⦄ := by
  unfold code.require_memory alloc.vec.Vec.is_empty
  step*
  all_goals simp_all
  exact List.length_pos_iff.mpr (by assumption)

theorem code.require_single_result.spec (ts : Slice types.ValueType) :
    code.require_single_result ts ⦃ r =>
      match r with
      | .Ok _ => ts.val.length ≤ 1
      | .Err e => e = .TooManyResults ∧ 1 < ts.val.length ⦄ := by
  unfold code.require_single_result
  simp only [limits.MAX_RESULTS]
  step*

/-- Both memory immediates are committed together; malformed offsets preserve
    the original state, even after a successfully decoded alignment. -/
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

theorem code.check_memory_and_alignment.spec (env : module.Env) (arg : code.MemArg)
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
