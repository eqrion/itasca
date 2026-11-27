import Itasca.Body.Scalar.Readers
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Body.Reader.StackValues

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Local.

This module collects LocalInstructions, LocalEffects.
Each section documents its contracts and consumers.
-/

/-! ## LocalInstructions -/

section

/-!
Reader context extension and local get/set/tee effects.

Main declarations: `Body.Pending.append_reader_context` and `reader_local_tee`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body Itasca.Visitor.Trace

theorem reader_local_get {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 32#u8)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_LOCAL_GET before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_local_get before out idx = .ok (.Ok (), after) ∧
      code.read_local_get st.core data ⟨locals, p.ft.results⟩ = .ok (.Ok idx, out) ∧
      Body.ReaderPost p out (.LOCAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_local_get] at accepted
  obtain ⟨idx, read, callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Body.Control.polymorphic, ctrls]
  have contextMatch : Translation.Environment.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have post := code.read_local_get.prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    capacity _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := Body.Pending.index_reader_post p C outer spine header base ctrls blocks
    32#u8 _ byte (fun idx => .instr_case_43 _ (Translation.Environment.index_wf idx))
    (fun idx _ encoded => .localGet idx encoded) out idx post
  exact ⟨idx, values, callback, read, source⟩

theorem reader_local_set {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 33#u8)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_LOCAL_SET before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_local_set before out idx = .ok (.Ok (), after) ∧
      code.read_local_set st.core data ⟨locals, p.ft.results⟩ = .ok (.Ok idx, out) ∧
      Body.ReaderPost p out (.LOCAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_local_set] at accepted
  obtain ⟨idx, read, callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Body.Control.polymorphic, ctrls]
  have contextMatch : Translation.Environment.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have post := code.read_local_set.prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Body.Control.base, ctrls] using base) _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := Body.Pending.index_reader_post p C outer spine header base ctrls blocks
    33#u8 _ byte (fun idx => .instr_case_44 _ (Translation.Environment.index_wf idx))
    (fun idx _ encoded => .localSet idx encoded) out idx post
  exact ⟨idx, values, callback, read, source⟩

theorem reader_local_tee {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.OpIterState)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 34#u8)
    (accepted : code.step visitor st.core data env ⟨locals, p.ft.results⟩ code.OP_LOCAL_TEE before =
      .ok (.Ok (), out, after)) :
    ∃ idx values, visitor.on_local_tee before out idx = .ok (.Ok (), after) ∧
      code.read_local_tee st.core data ⟨locals, p.ft.results⟩ = .ok (.Ok idx, out) ∧
      Body.ReaderPost p out (.LOCAL_TEE (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values := by
  rw [dispatch_local_tee] at accepted
  obtain ⟨idx, read, callback⟩ := Visitor.Core.run.accepted _ _ _ _ _ accepted
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have polymorphic : Body.Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by simp [Body.Control.polymorphic, ctrls]
  have contextMatch : Translation.Environment.Matches env ⟨locals, p.ft.results⟩ (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (Translation.Environment.Matches.root env ⟨locals, p.ft.results⟩)).enter _
  have post := code.read_local_tee.prefix st.core data env ⟨locals, p.ft.results⟩ outer p.current.vals vals
    (by simpa [Body.Control.base, ctrls] using base) capacity _ contextMatch p.current.ops (by simpa [polymorphic] using typed)
  rw [read, WP.spec_ok] at post
  obtain ⟨values, _, source⟩ := Body.Pending.index_reader_post p C outer spine header base ctrls blocks
    34#u8 _ byte (fun idx => .instr_case_45 _ (Translation.Environment.index_wf idx))
    (fun idx _ encoded => .localTee idx encoded) out idx post
  exact ⟨idx, values, callback, read, source⟩

end Itasca.Compiler

end

/-! ## LocalEffects -/

section

/-!
Successful local reads return the declared local type and append exactly that concrete operand to the physical validator stack.

Main declarations: `reader_local_get_effect` and `reader_local_tee_effect`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Successful local reads return the declared local type and append exactly
that concrete operand to the physical validator stack. -/
theorem reader_local_get_effect (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (capacity : st.vals.val.length < Usize.max)
    (accepted : code.read_local_get st data ctx = .ok (.Ok index, out)) :
    ∃ ty : wasm_types.ValueType, ctx.locals.val[index.val]? = some ty ∧
      out.vals.val = st.vals.val ++ [.Val ty] := by
  obtain ⟨⟨result, state⟩, read, values, controls, post⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at values controls post
  cases result with
  | Err error =>
    simp [code.read_local_get, read, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx, ty⟩ := pair
    obtain ⟨_, bound, lookup⟩ := post
    obtain ⟨next, pushed, nextValues, _, _⟩ := WP.spec_imp_exists
      (code.push_val.spec state (.Val ty) (by simpa [values] using capacity))
    simp [code.read_local_get, read, core.result.Result.Insts.CoreOpsTry.branch,
      pushed, bind_ok, Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact ⟨ty, by simpa [List.getElem?_eq_getElem bound] using congrArg some lookup,
      by simpa [values] using nextValues⟩

theorem typed_pop_exact {segment rest : List code.StackType} {ty value}
    (known : ConcreteStack segment)
    (effect : Body.Stack.Semantics.TypedPopResult false segment ty (.Ok value) rest) :
    segment = rest ++ [.Val ty] := by
  obtain ⟨popped, accepted⟩ := effect
  cases popped with
  | explicit =>
    cases value with
    | Bot => exact False.elim (known .Bot (by simp) rfl)
    | Val raw =>
      change Translation.valueType ty = Translation.valueType raw at accepted
      have equal : ty = raw := Translation.value_type_injective accepted
      simp [equal]

/-- A live, concrete local write consumes exactly the local's declared type. -/
theorem reader_local_set_effect (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Body.Control.base st).val = outer.length)
    (monomorphic : Body.Control.polymorphic st = false) (known : ConcreteStack segment)
    (accepted : code.read_local_set st data ctx = .ok (.Ok index, out)) :
    ∃ ty : wasm_types.ValueType, ctx.locals.val[index.val]? = some ty ∧
      st.vals.val = out.vals.val ++ [.Val ty] := by
  obtain ⟨⟨result, state⟩, read, stateValues, controls, post⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at stateValues controls post
  cases result with
  | Err error =>
    simp [code.read_local_set, read, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx, ty⟩ := pair
    obtain ⟨_, bound, lookup⟩ := post
    obtain ⟨⟨popResult, next⟩, popped, _, _, rest, nextValues, popEffect⟩ := WP.spec_imp_exists
      (code.pop_with_type.segment state outer segment ty (by simpa [stateValues] using values)
        (by simpa [Body.Control.base, controls] using base))
    dsimp only at nextValues popEffect
    cases popResult with
    | Err error =>
      simp [code.read_local_set, read, popped, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
    | Ok raw =>
      have poly : Body.Control.polymorphic state = false := by simpa [Body.Control.polymorphic, controls] using monomorphic
      rw [poly] at popEffect
      have segmentShape := typed_pop_exact known popEffect
      simp [code.read_local_set, read, popped, core.result.Result.Insts.CoreOpsTry.branch] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact ⟨ty, by simpa [List.getElem?_eq_getElem bound] using congrArg some lookup,
        by simp [values, nextValues, segmentShape, List.append_assoc]⟩

/-- A live, concrete local write consumes exactly the local's declared type. -/
theorem reader_local_tee_effect (st out : code.OpIterState) (data : Slice U8) (ctx : code.Context)
    (index : U32) (capacity : st.vals.val.length < Usize.max) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Body.Control.base st).val = outer.length)
    (monomorphic : Body.Control.polymorphic st = false) (known : ConcreteStack segment)
    (accepted : code.read_local_tee st data ctx = .ok (.Ok index, out)) :
    ∃ ty : wasm_types.ValueType, ctx.locals.val[index.val]? = some ty ∧
      ∃ rest, st.vals.val = rest ++ [.Val ty] ∧ out.vals.val = st.vals.val := by
  obtain ⟨⟨result, state⟩, read, stateValues, controls, post⟩ := WP.spec_imp_exists (code.take_local.spec st data ctx)
  dsimp only at stateValues controls post
  cases result with
  | Err error =>
    simp [code.read_local_tee, read, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | Ok pair =>
    obtain ⟨idx, ty⟩ := pair
    obtain ⟨_, bound, lookup⟩ := post
    obtain ⟨⟨popResult, next⟩, popped, _, _, rest, nextValues, popEffect⟩ := WP.spec_imp_exists
      (code.pop_with_type.segment state outer segment ty (by simpa [stateValues] using values)
        (by simpa [Body.Control.base, controls] using base))
    dsimp only at nextValues popEffect
    cases popResult with
    | Err error =>
      simp [code.read_local_tee, read, popped, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
    | Ok raw =>
      have poly : Body.Control.polymorphic state = false := by simpa [Body.Control.polymorphic, controls] using monomorphic
      rw [poly] at popEffect
      have segmentShape := typed_pop_exact known popEffect
      have nextCapacity : next.vals.val.length < Usize.max := by
        have shrink : next.vals.val.length ≤ st.vals.val.length := by
          simp only [nextValues, values, segmentShape, List.length_append, List.length_singleton]
          omega
        omega
      obtain ⟨finalState, pushed, finalValues, _, _⟩ := WP.spec_imp_exists
        (code.push_val.spec next (.Val ty) nextCapacity)
      simp [code.read_local_tee, read, popped, pushed, core.result.Result.Insts.CoreOpsTry.branch] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      refine ⟨ty, by simpa [List.getElem?_eq_getElem bound] using congrArg some lookup,
        outer ++ rest, ?_, ?_⟩
      · simp [values, segmentShape, List.append_assoc]
      · simp [finalValues, nextValues, values, segmentShape, List.append_assoc]

end Itasca.Compiler

end
