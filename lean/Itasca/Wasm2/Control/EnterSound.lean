import Itasca.Wasm2.Control.EndSound

/-!
# Soundness of block entry

Soundness of the extracted `code.enter`, which opens `block`, `loop` and `if` frames.
`enterParams`, `enterArgs` and `checkBlock` factor out the pieces shared by its branches, and
`enter_eq` unfolds `code.enter` into them. `EnterEffect` is the exact semantic effect of opening a
frame, and `code.enter.sound` shows that a successful entry has that effect on a decoded block
type. Completeness is in `Wasm2/Control/EnterComplete`.
-/

open Aeneas Aeneas.Std Result

namespace Itasca.Wasm2

/-- Common parameter pop and frame setup in all extracted entry branches. -/
def enterParams (st : code.BodyState) (env : module.Env)
    (kind : code.LabelKind) (bt : signature.BlockType) :
    Result (core.result.Result Unit error.OpError × code.BodyState) := do
  let rt ← signature.BlockType.params bt
  let (r, s) ← code.pop_results st.core env rt
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue _ =>
    let st1 ← code.push_frame { st with core := s } kind bt
    let (r, s1) ← code.push_results st1.core env rt
    .ok (r, { st1 with core := s1 })
  | .Break residual =>
    let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      Unit (core.convert.FromSame error.OpError) residual
    .ok (r, { st with core := s })

/-- Entry for all forms: `if` first pops its `i32` condition, then every form runs
`enterParams`. -/
def enterArgs (st : code.BodyState) (env : module.Env)
    (kind : code.LabelKind) (bt : signature.BlockType) :
    Result (core.result.Result Unit error.OpError × code.BodyState) := do
  match kind with
  | .Then =>
    let (r, s) ← code.pop_with_type st.core .I32
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | .Continue _ => enterParams { st with core := s } env kind bt
    | .Break residual =>
      let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame error.OpError) residual
      .ok (r, { st with core := s })
  | _ => enterParams st env kind bt

/-- The validity check of an indexed block type: the index is in range and the function type is
within the limits. -/
def checkIndex (env : module.Env) (bt : signature.BlockType) :
    Result (core.result.Result Unit error.OpError) := do
  match bt with
  | .TypeIndex index =>
    let i ← lift (UScalar.cast .Usize index)
    if i >= alloc.vec.Vec.len env.types then .ok (.Err .UnknownType)
    else
      let ft ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice types.FuncType) env.types i
      code.check_func_type ft
  | _ => .ok (.Ok ())

/-- The block type checks of `code.enter`: the profile filter, then `checkIndex`. -/
def checkBlock (env : module.Env) (profile : ValidationProfile) (bt : signature.BlockType) :
    Result (core.result.Result Unit error.OpError) := do
  let r ← code.check_block_type profile bt
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue _ => checkIndex env bt
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      Unit (core.convert.FromSame error.OpError) residual

/-- `code.enter` unfolds to the block type read, `checkBlock` and `enterArgs`. -/
theorem enter_eq (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (profile : ValidationProfile) (kind : code.LabelKind) :
    code.enter st data env profile kind = (do
      let r ← signature.read_block_type data st.core.pos
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | .Continue (bt, next) =>
        let r ← checkBlock env profile bt
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | .Continue _ => enterArgs { st with core := { st.core with pos := next } } env kind bt
        | .Break residual =>
          let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.OpError) residual
          .ok (r, { st with core := { st.core with pos := next } })
      | .Break residual =>
        let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.OpError) residual
        .ok (r, st)) := by
  simp only [code.enter, code.enter_info, Std.bind_assoc]
  congr 1
  funext r
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨bt, next⟩ := pair
    cases bt <;> cases kind
    all_goals
      simp only [checkBlock, checkIndex, enterArgs, enterParams,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        signature.BlockType.params, Std.uncurry, Std.bind_assoc, bind_ok]
      try dsimp only
      try simp only [Std.bind_assoc, bind_ok]
      repeat' first
        | rfl
        | simp only [Std.uncurry, Std.bind_assoc, bind_ok, core.convert.FromSame.from]
        | (congr 1; funext x; try dsimp only)
        | (split <;> try dsimp only)

    all_goals first | contradiction | simp_all [bind_ok]

@[step]
theorem checkIndex.spec (env : module.Env) (bt : signature.BlockType) :
    checkIndex env bt ⦃ r => r = .Ok () → ∃ ins outs,
      resolve env (inputs bt) = some ins ∧ resolve env (outputs bt) = some outs ∧
      ins.length ≤ 1000 ∧ outs.length ≤ 1000 ⦄ := by
  cases bt with
  | Empty => simp [checkIndex, resolve, inputs, outputs]
  | Value t => simp [checkIndex, resolve, inputs, outputs]
  | TypeIndex index =>
    unfold checkIndex
    step
    split
    · simp
    · step as ⟨ft, hft⟩
      step with code.check_func_type.spec ft as ⟨r, hr⟩
      have hok : r = .Ok () := by assumption
      subst r
      have hi : index.val < env.types.val.length := by scalar_tac
      exact ⟨ft.params.val, ft.results.val, by simp [resolve, inputs, hi, hft, r_post],
        by simp [resolve, outputs, hi, hft, r_post], hr⟩

@[step]
theorem checkBlock.spec (env : module.Env) (profile : ValidationProfile) (bt : signature.BlockType) :
    checkBlock env profile bt ⦃ r => r = .Ok () → (profile = .Wasm1 → ∃ b, Wasm1.ScalarBlockByte bt b) ∧
      ∃ ins outs, resolve env (inputs bt) = some ins ∧ resolve env (outputs bt) = some outs ∧
      ins.length ≤ 1000 ∧ outs.length ≤ 1000 ⦄ := by
  unfold checkBlock
  obtain ⟨r, hr, hscalar⟩ := WP.spec_imp_exists (code.check_block_type.spec profile bt)
  rw [hr]
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    exact WP.spec_mono (checkIndex.spec env bt) fun r h hok => ⟨hscalar (by cases u; rfl), h hok⟩

/-- Exact semantic effect of opening a structured frame. -/
def EnterEffect (st s : code.BodyState) (form : Frames.Form) (bt : signature.BlockType)
    (ins outs : List types.ValueType) (outer segment : List code.StackType) : Prop :=
  ∃ remaining base,
    remaining.length ≤ segment.length ∧ base.val = outer.length + remaining.length ∧
    (∀ ts, Sequence.Realizes (Control.polymorphic st.core) remaining ts →
      Sequence.Realizes (Control.polymorphic st.core) segment (ts ++ form.args ins)) ∧
    s.core.ctrls.val = st.core.ctrls.val ++ [(Frames.Saved.fresh base form bt ins outs).ctrl] ∧
    s.blocks.val = st.blocks.val ++ [bt] ∧
    s.core.vals.val = outer ++ remaining ++ ins.map code.StackType.Val

/-- Parameter popping preserves the suspended parent's input signature. -/
theorem enterParams.sound (st : code.BodyState) (env : module.Env)
    (form : Frames.Form) (bt : signature.BlockType) (ins outs : List types.ValueType)
    (outer segment : List code.StackType)
    (hin : resolve env (inputs bt) = some ins)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Control.base st.core).val = outer.length)
    (hs : Control.Shape st.core) (hcap : st.blocks.val.length < Usize.max) :
    enterParams st env form.kind bt ⦃ r => r.1 = .Ok () →
      r.2.core.pos = st.core.pos ∧ ∃ remaining base,
      remaining.length ≤ segment.length ∧ base.val = outer.length + remaining.length ∧
      (∀ ts, Sequence.Realizes (Control.polymorphic st.core) remaining ts →
        Sequence.Realizes (Control.polymorphic st.core) segment (ts ++ ins.map Translate.valueType)) ∧
      r.2.core.ctrls.val = st.core.ctrls.val ++ [(Frames.Saved.fresh base form bt ins outs).ctrl] ∧
      r.2.blocks.val = st.blocks.val ++ [bt] ∧
      r.2.core.vals.val = outer ++ remaining ++ ins.map code.StackType.Val ⦄ := by
  unfold enterParams
  simp only [signature.BlockType.params.spec, bind_ok]
  step with code.pop_results.realizes st.core env (inputs bt) ins outer segment hin hv hb
    as ⟨r, s, hc, hp, remaining, hv', hl, ht⟩
  have hs' : Control.Shape s := hs.replace_operands hc (by simp [hb, hv'])
  step
  split
  · have hok : r = .Ok () := by cases r <;> simp_all
    step with code.push_frame.spec { st with core := s } form.kind bt (by simpa [hc] using hcap)
      as ⟨s1, hc1, hv1, hp1, hb1⟩
    have hs1 : Control.Shape s1.core := shape_push hs' form.kind bt hc1 hv1
    step with code.push_results.total s1.core env (inputs bt) hs1
      as ⟨r1, s2, hs2, hc2, hp2, hpush⟩
    intro hok1
    obtain ⟨ts, hts, hvs⟩ := hpush hok1
    have he : ts = ins := by simpa [hin] using hts.symm
    refine ⟨hp2.trans (hp1.trans hp), remaining, alloc.vec.Vec.len s.vals, hl,
      by simp [hv'], ht hok, ?_, by simpa [hc2, hc] using hb1, ?_⟩
    · simp [hc2, hc1, hc, Frames.Saved.fresh, Wasm2.frame]
    · simpa [he, hv1, hv'] using hvs
  · step*

theorem enterArgs.sound (st : code.BodyState) (env : module.Env)
    (form : Frames.Form) (bt : signature.BlockType) (ins outs : List types.ValueType)
    (outer segment : List code.StackType) (initial : form.Initial)
    (hin : resolve env (inputs bt) = some ins)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Control.base st.core).val = outer.length)
    (hs : Control.Shape st.core) (hcap : st.blocks.val.length < Usize.max) :
    enterArgs st env form.kind bt ⦃ r => r.1 = .Ok () →
      r.2.core.pos = st.core.pos ∧ EnterEffect st r.2 form bt ins outs outer segment ⦄ := by
  rcases initial with rfl | rfl | rfl
  · simpa [enterArgs, Frames.Form.kind, EnterEffect, Frames.Form.args] using
      enterParams.sound st env .block bt ins outs outer segment hin hv hb hs hcap
  · simpa [enterArgs, Frames.Form.kind, EnterEffect, Frames.Form.args] using
      enterParams.sound st env .loop bt ins outs outer segment hin hv hb hs hcap
  · simp only [enterArgs, Frames.Form.kind]
    step with code.pop_with_type.realizes st.core outer segment .I32 hv hb
      as ⟨r, s, hc, hp, rest, hv', hl, ht⟩
    step
    split
    · have hs' : Control.Shape s := hs.replace_operands hc (by simp [hb, hv'])
      have hbs : (Control.base s).val = outer.length := by simpa [Control.base, hc] using hb
      apply WP.spec_mono (enterParams.sound { st with core := s } env .then_ bt ins outs outer rest
        hin hv' hbs hs' (by simpa [hc] using hcap))
      intro result hresult hok
      obtain ⟨hpos, remaining, base, hlen, hbase, hback, hctrl, hblocks, hvals⟩ := hresult hok
      refine ⟨hpos.trans hp, remaining, base, hlen.trans hl, hbase, ?_, ?_, by simpa [hc] using hblocks, hvals⟩
      · intro ts hts
        have hr : ∃ t, r = .Ok t := by cases r <;> simp_all
        obtain ⟨t, hr⟩ := hr
        have hremaining : Sequence.Realizes (Control.polymorphic s) remaining ts := by
          simpa [Control.polymorphic, hc] using hts
        rw [hr] at ht
        have hpop := ht.2 (ts ++ ins.map Translate.valueType) (by
          simpa [Control.polymorphic, hc] using hback ts hremaining)
        simpa [Frames.Form.args, List.append_assoc, Translate.valueType] using hpop
      · simpa [hc] using hctrl
    · step*

end Itasca.Wasm2

namespace Itasca

/-- A successful `code.enter` decodes a block type whose signature resolves within the limits and
opens the frame with effect `EnterEffect`. -/
theorem code.enter.sound (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (profile : ValidationProfile) (form : Wasm2.Frames.Form) (initial : form.Initial)
    (outer segment : List code.StackType)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Control.base st.core).val = outer.length)
    (hs : Control.Shape st.core) (hcap : st.blocks.val.length < Usize.max) :
    code.enter st data env profile form.kind ⦃ r => r.1 = .Ok () → ∃ bt ins outs,
      Wasm2.BlockDecoded data st.core.pos bt r.2.core.pos ∧
      (profile = .Wasm1 → ∃ b, Wasm1.ScalarBlockByte bt b) ∧
      Wasm2.resolve env (Wasm2.inputs bt) = some ins ∧
      Wasm2.resolve env (Wasm2.outputs bt) = some outs ∧
      ins.length ≤ 1000 ∧ outs.length ≤ 1000 ∧
      Wasm2.EnterEffect st r.2 form bt ins outs outer segment ⦄ := by
  rw [Wasm2.enter_eq]
  step with signature.read_block_type.spec data st.core.pos as ⟨r, hdecoded⟩
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨bt, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with Wasm2.checkBlock.spec env profile bt as ⟨r, hcheck⟩
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok u =>
      obtain ⟨hscalar, ins, outs, hin, hout, hip, hop⟩ := hcheck (by cases u; rfl)
      simp only [bind_ok]
      apply WP.spec_mono (Wasm2.enterArgs.sound { st with core := { st.core with pos := next } }
        env form bt ins outs outer segment initial hin hv hb ⟨hs.ordered, hs.bounded⟩ hcap)
      intro result hresult hok
      obtain ⟨hpos, heffect⟩ := hresult hok
      exact ⟨bt, ins, outs, hpos ▸ hdecoded, hscalar, hin, hout, hip, hop, heffect⟩

end Itasca
