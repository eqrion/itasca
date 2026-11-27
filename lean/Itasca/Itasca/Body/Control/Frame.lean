import Itasca.Module.CodeMetadata
import Itasca.Body.EmptyVisitorLoop
import Itasca.Handler.StackEffects
import Itasca.Body.TableAdapters
import Itasca.Binary.Body.Syntax
import Itasca.Handler.Environment

open WebAssembly

/-!
Proofs for Body / Control.

This module collects Frame, Total.
Each section documents its contracts and consumers.
-/

/-! ## Frame -/

section

/-!
Proofs for Body / Control.

This module collects FuncType, Frame.
Each section documents its contracts and consumers.
-/

/-! ## FuncType -/

section

/-!
# Function type application

Specs of the extracted `code.apply_func_type`, which pops a function type's parameters and pushes
its results for calls. `code.apply_func_type.total` and `.realizes` give totality and the effect on
the backward stack interpretation, `.complete` gives acceptance from declarative operand
compatibility, and `code.check_func_type.complete` gives acceptance of limit-respecting types.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- Function types within the parameter and result limits pass `code.check_func_type`. -/
theorem code.check_func_type.complete (ft : wasm_types.FuncType)
    (hp : ft.params.val.length ≤ 1000) (hr : ft.results.val.length ≤ 1000) :
    code.check_func_type ft = .ok (.Ok ()) := by
  have hp' : ¬ alloc.vec.Vec.len ft.params > limits.MAX_MULTI_VALUE_PARAMS := by
    simp only [limits.MAX_MULTI_VALUE_PARAMS]; scalar_tac
  have hr' : ¬ alloc.vec.Vec.len ft.results > limits.MAX_MULTI_VALUE_RESULTS := by
    simp only [limits.MAX_MULTI_VALUE_RESULTS]; scalar_tac
  simp [code.check_func_type, hp', hr']

/-- Function type application is total on structurally bounded stacks. The explicit
capacity guard also covers arbitrary oversized caller-supplied environments. -/
@[step]
theorem code.apply_func_type.total (st : code.OpIterState) (ft : wasm_types.FuncType)
    (hshape : Body.Control.Shape st) :
    code.apply_func_type st ft ⦃ r =>
      Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
        r.2.vals.val.length ≤ st.vals.val.length + 1000 ⦄ := by
  obtain ⟨check, hcheck, hlimit⟩ := WP.spec_imp_exists (code.check_func_type.spec ft)
  unfold code.apply_func_type
  rw [hcheck]
  cases check with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hshape]
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨⟨res, s⟩, hpop, hs, hc, hp, hl, _⟩ := WP.spec_imp_exists
      (code.pop_types.total st (alloc.vec.Vec.deref ft.params) hshape)
    dsimp only at hs hc hp hl
    rw [hpop]
    cases res with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hs, hc, hp]
      omega
    | Ok u =>
      simp only [bind_ok]
      step
      split
      · simp [hs, hc, hp]
        omega
      · have hcap : s.vals.val.length + (alloc.vec.Vec.deref ft.results).val.length ≤ Usize.max := by
          simp [alloc.vec.Vec.deref]
          scalar_tac
        obtain ⟨s', hpush, hv', hc', hp'⟩ := WP.spec_imp_exists
          (code.push_types.spec s (alloc.vec.Vec.deref ft.results) hcap)
        rw [hpush]
        simp only [bind_ok, WP.spec_ok]
        refine ⟨hs.replace_operands hc' ?_, hc'.trans hc, hp'.trans hp, ?_⟩
        · have hbase := hs.base_le
          simp only [hv', List.length_append, List.length_map]
          omega
        · have hresults : ft.results.val.length ≤ 1000 := hlimit.2
          simp only [hv', List.length_append, List.length_map]
          simp only [alloc.vec.Vec.deref]
          simp
          omega

/-- An accepted call consumes its parameters in operand order and appends all
results. The semantic transfer is independent of the function's arity. -/
theorem code.apply_func_type.realizes (st : code.OpIterState) (ft : wasm_types.FuncType)
    (outer segment : List code.StackType)
    (hv : st.vals.val = outer ++ segment) (hb : (Body.Control.base st).val = outer.length) :
    code.apply_func_type st ft ⦃ r =>
      r.1 = .Ok () → r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ft.params.val.length ≤ 1000 ∧ ft.results.val.length ≤ 1000 ∧
      ∃ rest, r.2.vals.val = outer ++ (rest ++ ft.results.val.map code.StackType.Val) ∧
        rest.length ≤ segment.length ∧
        ∀ ts, Body.Stack.Realizes (Body.Control.polymorphic st) rest ts →
          Body.Stack.Realizes (Body.Control.polymorphic st) segment
            (ts ++ ft.params.val.map Translation.valueType) ⦄ := by
  obtain ⟨check, hcheck, hc⟩ := WP.spec_imp_exists (code.check_func_type.spec ft)
  unfold code.apply_func_type
  rw [hcheck]
  cases check with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨⟨res, s⟩, hr, hcs, hps, rest, hvs, hlen, ht⟩ := WP.spec_imp_exists
      (code.pop_types.realizes st outer segment (alloc.vec.Vec.deref ft.params) hv hb)
    rw [hr]
    cases res with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok u =>
      simp only [bind_ok]
      step
      split
      · simp
      · step with code.push_types.spec s (alloc.vec.Vec.deref ft.results) (by simp [alloc.vec.Vec.deref]; scalar_tac)
        simp_all [alloc.vec.Vec.deref, List.append_assoc]

/-- Declarative operand compatibility forces call acceptance within the
signature limits and available stack capacity. -/
theorem code.apply_func_type.complete (st : code.OpIterState) (ft : wasm_types.FuncType)
    (outer segment : List code.StackType) (before : List valtype)
    (hp : ft.params.val.length ≤ 1000) (hr : ft.results.val.length ≤ 1000)
    (hv : st.vals.val = outer ++ segment) (hb : (Body.Control.base st).val = outer.length)
    (hcap : st.vals.val.length + ft.results.val.length ≤ Usize.max)
    (ht : Body.Stack.Realizes (Body.Control.polymorphic st) segment
      (before ++ ft.params.val.map Translation.valueType)) :
    code.apply_func_type st ft ⦃ r =>
      r.1 = .Ok () ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧
        rest.length ≤ segment.length + ft.results.val.length ∧
        Body.Stack.Realizes (Body.Control.polymorphic st) rest
          (before ++ ft.results.val.map Translation.valueType) ⦄ := by
  obtain ⟨⟨_, s⟩, hpop, rfl, hc, hpos, rest, hvs, hlen, ht'⟩ := WP.spec_imp_exists
    (code.pop_types.complete st outer segment before (alloc.vec.Vec.deref ft.params)
      hv hb (by simpa [alloc.vec.Vec.deref] using ht))
  have hspace : s.vals.val.length + ft.results.val.length ≤ Usize.max := by
    simp only [hvs, hv, List.length_append] at *
    omega
  unfold code.apply_func_type
  rw [code.check_func_type.complete ft hp hr]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [hpop]
  simp only [bind_ok]
  step
  split
  · scalar_tac
  · step with code.push_types.spec s (alloc.vec.Vec.deref ft.results) (by simpa [alloc.vec.Vec.deref] using hspace)
    refine ⟨by simp_all, by simp_all,
      rest ++ ft.results.val.map code.StackType.Val, ?_, ?_, ?_⟩
    · simp_all [alloc.vec.Vec.deref, List.append_assoc]
    · simpa using Nat.add_le_add_right hlen ft.results.val.length
    · exact (Body.Stack.realizes_append_concrete _ rest ft.results.val _).mpr ⟨before, ht', rfl⟩

end Itasca

end

/-! ## Frame -/

section

/-!
# Control frames and labels

The structural invariant of the extracted control stack and its label lookup. `Body.Shape` says
that frame bases are ordered and within the operand stack and that the `blocks` vector is aligned
with the control vector. `code.push_frame.spec`, `code.label.spec` and
`code.read_multi_value_label.spec` describe frame creation and label decoding, with `Body.labelAt`
as the specification of a branch depth.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- Frame bases remain ordered and within the operand stack. The signature
projection has the same indexing as the runtime control vector. -/
structure Shape (st : code.BodyState) : Prop where
  core : Body.Control.Shape st.core
  aligned : st.blocks.val.length = st.core.ctrls.val.length

/-- The control entry that `code.push_frame` creates, with its base at the current stack height. -/
def frame (st : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType) : code.Ctrl :=
  ⟨kind, bt, alloc.vec.Vec.len st.vals, false⟩

/-- Pushing a frame at the current stack height preserves `Body.Control.Shape`. -/
theorem shape_push {st st' : code.OpIterState} (h : Body.Control.Shape st)
    (kind : code.LabelKind) (bt : signature.BlockType)
    (hctrls : st'.ctrls.val = st.ctrls.val ++ [frame st kind bt])
    (hvals : st'.vals = st.vals) : Body.Control.Shape st' := by
  constructor
  · rw [hctrls, List.pairwise_append]
    exact ⟨h.ordered, by simp, by simpa [frame] using h.bounded⟩
  · intro c hc
    rw [hctrls] at hc
    rcases List.mem_append.mp hc with hc | hc
    · simpa [hvals] using h.bounded c hc
    · have heq : c = frame st kind bt := by simpa using hc
      simp [heq, frame, hvals]

/-- The descriptor a branch to a frame carries: the parameters for `loop`, the results
otherwise. -/
def target (kind : code.LabelKind) (bt : signature.BlockType) : signature.ResultType :=
  match kind with
  | .Loop => inputs bt
  | _ => outputs bt

/-- The label descriptor at a branch depth, counted from the innermost frame. -/
def labelAt (st : code.BodyState) (depth : Nat) : Option signature.ResultType := do
  if depth < st.blocks.val.length then
    let i := st.blocks.val.length - 1 - depth
    let c ← st.core.ctrls.val[i]?
    let bt ← st.blocks.val[i]?
    some (target c.kind bt)
  else none

end Itasca.Body

namespace Itasca

@[step]
theorem code.push_frame.spec (st : code.BodyState)
    (kind : code.LabelKind) (bt : signature.BlockType)
    (hc : st.core.ctrls.val.length < Usize.max) :
    code.push_frame st kind bt ⦃ s =>
      s.core.ctrls.val = st.core.ctrls.val ++ [Body.frame st.core kind bt] ∧
      s.core.vals = st.core.vals ∧ s.core.pos = st.core.pos ∧
      s.blocks.val = st.blocks.val ++ [bt] ⦄ := by
  unfold code.push_frame
  step*
  simp_all [Body.frame]

/-- Label lookup uses loop inputs and all other frames' outputs, in reverse
nesting order. Out-of-range labels produce an ordinary validation error. -/
@[step]
theorem code.label.spec (st : code.BodyState) (depth : U32)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.label st depth ⦃ r =>
      match r with
      | .Ok view => Body.labelAt st depth.val = some view
      | .Err e => e = .UnknownLabel ∧ st.blocks.val.length ≤ depth.val ⦄ := by
  unfold code.label
  step
  split
  · simp only [WP.spec_ok]
    constructor
    · trivial
    · scalar_tac
  · step
    step
    step
    split <;> simp only [signature.BlockType.params.spec, signature.BlockType.results.spec, bind_ok, WP.spec_ok]
    all_goals simp_all [Body.labelAt, Body.target]
    all_goals have hi : depth.val < st.core.ctrls.val.length := by scalar_tac
    all_goals have hc : st.core.ctrls.val.length - 1 - depth.val < st.core.ctrls.val.length := by omega
    all_goals simp_all

theorem code.label.complete (st : code.BodyState) (depth : U32)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) (view : signature.ResultType)
    (hl : Body.labelAt st depth.val = some view) :
    code.label st depth = .ok (.Ok view) := by
  obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (code.label.spec st depth ha)
  cases r with
  | Err e =>
    have hd : st.core.ctrls.val.length ≤ depth.val := by simpa using hs.2
    simp [Body.labelAt, Nat.not_lt.mpr hd] at hl
  | Ok actual =>
    have he : actual = view := by simpa [hs] using hl
    simpa [he] using hr

/-- `code.read_label_info` decodes a LEB128 depth and resolves it with `Body.labelAt`, leaving
the stack and frames unchanged. -/
@[step]
theorem code.read_label_info.spec (st : code.BodyState) (data : Slice U8)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.read_label_info st data ⦃ r =>
      r.2.core.vals = st.core.vals ∧ r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
      st.core.pos.val ≤ r.2.core.pos.val ∧
      (∀ depth view, r.1 = .Ok (depth, view) →
        Binary.Leb128.Decoded data st.core.pos depth r.2.core.pos ∧
        Body.labelAt st depth.val = some view) ⦄ := by
  obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases r with
  | Err e => simp [code.read_label_info, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨depth, next⟩ := pair
    have hpnext : st.core.pos.val ≤ next.val := (Binary.Leb128.Decoded.span _ _ _ _ hs).1.le
    obtain ⟨r, hl, hp⟩ := WP.spec_imp_exists
      (code.label.spec { st with core := { st.core with pos := next } } depth ha)
    cases r with
    | Err e => simp [code.read_label_info, hr, hl, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hpnext]
    | Ok view =>
      simp [code.read_label_info, hr, hl, core.result.Result.Insts.CoreOpsTry.branch]
      exact ⟨hpnext, hs, hp⟩

/-- `code.read_multi_value_label` is `code.read_label_info` without the depth. -/
@[step]
theorem code.read_multi_value_label.spec (st : code.BodyState) (data : Slice U8)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.read_multi_value_label st data ⦃ r =>
      r.2.core.vals = st.core.vals ∧ r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
      st.core.pos.val ≤ r.2.core.pos.val ∧
      (∀ view, r.1 = .Ok view → ∃ depth,
        Binary.Leb128.Decoded data st.core.pos depth r.2.core.pos ∧
        Body.labelAt st depth.val = some view) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hb, hp, hl⟩ :=
    WP.spec_imp_exists (code.read_label_info.spec st data ha)
  dsimp only at hv hc hb hp hl
  cases r with
  | Err e =>
    simp [code.read_multi_value_label, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    simp_all
  | Ok pair =>
    obtain ⟨depth, view⟩ := pair
    simp [code.read_multi_value_label, hr, core.result.Result.Insts.CoreOpsTry.branch]
    simp_all
    exact ⟨depth, hl⟩

end Itasca

end

end

/-! ## Total -/

section

/-!
# Totality of the control handlers

Termination and structural-invariant preservation for the extracted control handlers
`code.push_frame`, `code.branch`, `code.enter`, `code.branch_table`, `code.call` and their
metadata-returning helpers, on arbitrary bytes and environments. Each result keeps
`Body.Control.Shape` and the alignment of the `blocks` vector with the control vector.
-/

open Aeneas Aeneas.Std

set_option maxHeartbeats 1000000

namespace Itasca

attribute [local step] code.pop_with_type.total code.check_suffix.spec

/-- Erasing the active operand segment preserves structural frame bounds,
including the empty-control-stack case. -/
@[step]
theorem code.mark_unreachable_total (st : code.OpIterState)
    (hs : Body.Control.Shape st) :
    code.mark_unreachable st ⦃ s =>
      Body.Control.Shape s ∧ s.ctrls.val.length = st.ctrls.val.length ∧ s.pos = st.pos ∧
      s.vals.val.length ≤ st.vals.val.length ∧
      s.ctrls.val.map code.Ctrl.signature = st.ctrls.val.map code.Ctrl.signature ⦄ := by
  rcases List.eq_nil_or_concat' st.ctrls.val with he | ⟨cs, c, he⟩
  · unfold code.mark_unreachable
    step with code.cur_base.spec st
    subst base
    step with code.mark_unreachable_loop.spec st (Body.Control.base st) hs.base_le
    step*
    simp_all
    all_goals simp_all [Body.Control.base]
    exact ⟨by simp [he], by simp [he]⟩
  · obtain ⟨s, hr, hv, hl, hc, hp⟩ := WP.spec_imp_exists
      (code.mark_unreachable.spec st cs c he (hs.bounded c (by simp [he])))
    rw [hr, WP.spec_ok]
    exact ⟨hs.unreachable cs c he hc hl, by simp [hc, he], hp,
      by simp [hv], by simp [hc, he]⟩

/-- `code.push_frame` is total and adds one aligned frame at the current stack height. -/
@[step]
theorem code.push_frame.total (st : code.BodyState)
    (kind : code.LabelKind) (bt : signature.BlockType)
    (hshape : Body.Control.Shape st.core)
    (halign : st.blocks.val.length = st.core.ctrls.val.length)
    (hcap : st.blocks.val.length < Usize.max) :
    code.push_frame st kind bt ⦃ s =>
      Body.Control.Shape s.core ∧ s.blocks.val.length = s.core.ctrls.val.length ∧
      s.core.pos = st.core.pos ∧ s.core.vals = st.core.vals ∧
      s.blocks.val.length = st.blocks.val.length + 1 ⦄ := by
  apply WP.spec_mono (code.push_frame.spec st kind bt (by omega))
  rintro s ⟨hc, hv, hp, hb⟩
  exact ⟨Body.shape_push hshape kind bt hc hv, by simp [hb, hc], hp, hv, by simp [hb]⟩

/-- Branches preserve frame alignment and bounds for arbitrary label bytes and
arbitrary environments. Conditional branches restore the entire signature. -/
theorem code.branch.total (st : code.BodyState) (data : Slice U8)
    (env : metadata.CodeMetadata) (conditional : Bool) (hs : Body.Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.branch st data env conditional ⦃ r =>
      Body.Control.Shape r.2.core ∧ r.2.blocks.val.length = r.2.core.ctrls.val.length ∧
      r.2.blocks = st.blocks ∧ st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  rw [code.branch.eq_core]
  unfold Body.branchCore
  step with code.read_multi_value_label.spec st data ha as ⟨r, st1, hv, hc, hblocks, hpos, hres⟩
  have hs' : Body.Control.Shape st1.core :=
    ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩
  have ha' : st1.blocks.val.length = st1.core.ctrls.val.length := by simp_all
  cases conditional <;> step* <;> simp_all

/-- Reading and entering a block is total on arbitrary bytes. Popping block
parameters before fixing the frame's base preserves nested frame bounds. -/
theorem code.enter_info.total (st : code.BodyState) (data : Slice U8)
    (env : metadata.CodeMetadata) (kind : code.LabelKind)
    (hs : Body.Control.Shape st.core) (hcap : st.blocks.val.length < Usize.max) :
    code.enter_info st data env kind ⦃ r =>
      Body.Control.Shape r.2.core ∧ r.2.blocks.val.length = r.2.core.ctrls.val.length ∧
      r.2.blocks.val.length ≤ st.blocks.val.length + 1 ∧
      st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  unfold code.enter_info
  obtain ⟨res, hr, hdecoded⟩ := WP.spec_imp_exists (signature.read_block_type.spec data st.core.pos)
  rw [hr]
  cases res with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hs]
  | Ok pair =>
    obtain ⟨bt, next⟩ := pair
    have hpnext := hdecoded.span.1.le
    simp only [bind_ok]
    have hbranch : core.result.Result.Insts.CoreOpsTry.branch
        (.Ok (bt, next) : core.result.Result (signature.BlockType × Usize) error.OpError) =
        .ok (.Continue (bt, next)) := rfl
    rw [hbranch]
    simp only [bind_ok]
    have hspos : Body.Control.Shape { st.core with pos := next } := ⟨hs.ordered, hs.bounded⟩
    simp only [signature.BlockType.params.spec]
    cases bt <;> cases kind <;> step* <;> simp_all

@[step]
theorem code.take_index.shape (st : code.OpIterState) (data : Slice U8)
    (hs : Body.Control.Shape st) :
    code.take_index st data ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  obtain ⟨⟨r, out⟩, hr, hv, hc, hd⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  dsimp only at hv hc hd
  rw [hr, WP.spec_ok]
  refine ⟨?_, hc, ?_⟩
  · exact ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩
  · cases r with
    | Err e => simpa only [hd.2] using Nat.le_refl st.pos.val
    | Ok index => exact (Binary.Leb128.Decoded.span _ _ _ _ hd).1.le

@[step]
theorem wasm_types.ElemType.value_type.total (ty : wasm_types.ElemType) :
    wasm_types.ElemType.value_type ty ⦃ _ => True ⦄ := by
  cases ty <;> simp [wasm_types.ElemType.value_type]

@[step]
theorem wasm_types.ValueType.ne.total (a b : wasm_types.ValueType) :
    core.cmp.PartialEq.ne.trait_default wasm_types.ValueType.Insts.CoreCmpPartialEqValueType a b
      ⦃ _ => True ⦄ := by
  cases a <;> cases b <;>
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

@[step]
theorem code.call_info.total (st : code.BodyState) (data : Slice U8)
    (env : metadata.CodeMetadata) (hs : Body.Control.Shape st.core) :
    code.call_info st data env ⦃ r =>
      Body.Control.Shape r.2.core ∧ r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
        st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  unfold code.call_info
  step* <;> try simp_all
  rw [← o_post]
  cases o <;> simp only [core.option.Option.ok_or, bind_ok]
  all_goals step* <;> simp_all

@[step]
theorem code.call_indirect_info.total (st : code.BodyState) (data : Slice U8)
    (env : metadata.CodeMetadata) (hs : Body.Control.Shape st.core) :
    code.call_indirect_info st data env ⦃ r =>
      Body.Control.Shape r.2.core ∧ r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
        st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  unfold code.call_indirect_info
  step* <;> simp_all <;> omega

end Itasca

end
