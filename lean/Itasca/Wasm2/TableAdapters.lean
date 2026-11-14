import Itasca.Support.Result
import Itasca.Support.LiteralDispatch

/-!
Sections, each formerly its own module: HandlerAdapters, Signature, Typing, SignatureEquality, TableAdapters.
-/

/-! ## HandlerAdapters -/

section

/-!
# Branch and call handler adapters

State-only presentations of `code.branch` and `code.call`, which the extracted code builds from the
metadata-returning `code.branch_info`, `code.call_info` and `code.call_indirect_info`.
`Wasm2.branchCore` and `Wasm2.callCore` unfold those helpers, and `code.branch.eq_core` and
`code.call.eq_core` show that the extracted handlers equal them.
-/

open Aeneas Aeneas.Std Result

namespace Itasca

/-- `code.branch` with `code.branch_info` unfolded, so it returns only the result and state. -/
def Wasm2.branchCore
  (st : _root_.Itasca.code.BodyState) (data : Slice Std.U8)
  (env : _root_.Itasca.metadata.Env) (conditional : Bool) :
  Result ((core.result.Result Unit _root_.Itasca.error.OpError) ×
    _root_.Itasca.code.BodyState)
  := do
  let (r, st1) ← code.read_multi_value_label st data
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    if conditional
    then
      let (r1, ois) ← code.pop_with_type st1.core wasm_types.ValueType.I32
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let (r2, ois1) ← code.pop_results ois env val
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          if conditional
          then
            let (r3, ois2) ← code.push_results ois1 env val
            ok (r3, { st1 with core := ois2 })
          else
            let ois2 ← code.mark_unreachable ois1
            ok (core.result.Result.Ok (), { st1 with core := ois2 })
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
          ok (r3, { st1 with core := ois1 })
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
        ok (r2, { st1 with core := ois })
    else
      let (r1, ois) ← code.pop_results st1.core env val
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        if conditional
        then
          let (r2, ois1) ← code.push_results ois env val
          ok (r2, { st1 with core := ois1 })
        else
          let ois1 ← code.mark_unreachable ois
          ok (core.result.Result.Ok (), { st1 with core := ois1 })
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
        ok (r2, { st1 with core := ois })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
    ok (r1, st1)

/-- `code.call` with `code.call_info` and `code.call_indirect_info` unfolded, so it returns only
the result and state. -/
def Wasm2.callCore (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (indirect : Bool) :
    Result (core.result.Result Unit error.OpError × code.BodyState) := do
  if indirect then
    let (r, out) ← code.call_indirect_info st data env
    match r with
    | .Err e => .ok (.Err e, out)
    | .Ok _ => .ok (.Ok (), out)
  else
    let r ← reader.read_u32_leb data st.core.pos
    match r with
    | .Err e => .ok (.Err e, st)
    | .Ok (index, next) =>
      let i ← lift (UScalar.cast .Usize index)
      if i ≥ alloc.vec.Vec.len env.func_types then
        .ok (.Err .UnknownFunc, { st with core := { st.core with pos := next } })
      else
        let ft ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice wasm_types.FuncType)
          env.func_types i
        let (r, out) ← code.apply_func_type { st.core with pos := next } ft
        .ok (r, { st with core := out })


/-- The extracted `code.branch` equals `Wasm2.branchCore`. -/
theorem code.branch.eq_core (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (conditional : Bool) :
    code.branch st data env conditional = Wasm2.branchCore st data env conditional := by
  simp only [code.branch, code.branch_info, Wasm2.branchCore,
    code.read_multi_value_label, Std.bind_assoc]
  congr 1
  funext x
  obtain ⟨r, s⟩ := x
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨depth, ts⟩ := pair
    cases conditional <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Std.bind_assoc]
    all_goals
      congr 1
      funext x
      obtain ⟨r, ois⟩ := x
      cases r <;> simp [Std.bind_assoc]
    all_goals
      congr 1
      funext x
      obtain ⟨r, ois⟩ := x
      cases r <;> simp [Std.bind_assoc]
    all_goals
      congr 1
      funext x
      obtain ⟨r, ois⟩ := x
      cases r <;> simp

/-- The extracted `code.call` equals `Wasm2.callCore`. -/
theorem code.call.eq_core (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (indirect : Bool) :
    code.call st data env indirect = Wasm2.callCore st data env indirect := by
  cases indirect with
  | true =>
    simp only [code.call, Wasm2.callCore, ↓reduceIte]
    congr 1
    funext pair
    obtain ⟨r, out⟩ := pair
    cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | false =>
    simp only [code.call, code.call_info, code.take_index, Wasm2.callCore,
      Bool.false_eq_true, ↓reduceIte, Std.bind_assoc]
    congr 1
    funext r
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨index, next⟩ := pair
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry, Std.bind_assoc]
      congr 1
      funext i
      split
      · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp only [Std.bind_assoc]
        congr 1
        funext ft
        congr 1
        funext pair
        obtain ⟨r, out⟩ := pair
        cases r <;> simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca

end

/-! ## Signature -/

section

/-!
# Signature descriptors

`Wasm2.resolve` gives the list of value types denoted by a `signature.ResultType` descriptor in a
module environment. Specs of the extracted `signature.ResultType.len` and
`signature.ResultType.get` relate them to `resolve`, and the `complete` versions give acceptance
from independent premises.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Logical list denoted by a descriptor; no such list is allocated by Rust. -/
def resolve (env : metadata.Env) : signature.ResultType → Option (List wasm_types.ValueType)
  | .Empty => some []
  | .One t => some [t]
  | .Type index part => (env.types.val[index.val]?).map fun ft =>
      match part with
      | .Params => ft.params.val
      | .Results => ft.results.val

end Itasca.Wasm2

namespace Itasca

@[step]
theorem wasm_types.ValueType.eq_spec (a b : wasm_types.ValueType) :
    wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq a b ⦃ equal =>
      equal = true ↔ a = b ⦄ := by
  cases a <;> cases b <;> simp [wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

@[step]
theorem signature.ResultType.len.spec (view : signature.ResultType) (env : metadata.Env) :
    signature.ResultType.len view env ⦃ r =>
      match r with
      | .Ok n => ∃ ts, Wasm2.resolve env view = some ts ∧ n.val = ts.length
      | .Err e => e = .UnknownType ∧ Wasm2.resolve env view = none ⦄ := by
  cases view with
  | Empty => simp [signature.ResultType.len, Wasm2.resolve]
  | One t => simp [signature.ResultType.len, Wasm2.resolve]
  | «Type» index part =>
    unfold signature.ResultType.len
    step*
    all_goals cases part <;> simp_all [Wasm2.resolve]
    all_goals have hi : index.val < env.types.val.length := by scalar_tac
    all_goals simp_all

@[step]
theorem signature.ResultType.get.spec (view : signature.ResultType) (env : metadata.Env) (i : Usize) :
    signature.ResultType.get view env i ⦃ r =>
      match r with
      | .Ok v => ∃ ts, Wasm2.resolve env view = some ts ∧ v = ts[i.val]?
      | .Err e => e = .UnknownType ∧ Wasm2.resolve env view = none ⦄ := by
  cases view with
  | Empty => simp [signature.ResultType.get, Wasm2.resolve]
  | One t =>
    unfold signature.ResultType.get
    step*
    all_goals simp_all [Wasm2.resolve] <;> omega
  | «Type» index part =>
    unfold signature.ResultType.get
    step*
    all_goals cases part <;> simp_all [Wasm2.resolve]
    all_goals have hi : index.val < env.types.val.length := by scalar_tac
    all_goals simp_all

theorem signature.ResultType.len.complete (view : signature.ResultType) (env : metadata.Env)
    (ts : List wasm_types.ValueType) (hts : Wasm2.resolve env view = some ts) :
    ∃ n, signature.ResultType.len view env = .ok (.Ok n) ∧ n.val = ts.length := by
  obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (signature.ResultType.len.spec view env)
  cases r with
  | Err e => simp [hts] at hs
  | Ok n =>
    obtain ⟨us, hu, hn⟩ := hs
    have he : us = ts := by simpa [hts] using hu.symm
    exact ⟨n, hr, he ▸ hn⟩

theorem signature.ResultType.get.complete (view : signature.ResultType) (env : metadata.Env)
    (ts : List wasm_types.ValueType) (hts : Wasm2.resolve env view = some ts) (i : Usize) :
    signature.ResultType.get view env i = .ok (.Ok ts[i.val]?) := by
  obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (signature.ResultType.get.spec view env i)
  cases r with
  | Err e => simp [hts] at hs
  | Ok v =>
    obtain ⟨us, hu, hv⟩ := hs
    have he : us = ts := by simpa [hts] using hu.symm
    simpa [he, hv] using hr

end Itasca

end

/-! ## Typing -/

section

/-!
# Block type signatures

`Wasm2.inputs` and `Wasm2.outputs` give the parameter and result descriptors of a block type, as
read by the extracted `signature.BlockType.params` and `signature.BlockType.results`.
`Wasm2.blockType_ok` relates their resolved types to the generated `Blocktype_ok` rule.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- The parameter descriptor of a block type. Only an indexed block type has parameters. -/
def inputs : signature.BlockType → signature.ResultType
  | .TypeIndex i => .Type i .Params
  | _ => .Empty

/-- The result descriptor of a block type. -/
def outputs : signature.BlockType → signature.ResultType
  | .Empty => .Empty
  | .Value t => .One t
  | .TypeIndex i => .Type i .Results

/-- Resolving both views of an indexed block selects the same function type
    used by the generated Wasm 2.0 block typing rule. -/
theorem blockType_ok (env : metadata.Env) (C : context) (hC : wf_context C)
    (htypes : C.TYPES = env.types.val.map EnvTranslation.funcType)
    (bt : signature.BlockType) (ins outs : List wasm_types.ValueType)
    (hi : resolve env (inputs bt) = some ins)
    (ho : resolve env (outputs bt) = some outs) :
    Blocktype_ok C (blockType bt)
      (.mk_functype (.mk_list (ins.map Translate.valueType))
        (.mk_list (outs.map Translate.valueType))) := by
  cases bt with
  | Empty =>
    simp [inputs, outputs, resolve] at hi ho
    subst ins; subst outs
    exact .valtype C none hC (.blocktype_case_0 _)
  | Value t =>
    simp [inputs, outputs, resolve] at hi ho
    subst ins; subst outs
    exact .valtype C (some (Translate.valueType t)) hC (.blocktype_case_0 _)
  | TypeIndex i =>
    by_cases hb : i.val < env.types.val.length
    · simp [inputs, outputs, resolve, List.getElem?_eq_getElem hb] at hi ho
      subst ins; subst outs
      apply Blocktype_ok.typeidx C (.mk_uN i.val) _ _
      · simpa [htypes, proj_uN_0] using hb
      · rw [htypes, getElem!_pos _ _ (by simpa [proj_uN_0] using hb), List.getElem_map]
        rfl
      · exact hC
      · exact blockType_wf (.TypeIndex i)
    · simp [inputs, resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ i.val)] at hi

end Itasca.Wasm2

namespace Itasca

@[simp]
theorem signature.BlockType.params.spec (bt : signature.BlockType) :
    signature.BlockType.params bt = .ok (Wasm2.inputs bt) := by cases bt <;> rfl

@[simp]
theorem signature.BlockType.results.spec (bt : signature.BlockType) :
    signature.BlockType.results bt = .ok (Wasm2.outputs bt) := by cases bt <;> rfl

end Itasca

end

/-! ## SignatureEquality -/

section

/-!
# Signature descriptor equality

Specs of the extracted `code.same_types` and its loop `code.same_types_loop`, which compare the
resolved type lists of two `signature.ResultType` descriptors. `code.same_types.spec` gives
totality and exact equality, and `code.same_types.complete` gives acceptance from equal lists.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- The comparison loop decides equality of the resolved lists, without
assuming descriptor identity (distinct type indices may have equal types). -/
theorem code.same_types_loop.spec (env : metadata.Env)
    (a b : signature.ResultType) (ts us : List wasm_types.ValueType)
    (ha : Wasm2.resolve env a = some ts)
    (hb : Wasm2.resolve env b = some us)
    (n i : Usize) (hn : n.val = ts.length) (hu : us.length = ts.length)
    (hi : i.val ≤ n.val) (hpre : ∀ j < i.val, ts[j]? = us[j]?) :
    code.same_types_loop env a b n i ⦃ r =>
      ∃ equal, r = .Ok equal ∧ (equal = true ↔ ts = us) ⦄ := by
  unfold code.same_types_loop
  apply loop.spec_decr_nat (fun j => n.val - j.val)
    (fun j => j.val ≤ n.val ∧ ∀ k < j.val, ts[k]? = us[k]?)
  · intro j ⟨hj, hp⟩
    unfold code.same_types_loop.body
    split
    · rename_i hend
      simp only [WP.spec_ok]
      refine ⟨true, rfl, ?_⟩
      simp only [true_iff]
      apply List.ext_getElem?
      intro k
      by_cases hk : k < j.val
      · exact hp k hk
      · rw [List.getElem?_eq_none (by scalar_tac), List.getElem?_eq_none (by scalar_tac)]
    · rename_i hlt
      have ht : j.val < ts.length := by scalar_tac
      have hus : j.val < us.length := by omega
      rw [signature.ResultType.get.complete a env ts ha j]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      rw [signature.ResultType.get.complete b env us hb j]
      simp only [bind_ok,
        List.getElem?_eq_getElem ht, List.getElem?_eq_getElem hus]
      step with core.cmp.PartialEq.ne.trait_default.spec
        wasm_types.ValueType.Insts.CoreCmpPartialEqValueType _ _ (wasm_types.ValueType.eq_spec _ _)
        as ⟨different, hdifferent⟩
      split
      · rename_i hne
        simp only [WP.spec_ok]
        refine ⟨false, rfl, ?_⟩
        simp only [Bool.false_eq_true, false_iff]
        intro he
        subst us
        simp_all
      · rename_i heq
        step
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro k hk
        by_cases hk' : k < j.val
        · exact hp k hk'
        · have hk' : k = j.val := by scalar_tac
          subst k
          simp_all
  · exact ⟨hi, hpre⟩

/-- Totality and exact equality for arbitrary descriptor pairs. -/
@[step]
theorem code.same_types.spec (env : metadata.Env) (a b : signature.ResultType) :
    code.same_types env a b ⦃ r =>
      match r with
      | .Ok equal => ∃ ts us, Wasm2.resolve env a = some ts ∧
          Wasm2.resolve env b = some us ∧ (equal = true ↔ ts = us)
      | .Err e => e = .UnknownType ∧
          (Wasm2.resolve env a = none ∨ Wasm2.resolve env b = none) ⦄ := by
  obtain ⟨ra, hra, hsa⟩ := WP.spec_imp_exists (signature.ResultType.len.spec a env)
  unfold code.same_types
  rw [hra]
  cases ra with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hsa.1, hsa.2]
  | Ok n =>
    obtain ⟨ts, ha, hn⟩ := hsa
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨rb, hrb, hsb⟩ := WP.spec_imp_exists (signature.ResultType.len.spec b env)
    rw [hrb]
    cases rb with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hsb.1, hsb.2]
    | Ok m =>
      obtain ⟨us, hb, hm⟩ := hsb
      simp only [bind_ok]
      split
      · rename_i hne
        simp only [WP.spec_ok]
        refine ⟨ts, us, ha, hb, ?_⟩
        simp only [Bool.false_eq_true, false_iff]
        intro he
        have : n = m := by scalar_tac
        simp_all
      · rename_i he
        apply WP.spec_mono (code.same_types_loop.spec env a b ts us ha hb
          n 0#usize hn (by scalar_tac) (by scalar_tac) (by simp))
        rintro r ⟨equal, rfl, hs⟩
        exact ⟨ts, us, ha, hb, hs⟩

/-- Descriptors that resolve to the same list are accepted as equal. -/
theorem code.same_types.complete (env : metadata.Env) (a b : signature.ResultType)
    (ts : List wasm_types.ValueType) (ha : Wasm2.resolve env a = some ts)
    (hb : Wasm2.resolve env b = some ts) :
    code.same_types env a b = .ok (.Ok true) := by
  obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (code.same_types.spec env a b)
  cases r with
  | Err e => simp [ha, hb] at hs
  | Ok equal =>
    obtain ⟨ts', us', ha', hb', he⟩ := hs
    have ht : ts' = ts := by simpa [ha] using ha'.symm
    have hu : us' = ts := by simpa [hb] using hb'.symm
    have heq : equal = true := he.mpr (ht.trans hu.symm)
    simpa [heq] using hr

end Itasca

end

/-! ## TableAdapters -/

section

/-!
# `br_table` handler adapters

State-only presentations of the `br_table` handler `code.branch_table` and its worker loop
`code.branch_table_with_loop` with the empty visitor. `Wasm2.branchTableLoop` and
`Wasm2.tableCore` project away the visitor, `Wasm2.tableBody_eq` relates the loop bodies, and
`code.branch_table.eq_core` shows that the extracted `code.branch_table` equals `Wasm2.tableCore`.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca

/-- A pure result projection preserves the producer's postcondition. -/
theorem ResultFacts.map_spec {A B : Type} (m : Result A) (f : A → B) (P : B → Prop)
    (h : m ⦃ x => P (f x) ⦄) :
    (do let x ← m; .ok (f x)) ⦃ P ⦄ :=
  WP.spec_bind h (fun _ hx => by simpa only [WP.spec_ok] using hx)

/-- One iteration of `code.branch_table_with_loop` with the empty visitor removed. -/
def Wasm2.branchTableLoop.body
  (data : Slice Std.U8) (env : _root_.Itasca.metadata.Env)
  (count : Std.U32) (ois : _root_.Itasca.code.OpIterState)
  (arity : Option Std.Usize) (i : Std.U32) :
  Result (ControlFlow (_root_.Itasca.code.OpIterState × (Option Std.Usize) ×
    Std.U32)
    ((core.result.Result Unit _root_.Itasca.error.OpError) ×
    _root_.Itasca.code.BodyState))
  := do
  let (r, st) ← code.read_label_info { core := ois } data
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (_, ts) := val
    let r2 ← signature.ResultType.len ts env
    let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf2 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      match arity with
      | none =>
        let r3 ← code.check_suffix st.core env ts
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          if i = count
          then
            let ois1 ← code.mark_unreachable st.core
            ok (done (core.result.Result.Ok (), { core := ois1 }))
          else
            let i1 ← i + 1#u32
            ok (cont (st.core, some val1, i1))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
          ok (done (r4, st))
      | some expected =>
        if expected != val1
        then ok (done (core.result.Result.Err error.OpError.TypeMismatch, st))
        else
          let r3 ← code.check_suffix st.core env ts
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            if i = count
            then
              let ois1 ← code.mark_unreachable st.core
              ok (done (core.result.Result.Ok (), { core := ois1 }))
            else
              let i1 ← i + 1#u32
              ok (cont (st.core, arity, i1))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r4 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
            ok (done (r4, st))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r3 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
      ok (done (r3, st))
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
    ok (done (r1, st))

/-- The extracted `code.branch_table_with_loop` with the empty visitor, returning only the result
and body state. -/
def Wasm2.branchTableLoop
  (ois : code.OpIterState) (data : Slice U8) (env : metadata.Env)
  (count : U32) (arity : Option Usize) (i : U32) :
  Result (core.result.Result Unit error.OpError × code.BodyState) := do
  let (r, s, _) ← code.branch_table_with_loop
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor ois data env () count arity i
  .ok (r, s)

/-- `code.branch_table_with` with the empty visitor, unfolded to `Wasm2.branchTableLoop`. -/
def Wasm2.tableCore
  (st : _root_.Itasca.code.BodyState) (data : Slice Std.U8)
  (env : _root_.Itasca.metadata.Env) :
  Result ((core.result.Result Unit _root_.Itasca.error.OpError) ×
    _root_.Itasca.code.BodyState)
  := do
  let r ← reader.read_u32_leb data st.core.pos
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (count, «end») := val
    let (r1, ois) ←
      code.pop_with_type { st.core with pos := «end» } wasm_types.ValueType.I32
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      Wasm2.branchTableLoop ois data env count none 0#u32
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
      ok (r2, { core := ois })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
    ok (r1, st)


namespace Wasm2

@[simp] def tableCont (p : code.OpIterState × Option Usize × U32) :=
  (p.1, (), p.2.1, p.2.2)

@[simp] def tableDone (p : core.result.Result Unit error.OpError × code.BodyState) :=
  (p.1, p.2, ())

@[simp] def tableFlow :
    ControlFlow (code.OpIterState × Option Usize × U32)
      (core.result.Result Unit error.OpError × code.BodyState) →
    ControlFlow (code.OpIterState × Unit × Option Usize × U32)
      (core.result.Result Unit error.OpError × code.BodyState × Unit)
  | .cont p => .cont (tableCont p)
  | .done p => .done (tableDone p)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- The extracted loop body with the empty visitor equals `Wasm2.branchTableLoop.body` up to the
visitor component. -/
theorem tableBody_eq (data : Slice U8) (env : metadata.Env)
    (count : U32) (ois : code.OpIterState) (arity : Option Usize)
    (i : U32) :
    code.branch_table_with_loop.body code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env count ois () arity i =
      (do let cf ← Wasm2.branchTableLoop.body data env count ois arity i
          .ok (tableFlow cf)) := by
  simp only [code.branch_table_with_loop.body, Wasm2.branchTableLoop.body, Std.bind_assoc]
  congr 1
  funext x
  obtain ⟨r, st⟩ := x
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      tableFlow, tableDone]
  | Ok pair =>
    obtain ⟨depth, ts⟩ := pair
    simp only [uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.bind_assoc]
    by_cases h : i = count <;> cases arity <;>
      simp [h, code.OpVisitor.on_br_table_label.default, code.OpVisitor.on_br_table.default,
        code.visit,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        Std.bind_assoc, tableFlow, tableCont, tableDone]
    all_goals
      congr 1
      funext r
      cases r <;> simp [Std.bind_assoc]
    all_goals try split <;> simp [Std.bind_assoc]
    all_goals
      congr 1
      funext r
      cases r <;> simp [Std.bind_assoc]

end Wasm2

/-- The extracted `code.branch_table_with` with the empty visitor equals `Wasm2.tableCore`. -/
theorem code.branch_table_with.eq_core (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
     :
    (do let (r, s, _) ← code.branch_table_with code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
          st data env (); .ok (r, s)) = Wasm2.tableCore st data env := by
  simp only [code.branch_table_with, Wasm2.tableCore,
    Wasm2.branchTableLoop, Std.bind_assoc]
  congr 1
  funext r
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨count, next⟩ := pair
    simp only [uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.bind_assoc]
    congr 1
    funext x
    obtain ⟨r, ois⟩ := x
    cases r <;> simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- The extracted `code.branch_table` equals `Wasm2.tableCore`. -/
theorem code.branch_table.eq_core (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
     :
    code.branch_table st data env = Wasm2.tableCore st data env := by
  rw [← code.branch_table_with.eq_core]
  simp only [code.branch_table]

end Itasca

end
