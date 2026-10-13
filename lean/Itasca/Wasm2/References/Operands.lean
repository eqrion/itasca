import Itasca.Wasm2.References.Readers
import Itasca.Wasm2.FixedOperands

/-!
# Operand factorization of reference readers

Each extracted `code.read_ref_null`, `code.read_table_get`, `code.read_table_set`,
`code.read_table_grow`, `code.read_table_size`, `code.read_table_fill` and
`code.read_typed_select` equals `Wasm2.metadataOperands` applied to its metadata decoder, which
is the decoder followed by the fixed pop and push of `Simd.readFixed`.
`code.read_ref_is_null.segment` gives the typing of the polymorphic null test.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- A checked metadata reader followed by a fixed stack effect. The result keeps the decoded
metadata for the instruction's visitor hook. -/
def metadataOperands {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List types.ValueType) (output : A → Option types.ValueType)
    (metadata : A → B) : Result (core.result.Result B error.OpError × code.OpIterState) := do
  let (r, s) ← decode
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok a =>
    let (r, out) ← Simd.readFixed s (pops a) (output a)
    match r with
    | .Err e => .ok (.Err e, out)
    | .Ok () => .ok (.Ok (metadata a), out)

/-- The explicit select vector has exactly one literal value-type entry. -/
def selectType (st : code.OpIterState) (data : Slice U8) :
    Result (core.result.Result types.ValueType error.OpError × code.OpIterState) := do
  let (r, s) ← code.take_index st data
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok count =>
      if count = 1#u32 then code.take_value_type s data
      else .ok (.Err .TypeMismatch, s)

theorem selectType.spec (st : code.OpIterState) (data : Slice U8) :
    selectType st data ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ ty, r.1 = .Ok ty → ∃ count,
        Wasm1.BytesAt data st.pos (count ++ [valueByte ty]) r.2.pos ∧ Leb128.Encoding count 1 ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hd⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  dsimp only at hv hc hd
  cases r with
  | Err e => simp [selectType, hr, hv, hc]
  | Ok count =>
    by_cases he : count = 1#u32
    · subst count
      simp only [selectType, hr, bind_ok]
      apply WP.spec_mono (code.take_value_type.spec s data)
      rintro ⟨res, out⟩ ⟨hvo, hco, htag⟩
      refine ⟨hvo.trans hv, hco.trans hc, ?_⟩
      intro ty hok
      obtain ⟨bytes, hb, hl, hn, he⟩ := hd
      exact ⟨bytes, (show Wasm1.BytesAt data st.pos bytes s.pos from ⟨hb, hl, hn⟩).append (htag ty hok), he⟩
    · simp [selectType, hr, he, hv, hc]

theorem metadataOperands.empty {A : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState)) :
    metadataOperands decode (fun _ => []) (fun _ => none) id = decode := by
  calc
    metadataOperands decode (fun _ => []) (fun _ => none) id = decode >>= Result.ok := by
      unfold metadataOperands
      congr 1
      funext pair
      obtain ⟨res, s⟩ := pair
      cases res <;> simp [Simd.readFixed]
    _ = decode := Std.bind_pure decode

end Itasca.Wasm2

namespace Itasca

/-- The extracted handler has exactly its metadata-dependent fixed operand effect. -/
theorem code.read_ref_null.fixed (st : code.OpIterState) (data : Slice U8) :
    code.read_ref_null st data = Wasm2.metadataOperands (code.take_reference_type st data)
      (fun _ => []) (fun rt => some (ModuleConstants.referenceValueType rt)) id := by
  simp only [code.read_ref_null, Wasm2.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      types.ElemType.value_type.eq, Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry]
    try dsimp only
    repeat' rfl

/-- The extracted handler has exactly its metadata-dependent fixed operand effect. -/
theorem code.read_table_get.fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_table_get st data env = Wasm2.metadataOperands (code.take_table st data env)
      (fun _ => [.I32]) (fun a => some a.2) Prod.fst := by
  simp only [code.read_table_get, Wasm2.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry]
    try dsimp only
    repeat' first
      | rfl
      | (congr 1
         funext pair
         obtain ⟨res, state⟩ := pair
         cases res <;> simp [
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
           Std.bind_assoc])

/-- The extracted handler has exactly its metadata-dependent fixed operand effect. -/
theorem code.read_table_set.fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_table_set st data env = Wasm2.metadataOperands (code.take_table st data env)
      (fun a => [a.2, .I32]) (fun _ => none) Prod.fst := by
  simp only [code.read_table_set, Wasm2.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry]
    try dsimp only
    repeat' first
      | rfl
      | (congr 1
         funext pair
         obtain ⟨res, state⟩ := pair
         cases res <;> simp [
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
           Std.bind_assoc])

/-- The extracted handler has exactly its metadata-dependent fixed operand effect. -/
theorem code.read_table_grow.fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_table_grow st data env = Wasm2.metadataOperands (code.take_table st data env)
      (fun a => [.I32, a.2]) (fun _ => some .I32) Prod.fst := by
  simp only [code.read_table_grow, Wasm2.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry]
    try dsimp only
    repeat' first
      | rfl
      | (congr 1
         funext pair
         obtain ⟨res, state⟩ := pair
         cases res <;> simp [
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
           Std.bind_assoc])

/-- The extracted handler has exactly its metadata-dependent fixed operand effect. -/
theorem code.read_table_size.fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_table_size st data env = Wasm2.metadataOperands (code.take_table st data env)
      (fun _ => []) (fun _ => some .I32) Prod.fst := by
  simp only [code.read_table_size, Wasm2.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry]
    try dsimp only

/-- The extracted handler has exactly its metadata-dependent fixed operand effect. -/
theorem code.read_table_fill.fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_table_fill st data env = Wasm2.metadataOperands (code.take_table st data env)
      (fun a => [.I32, a.2, .I32]) (fun _ => none) Prod.fst := by
  simp only [code.read_table_fill, Wasm2.metadataOperands]
  congr 1
  funext pair
  obtain ⟨r, state⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok a =>
    try (cases (show U32 × types.ValueType from a))
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry]
    try dsimp only
    repeat' first
      | rfl
      | (congr 1
         funext pair
         obtain ⟨res, state⟩ := pair
         cases res <;> simp [
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
           Std.bind_assoc])

theorem code.read_typed_select.fixed (st : code.OpIterState) (data : Slice U8) :
    code.read_typed_select st data = Wasm2.metadataOperands (Wasm2.selectType st data)
      (fun ty => [.I32, ty, ty]) some id := by
  obtain ⟨⟨r, state⟩, hr, _⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  cases r with
  | Err e => simp [code.read_typed_select, Wasm2.metadataOperands, Wasm2.selectType, hr,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok count =>
    by_cases hc : count = 1#u32
    · subst count
      simp [code.read_typed_select, Wasm2.metadataOperands, Wasm2.selectType, hr,
        core.result.Result.Insts.CoreOpsTry.branch]
      congr 1
      funext pair
      obtain ⟨r, state⟩ := pair
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok ty =>
        simp only [bind_ok, Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry]
        repeat' first
          | rfl
          | (congr 1
             funext pair
             obtain ⟨res, state⟩ := pair
             cases res <;> simp [
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
               Std.bind_assoc])
    · have hcv : count.val ≠ 1 := fun he => hc (UScalar.eq_of_val_eq he)
      simp [code.read_typed_select, Wasm2.metadataOperands, Wasm2.selectType, hr, hc, hcv,
        core.result.Result.Insts.CoreOpsTry.branch]

/-- A successful null test consumes a reference (or the polymorphic bottom)
and produces i32. The chosen reference type remains explicit in the typing. -/
theorem code.read_ref_is_null.segment (st : code.OpIterState)
    (outer segment : List code.StackType)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_ref_is_null st ⦃ r => r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ after, r.2.vals.val = outer ++ after ∧
        (r.1 = .Ok () → ∃ rt, Wasm2.Simd.FixedEffect (Control.polymorphic st) segment
          [ModuleConstants.referenceValueType rt] (some .I32) after) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hc, hp, popped, hpv, hpop⟩ := WP.spec_imp_exists
    (code.pop_stack_type.segment st outer segment hv hb)
  dsimp only at hc hp hpv hpop
  have hlen := hpop.length
  cases r with
  | Err e =>
    simpa [code.read_ref_is_null, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using
      (show s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ ∃ after, s.vals.val = outer ++ after from
        ⟨hc, hp, popped, hpv⟩)
  | Ok t =>
    change StackSemantics.Popped (Control.polymorphic st) segment t popped at hpop
    have hcap : s.vals.val.length < Usize.max := by
      simp only [hv, hpv, List.length_append] at *
      omega
    have finish (rt : types.ElemType)
        (ht : Sequence.Accepts t (valtype_reftype (Translate.referenceType rt)))
        (hrun : code.read_ref_is_null st = do
          let out ← code.push_val s (.Val .I32)
          .ok (.Ok (), out)) :
        code.read_ref_is_null st ⦃ r => r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
          ∃ after, r.2.vals.val = outer ++ after ∧
            (r.1 = .Ok () → ∃ rt, Wasm2.Simd.FixedEffect (Control.polymorphic st) segment
              [ModuleConstants.referenceValueType rt] (some .I32) after) ⦄ := by
      obtain ⟨out, ho, hov, hoc, hop⟩ := WP.spec_imp_exists (code.push_val.spec s (.Val .I32) hcap)
      rw [hrun, ho, bind_ok, WP.spec_ok]
      refine ⟨hoc.trans hc, hop.trans hp, popped ++ [.Val .I32],
        by simpa [hpv, List.append_assoc] using hov, ?_⟩
      intro _
      refine ⟨rt, ?_⟩
      intro ts hts
      obtain ⟨front, hfront, rfl⟩ := (Sequence.realizes_append_concrete _ _ [.I32] ts).mp hts
      refine ⟨front, rfl, ?_⟩
      have hh := hpop.realizes front (valtype_reftype (Translate.referenceType rt)) ht hfront
      cases rt <;> simpa [Wasm2.Simd.inputTypes, ModuleConstants.referenceValueType, Translate.referenceType,
        Translate.valueType, valtype_reftype] using hh
    cases t with
    | Bot =>
      apply finish .FuncRef trivial
      simp [code.read_ref_is_null, hr, core.result.Result.Insts.CoreOpsTry.branch]
    | Val ty =>
      cases ty
      all_goals first
        | (apply finish .FuncRef rfl; simp [code.read_ref_is_null, hr, core.result.Result.Insts.CoreOpsTry.branch])
        | (apply finish .ExternRef rfl; simp [code.read_ref_is_null, hr, core.result.Result.Insts.CoreOpsTry.branch])
        | (simpa [code.read_ref_is_null, hr, core.result.Result.Insts.CoreOpsTry.branch] using
          (show s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ ∃ after, s.vals.val = outer ++ after from
            ⟨hc, hp, popped, hpv⟩))

end Itasca
