import Itasca.Wasm2.References.Operands

/-!
# Operand factorization of bulk readers

Defines the metadata decoders `memoryInitMetadata`, `memoryCopyMetadata` and
`referencePairMetadata`, and shows that `code.read_memory_init`, `code.read_memory_copy`,
`code.read_memory_fill`, `code.read_table_init` and `code.read_table_copy` equal a decoder
followed by the fixed operand checker (`*.fixed`). Their specs (`*.spec`) give byte provenance
and the type agreement of the table pair.
-/

open Aeneas Aeneas.Std

noncomputable section

local instance : DecidableEq Itasca.types.ValueType := Classical.decEq _

namespace Itasca.Wasm2

/-- Read a data-segment index and the reserved memory-zero byte before operands. -/
def memoryInitMetadata (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    Result (core.result.Result U32 error.OpError × code.OpIterState) := do
  let (r, s) ← code.take_data_index st data env
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok idx =>
    let (r, out) ← code.read_bulk_memory s data env
    match r with
    | .Err e => .ok (.Err e, out)
    | .Ok () => .ok (.Ok idx, out)

/-- Wasm 2.0 `memory.copy` reads two reserved literal memory-zero bytes. -/
def memoryCopyMetadata (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    Result (core.result.Result Unit error.OpError × code.OpIterState) := do
  let (r, s) ← code.read_bulk_memory st data env
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok () => code.read_reserved_zero s data

/-- Reads a second table index and requires its reference type to equal the first one's, as
`table.copy` and `table.init` do. -/
def referencePairMetadata
    (first : Result (core.result.Result (U32 × types.ValueType) error.OpError × code.OpIterState))
    (data : Slice U8) (env : module.Env) :
    Result (core.result.Result (U32 × U32) error.OpError × code.OpIterState) := do
  let (r, s) ← first
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok (firstIdx, firstTy) =>
    let (r, out) ← code.take_table s data env
    match r with
    | .Err e => .ok (.Err e, out)
    | .Ok (secondIdx, secondTy) =>
      if firstTy = secondTy then .ok (.Ok (firstIdx, secondIdx), out)
      else .ok (.Err .TypeMismatch, out)

end Itasca.Wasm2

namespace Itasca

theorem types.ValueType.ne.eq (a b : types.ValueType) :
    core.cmp.PartialEq.ne.trait_default types.ValueType.Insts.CoreCmpPartialEqValueType a b =
      .ok (decide (a ≠ b)) := by
  cases a <;> cases b <;> simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

theorem code.read_bulk_operands.fixed (st : code.OpIterState) :
    code.read_bulk_operands st = Wasm2.Simd.readFixed st [.I32, .I32, .I32] none := by
  simp only [code.read_bulk_operands, Wasm2.Simd.readFixed]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual])

theorem code.read_memory_fill.fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_memory_fill st data env = Wasm2.metadataOperands (code.read_bulk_memory st data env)
      (fun _ => [.I32, .I32, .I32]) (fun _ => none) id := by
  simp only [code.read_memory_fill, Wasm2.metadataOperands, 
    code.read_bulk_operands.fixed]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry])

theorem code.read_memory_init.fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_memory_init st data env = Wasm2.metadataOperands (Wasm2.memoryInitMetadata st data env)
      (fun _ => [.I32, .I32, .I32]) (fun _ => none) id := by
  simp only [code.read_memory_init, Wasm2.metadataOperands, Wasm2.memoryInitMetadata,
    code.read_bulk_operands.fixed, Std.bind_assoc]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry])

theorem code.read_memory_copy.fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_memory_copy st data env = Wasm2.metadataOperands (Wasm2.memoryCopyMetadata st data env)
      (fun _ => [.I32, .I32, .I32]) (fun _ => none) id := by
  simp only [code.read_memory_copy, Wasm2.metadataOperands, Wasm2.memoryCopyMetadata,
    code.read_bulk_operands.fixed, Std.bind_assoc]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry])

theorem code.read_table_init.fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_table_init st data env = Wasm2.metadataOperands (Wasm2.referencePairMetadata (code.take_element st data env) data env)
      (fun _ => [.I32, .I32, .I32]) (fun _ => none) id := by
  simp only [code.read_table_init, Wasm2.metadataOperands, Wasm2.referencePairMetadata,
    code.read_bulk_operands.fixed, Std.bind_assoc]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry])
    | (rename_i a; cases (show U32 × types.ValueType from a))
    | (simp only [types.ValueType.ne.eq, bind_ok]; split <;> simp_all)

theorem code.read_table_copy.fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_table_copy st data env = Wasm2.metadataOperands (Wasm2.referencePairMetadata (code.take_table st data env) data env)
      (fun _ => [.I32, .I32, .I32]) (fun _ => none) id := by
  simp only [code.read_table_copy, Wasm2.metadataOperands, Wasm2.referencePairMetadata,
    code.read_bulk_operands.fixed, Std.bind_assoc]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry])
    | (rename_i a; cases (show U32 × types.ValueType from a))
    | (simp only [types.ValueType.ne.eq, bind_ok]; split <;> simp_all)

end Itasca

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

theorem memoryInitMetadata.spec (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    memoryInitMetadata st data env ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ idx, r.1 = .Ok idx → ∃ bytes,
        Wasm1.BytesAt data st.pos (bytes ++ [0#u8]) r.2.pos ∧ Leb128.Encoding bytes idx.val ∧
        (∃ count, env.data_count = some count ∧ idx.val < count.val) ∧ 0 < env.mem_types.val.length ⦄ := by
  obtain ⟨⟨res, middle⟩, hr, hv, hc, hd⟩ := WP.spec_imp_exists (code.take_data_index.spec st data env)
  dsimp only at hv hc hd
  cases res with
  | Err e => simp [memoryInitMetadata, hr, hv, hc]
  | Ok idx =>
    obtain ⟨⟨res, out⟩, ho, hov, hoc, hod⟩ := WP.spec_imp_exists (code.read_bulk_memory.spec middle data env)
    dsimp only at hov hoc hod
    cases res with
    | Err e => simp [memoryInitMetadata, hr, ho, hov, hoc, hv, hc]
    | Ok u =>
      cases u
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok idx, out), by simp [memoryInitMetadata, hr, ho], hov.trans hv, hoc.trans hc, ?_⟩
      intro other he
      cases he
      obtain ⟨⟨bytes, hbs, hbl, hbb, hbe⟩, hcount⟩ := hd idx rfl
      obtain ⟨hzero, hmem⟩ := hod rfl
      exact ⟨bytes, (Wasm1.BytesAt.mk hbs hbl hbb).append hzero, hbe, hcount, hmem⟩

theorem memoryCopyMetadata.spec (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    memoryCopyMetadata st data env ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      (r.1 = .Ok () → Wasm1.BytesAt data st.pos [0#u8, 0#u8] r.2.pos ∧ 0 < env.mem_types.val.length) ⦄ := by
  obtain ⟨⟨res, middle⟩, hr, hv, hc, hd⟩ := WP.spec_imp_exists (code.read_bulk_memory.spec st data env)
  dsimp only at hv hc hd
  cases res with
  | Err e => simp [memoryCopyMetadata, hr, hv, hc]
  | Ok u =>
    cases u
    simp only [memoryCopyMetadata, hr, bind_ok]
    apply WP.spec_mono (code.read_reserved_zero.spec middle data)
    rintro ⟨res, out⟩ ⟨hov, hoc, hod⟩
    refine ⟨hov.trans hv, hoc.trans hc, ?_⟩
    intro hok
    dsimp only at hov hoc hod hok
    subst res
    obtain ⟨hp, hz, hpos⟩ := hod
    exact ⟨(hd rfl).1.append (Wasm1.BytesAt.byte data middle.pos out.pos _ hp hz hpos), (hd rfl).2⟩

/-- Sequential reference-index decoding preserves each byte span and compares
the two resolved element types before the fixed operand checker runs. -/
theorem referencePairMetadata.spec
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (first : Result (core.result.Result (U32 × types.ValueType) error.OpError × code.OpIterState))
    (P : U32 → types.ValueType → Usize → Prop)
    (hf : first ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ idx ty, r.1 = .Ok (idx, ty) → P idx ty r.2.pos ⦄) :
    referencePairMetadata first data env ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ i j, r.1 = .Ok (i, j) → ∃ middle ty,
        P i ty middle ∧ Leb128.Decoded data middle j r.2.pos ∧
        ∃ hi : j.val < env.table_types.val.length,
          ty = ModuleConstants.referenceValueType env.table_types.val[j.val].elem ⦄ := by
  classical
  obtain ⟨⟨res, middle⟩, hr, hv, hc, hd⟩ := WP.spec_imp_exists hf
  dsimp only at hv hc hd
  cases res with
  | Err e => simp [referencePairMetadata, hr, hv, hc]
  | Ok pair =>
    obtain ⟨i, ty⟩ := pair
    obtain ⟨⟨res, out⟩, ho, hov, hoc, hod⟩ := WP.spec_imp_exists (code.take_table.spec middle data env)
    dsimp only at hov hoc hod
    cases res with
    | Err e => simp [referencePairMetadata, hr, ho, hov, hoc, hv, hc]
    | Ok pair =>
      obtain ⟨j, ty'⟩ := pair
      by_cases he : ty = ty'
      · subst ty'
        rw [WP.spec_equiv_exists]
        refine ⟨(.Ok (i, j), out), by simp [referencePairMetadata, hr, ho],
          hov.trans hv, hoc.trans hc, ?_⟩
        intro otherI otherJ hok
        cases hok
        exact ⟨middle.pos, ty, hd i ty rfl, hod j ty rfl⟩
      · simp [referencePairMetadata, hr, ho, he, hov, hoc, hv, hc]

end Itasca.Wasm2
