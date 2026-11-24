import Itasca.Body.Step.Context
import Itasca.Body.References.Readers
import Itasca.Body.NumericExt.Total
import Itasca.Body.References.Reader

/-!
Proofs for Body / Bulk.

This module collects Total, Visitor, Operands, Step.
Each section documents its contracts and consumers.
-/

/-! ## Total -/

section

/-! ## Dispatch -/

section

/-!
# Dispatch of bulk instructions

`Body.bulkStep` unfolds the extracted `code.step_bulk` (the `0xFC` subopcodes 8 to 17) into
`Visitor.Core.run` applied to each bulk reader and its visitor callback. `code.step_bulk.eq_runs`
proves the two equal.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- Factorization of the bulk instruction callbacks around their readers. -/
def bulkStep {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (opcode : U32) (v : V) :
    Result (core.result.Result Unit error.OpError × code.OpIterState × V) :=
  match opcode with
  | 8#uscalar => Visitor.Core.run (code.read_memory_init st data env) (fun v s a => visitor.on_memory_init v s a) v
  | 9#uscalar => Visitor.Core.run (code.take_data_index st data env) (fun v s a => visitor.on_data_drop v s a) v
  | 10#uscalar => Visitor.Core.run (code.read_memory_copy st data env) (fun v s _ => visitor.on_memory_copy v s) v
  | 11#uscalar => Visitor.Core.run (code.read_memory_fill st data env) (fun v s _ => visitor.on_memory_fill v s) v
  | 12#uscalar => Visitor.Core.run (code.read_table_init st data env) (fun v s a => visitor.on_table_init v s a.1 a.2) v
  | 13#uscalar => Visitor.Core.run (code.take_element st data env) (fun v s a => visitor.on_elem_drop v s a.1) v
  | 14#uscalar => Visitor.Core.run (code.read_table_copy st data env) (fun v s a => visitor.on_table_copy v s a.1 a.2) v
  | 15#uscalar => Visitor.Core.run (code.read_table_grow st data env) (fun v s a => visitor.on_table_grow v s a) v
  | 16#uscalar => Visitor.Core.run (code.read_table_size st data env) (fun v s a => visitor.on_table_size v s a) v
  | 17#uscalar => Visitor.Core.run (code.read_table_fill st data env) (fun v s a => visitor.on_table_fill v s a) v
  | _ => .ok (.Err .UnrecognizedOpcode, st, v)

end Itasca.Body

namespace Itasca

/-- `code.step_bulk` equals its unfolded form `Body.bulkStep`. -/
theorem code.step_bulk.eq_runs {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (opcode : U32) (v : V) :
    code.step_bulk visitor st data env opcode v = Body.bulkStep visitor st data env opcode v := by
  unfold code.step_bulk Body.bulkStep
  split <;> try rfl
  all_goals simp only [Visitor.Core.run]
  all_goals congr 1
  all_goals funext pair
  all_goals obtain ⟨r, s⟩ := pair
  all_goals cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  all_goals try (rename_i a; cases (show U32 × U32 from a))
  all_goals try (rename_i a; cases (show U32 × wasm_types.ValueType from a))
  all_goals try simp only [Std.uncurry]
  all_goals congr 1
  all_goals funext pair
  all_goals obtain ⟨reply, w⟩ := pair
  all_goals cases reply <;> simp [code.visit]

end Itasca

end

/-! ## Total -/

section

/-!
# Totality of bulk instructions

`bulk_total` shows that `code.step_bulk` never panics under a total visitor, and preserves
`Body.Control.Shape`, the control stack depth and cursor monotonicity for arbitrary immediate bytes.
`run_reader_total` lifts a reader's termination contract through its callback.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- A returning hook preserves a reader's structural termination contract. -/
theorem run_reader_total {A V : Type} (st : code.OpIterState)
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V)
    (hr : read ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ st.pos.val ≤ r.2.pos.val ⦄)
    (hh : ∀ s a, ∃ res v', hook v s a = .ok (res, v')) :
    Visitor.Core.run read hook v ⦃ r => Body.Control.Shape r.2.1 ∧
      r.2.1.ctrls.val.length = st.ctrls.val.length ∧ st.pos.val ≤ r.2.1.pos.val ⦄ := by
  apply WP.spec_mono (Visitor.Core.run.spec read hook v
    (fun s => Body.Control.Shape s ∧ s.ctrls = st.ctrls ∧ st.pos.val ≤ s.pos.val)
    (fun _ _ => True) ?_ hh)
  · rintro r ⟨⟨hs, hc, hp⟩, _⟩
    exact ⟨hs, by simp [hc], hp⟩
  · apply WP.spec_mono hr
    exact fun _ h => ⟨h, by simp⟩

/-- Bulk instructions preserve structural bounds for arbitrary immediate bytes. -/
theorem bulk_total {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (opcode : U32) (v : V)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max)
    (hv : Visitor.Total visitor) :
    code.step_bulk visitor st data env opcode v ⦃ r => Body.Control.Shape r.2.1 ∧
      r.2.1.ctrls.val.length = st.ctrls.val.length ∧ st.pos.val ≤ r.2.1.pos.val ⦄ := by
  rw [code.step_bulk.eq_runs]
  unfold bulkStep
  split
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_memory_init.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_memory_init v s a
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.take_data_index.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_data_drop v s a
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_memory_copy.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_memory_copy v s
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_memory_fill.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_memory_fill v s
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_table_init.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_table_init v s a.1 a.2
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.take_element.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_elem_drop v s a.1
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_table_copy.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_table_copy v s a.1 a.2
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_table_grow.total st data env hs hsize)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_table_grow v s a
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_table_size.total st data env hs hsize)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_table_size v s a
  · apply run_reader_total st _ _ v
    · apply WP.spec_mono (code.read_table_fill.total st data env hs)
      exact fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    · exact fun s a => hv.on_table_fill v s a
  · simp [hs]

end Itasca.Body

end

end

/-! ## Visitor -/

section

/-!
# Visitor transfer for bulk instructions

`bulk_transfer` shows that if `code.step_bulk` accepts with one visitor, it accepts with any
replacement visitor whose callbacks accept, reaching the same reader state.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Visitor

/-- Accepted replacement hooks preserve every successful bulk reader state. -/
theorem bulk_transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : Visitor.Accepts replacement)
    (st final : code.OpIterState) (data : Slice U8) (env : metadata.Env) (opcode : U32)
    (v v' : V) (w : W)
    (h : code.step_bulk visitor st data env opcode v = .ok (.Ok (), final, v')) :
    ∃ w', code.step_bulk replacement st data env opcode w = .ok (.Ok (), final, w') := by
  rw [code.step_bulk.eq_runs] at h ⊢
  unfold bulkStep at h ⊢
  split at h
  case h_1 =>
    exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_memory_init w final a)
  case h_2 =>
    exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_data_drop w final a)
  case h_3 =>
    exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_memory_copy w final)
  case h_4 =>
    exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_memory_fill w final)
  case h_5 =>
    exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_table_init w final a.1 a.2)
  case h_6 =>
    exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_elem_drop w final a.1)
  case h_7 =>
    exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_table_copy w final a.1 a.2)
  case h_8 =>
    exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_table_grow w final a)
  case h_9 =>
    exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_table_size w final a)
  case h_10 =>
    exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_table_fill w final a)
  case h_11 => simp at h

end Itasca.Body.Visitor

end

/-! ## Operands -/

section

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

local instance : DecidableEq Itasca.wasm_types.ValueType := Classical.decEq _

namespace Itasca.Body

/-- Read a data-segment index and the reserved memory-zero byte before operands. -/
def memoryInitMetadata (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
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
def memoryCopyMetadata (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
    Result (core.result.Result Unit error.OpError × code.OpIterState) := do
  let (r, s) ← code.read_bulk_memory st data env
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok () => code.read_reserved_zero s data

/-- Reads a second table index and requires its reference type to equal the first one's, as
`table.copy` and `table.init` do. -/
def referencePairMetadata
    (first : Result (core.result.Result (U32 × wasm_types.ValueType) error.OpError × code.OpIterState))
    (data : Slice U8) (env : metadata.Env) :
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

end Itasca.Body

namespace Itasca

theorem wasm_types.ValueType.ne.eq (a b : wasm_types.ValueType) :
    core.cmp.PartialEq.ne.trait_default wasm_types.ValueType.Insts.CoreCmpPartialEqValueType a b =
      .ok (decide (a ≠ b)) := by
  cases a <;> cases b <;> simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    wasm_types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

theorem code.read_bulk_operands.fixed (st : code.OpIterState) :
    code.read_bulk_operands st = Body.Simd.readFixed st [.I32, .I32, .I32] none := by
  simp only [code.read_bulk_operands, Body.Simd.readFixed]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual])

theorem code.read_memory_fill.fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
    code.read_memory_fill st data env = Body.metadataOperands (code.read_bulk_memory st data env)
      (fun _ => [.I32, .I32, .I32]) (fun _ => none) id := by
  simp only [code.read_memory_fill, Body.metadataOperands,
    code.read_bulk_operands.fixed]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Body.Simd.readFixed, Std.bind_assoc, Std.uncurry])

theorem code.read_memory_init.fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
    code.read_memory_init st data env = Body.metadataOperands (Body.memoryInitMetadata st data env)
      (fun _ => [.I32, .I32, .I32]) (fun _ => none) id := by
  simp only [code.read_memory_init, Body.metadataOperands, Body.memoryInitMetadata,
    code.read_bulk_operands.fixed, Std.bind_assoc]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Body.Simd.readFixed, Std.bind_assoc, Std.uncurry])

theorem code.read_memory_copy.fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
    code.read_memory_copy st data env = Body.metadataOperands (Body.memoryCopyMetadata st data env)
      (fun _ => [.I32, .I32, .I32]) (fun _ => none) id := by
  simp only [code.read_memory_copy, Body.metadataOperands, Body.memoryCopyMetadata,
    code.read_bulk_operands.fixed, Std.bind_assoc]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Body.Simd.readFixed, Std.bind_assoc, Std.uncurry])

theorem code.read_table_init.fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
    code.read_table_init st data env = Body.metadataOperands (Body.referencePairMetadata (code.take_element st data env) data env)
      (fun _ => [.I32, .I32, .I32]) (fun _ => none) id := by
  simp only [code.read_table_init, Body.metadataOperands, Body.referencePairMetadata,
    code.read_bulk_operands.fixed, Std.bind_assoc]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Body.Simd.readFixed, Std.bind_assoc, Std.uncurry])
    | (rename_i a; cases (show U32 × wasm_types.ValueType from a))
    | (simp only [wasm_types.ValueType.ne.eq, bind_ok]; split <;> simp_all)

theorem code.read_table_copy.fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
    code.read_table_copy st data env = Body.metadataOperands (Body.referencePairMetadata (code.take_table st data env) data env)
      (fun _ => [.I32, .I32, .I32]) (fun _ => none) id := by
  simp only [code.read_table_copy, Body.metadataOperands, Body.referencePairMetadata,
    code.read_bulk_operands.fixed, Std.bind_assoc]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Body.Simd.readFixed, Std.bind_assoc, Std.uncurry])
    | (rename_i a; cases (show U32 × wasm_types.ValueType from a))
    | (simp only [wasm_types.ValueType.ne.eq, bind_ok]; split <;> simp_all)

end Itasca

open Aeneas Aeneas.Std

namespace Itasca.Body

theorem memoryInitMetadata.spec (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
    memoryInitMetadata st data env ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ idx, r.1 = .Ok idx → ∃ bytes,
        Body.Scalar.BytesAt data st.pos (bytes ++ [0#u8]) r.2.pos ∧ Binary.Leb128.Encoding bytes idx.val ∧
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
      exact ⟨bytes, (Body.Scalar.BytesAt.mk hbs hbl hbb).append hzero, hbe, hcount, hmem⟩

theorem memoryCopyMetadata.spec (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) :
    memoryCopyMetadata st data env ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      (r.1 = .Ok () → Body.Scalar.BytesAt data st.pos [0#u8, 0#u8] r.2.pos ∧ 0 < env.mem_types.val.length) ⦄ := by
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
    exact ⟨(hd rfl).1.append (Body.Scalar.BytesAt.byte data middle.pos out.pos _ hp hz hpos), (hd rfl).2⟩

/-- Sequential reference-index decoding preserves each byte span and compares
the two resolved element types before the fixed operand checker runs. -/
theorem referencePairMetadata.spec
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (first : Result (core.result.Result (U32 × wasm_types.ValueType) error.OpError × code.OpIterState))
    (P : U32 → wasm_types.ValueType → Usize → Prop)
    (hf : first ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ idx ty, r.1 = .Ok (idx, ty) → P idx ty r.2.pos ⦄) :
    referencePairMetadata first data env ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ i j, r.1 = .Ok (i, j) → ∃ middle ty,
        P i ty middle ∧ Binary.Leb128.Decoded data middle j r.2.pos ∧
        ∃ hi : j.val < env.table_types.val.length,
          ty = Module.Constants.referenceValueType env.table_types.val[j.val].elem ⦄ := by
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

end Itasca.Body

end

/-! ## Step -/

section

/-!
# Preservation for bulk instructions

`Pending.memory_fill`, `Pending.memory_copy`, `Pending.memory_init`, `Pending.table_init` and
`Pending.table_copy` show that the extracted bulk readers preserve the body invariant `Pending`
(Wasm 2.0). They take the already decoded `0xFC` prefix as a premise.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

theorem Pending.memory_fill {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 11#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_memory_fill {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_memory_fill.fixed]
  apply p.metadata_read
    (code.read_bulk_memory {st.core with pos := next} data env)
    (fun _ => [.I32, .I32, .I32]) (fun _ => none) id (fun _ => .MEMORY_FILL) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (code.read_bulk_memory.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    intro u hok
    cases u
    obtain ⟨hb, _⟩ := hd hok
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 11#u32 hpe .memoryFill)
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append hb)
  · exact fun _ => .instr_case_64
  · rintro u ⟨decoded, hrun⟩ C hC
    cases u
    have hspec := code.read_bulk_memory.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    simpa [Simd.inputTypes, Simd.outputTypes, Translation.valueType] using hC.memory_fill (hspec.2.2 rfl).2

theorem Pending.memory_copy {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 10#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_memory_copy {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_memory_copy.fixed]
  apply p.metadata_read
    (memoryCopyMetadata {st.core with pos := next} data env)
    (fun _ => [.I32, .I32, .I32]) (fun _ => none) id (fun _ => .MEMORY_COPY) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (memoryCopyMetadata.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    intro u hok
    cases u
    obtain ⟨hb, _⟩ := hd hok
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 10#u32 hpe .memoryCopy)
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append hb)
  · exact fun _ => .instr_case_65
  · rintro u ⟨decoded, hrun⟩ C hC
    cases u
    have hspec := memoryCopyMetadata.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    simpa [Simd.inputTypes, Simd.outputTypes, Translation.valueType] using hC.memory_copy (hspec.2.2 rfl).2

theorem Pending.memory_init {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 8#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_memory_init {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_memory_init.fixed]
  apply p.metadata_read
    (memoryInitMetadata {st.core with pos := next} data env)
    (fun _ => [.I32, .I32, .I32]) (fun _ => none) id
    (fun idx => .MEMORY_INIT (.mk_uN idx.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono (memoryInitMetadata.spec {st.core with pos := next} data env)
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    intro idx hok
    obtain ⟨bytes, hb, he, _⟩ := hd idx hok
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 8#u32 hpe (.memoryInit idx he))
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append hb)
  · exact fun idx => .instr_case_66 _ (Translation.Environment.index_wf idx)
  · rintro idx ⟨decoded, hrun⟩ C hC
    have hspec := memoryInitMetadata.spec {st.core with pos := next} data env
    rw [hrun, WP.spec_ok] at hspec
    obtain ⟨_, _, _, ⟨count, hcount, hi⟩, hm⟩ := hspec.2.2 idx rfl
    simpa [Simd.inputTypes, Simd.outputTypes, Translation.valueType] using hC.memory_init idx count hcount hi hm

theorem reference_value_injective {a b : wasm_types.ElemType}
    (h : Module.Constants.referenceValueType a = Module.Constants.referenceValueType b) : a = b := by
  cases a <;> cases b <;> simp_all [Module.Constants.referenceValueType]

theorem Pending.table_init {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 12#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_table_init {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_table_init.fixed]
  have hmetadata := referencePairMetadata.spec {st.core with pos := next} data env
    (code.take_element {st.core with pos := next} data env)
    (fun i ty pos => Binary.Leb128.Decoded data next i pos ∧
      ∃ hi : i.val < env.elements.val.length,
        ty = Module.Constants.referenceValueType env.elements.val[i.val].elem)
    (code.take_element.spec {st.core with pos := next} data env)
  apply p.metadata_read
    _ (fun _ => [.I32, .I32, .I32]) (fun _ => none) id
    (fun a => .TABLE_INIT (.mk_uN a.2.val) (.mk_uN a.1.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono hmetadata
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    rintro ⟨i, j⟩ hok
    obtain ⟨middle, ty, ⟨hdi, _⟩, hdj, _⟩ := hd i j hok
    obtain ⟨ibs, his, hil, hib, hie⟩ := hdi
    obtain ⟨jbs, hjs, hjl, hjb, hje⟩ := hdj
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 12#u32 hpe (.tableInit i j hie hje))
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append ((Body.Scalar.BytesAt.mk his hil hib).append ⟨hjs, hjl, hjb⟩))
  · exact fun a => .instr_case_54 _ _ (Translation.Environment.index_wf a.2) (Translation.Environment.index_wf a.1)
  · rintro ⟨i, j⟩ ⟨decoded, hrun⟩ C hC
    rw [hrun, WP.spec_ok] at hmetadata
    obtain ⟨middle, ty, ⟨_, hi, hity⟩, _, hj, hjty⟩ := hmetadata.2.2 i j rfl
    simpa [Simd.inputTypes, Simd.outputTypes, Translation.valueType] using
      hC.table_init j i env.table_types.val[j.val] env.elements.val[i.val] hj hi rfl rfl (reference_value_injective (hity.symm.trans hjty))

theorem Pending.table_copy {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 14#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    code.read_table_copy {st.core with pos := next} data env ⦃ r =>
      (∃ a, r.1 = .Ok a) → p.After {st with core := r.2} ⦄ := by
  rw [code.read_table_copy.fixed]
  have hmetadata := referencePairMetadata.spec {st.core with pos := next} data env
    (code.take_table {st.core with pos := next} data env)
    (fun i ty pos => Binary.Leb128.Decoded data next i pos ∧
      ∃ hi : i.val < env.table_types.val.length,
        ty = Module.Constants.referenceValueType env.table_types.val[i.val].elem)
    (code.take_table.spec {st.core with pos := next} data env)
  apply p.metadata_read
    _ (fun _ => [.I32, .I32, .I32]) (fun _ => none) id
    (fun a => .TABLE_COPY (.mk_uN a.1.val) (.mk_uN a.2.val)) ?_ ?_ ?_ hsize
  · apply WP.spec_mono hmetadata
    rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
    refine ⟨hv, hc, ?_⟩
    rintro ⟨i, j⟩ hok
    obtain ⟨middle, ty, ⟨hdi, _⟩, hdj, _⟩ := hd i j hok
    obtain ⟨ibs, his, hil, hib, hie⟩ := hdi
    obtain ⟨jbs, hjs, hjl, hjb, hje⟩ := hdj
    obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
    exact At.of_immediate p.inbounds hbyte p.pos (.bulk 14#u32 hpe (.tableCopy i j hie hje))
      ((Body.Scalar.BytesAt.mk hp hpl hpb).append ((Body.Scalar.BytesAt.mk his hil hib).append ⟨hjs, hjl, hjb⟩))
  · exact fun a => .instr_case_53 _ _ (Translation.Environment.index_wf a.1) (Translation.Environment.index_wf a.2)
  · rintro ⟨i, j⟩ ⟨decoded, hrun⟩ C hC
    rw [hrun, WP.spec_ok] at hmetadata
    obtain ⟨middle, ty, ⟨_, hi, hity⟩, _, hj, hjty⟩ := hmetadata.2.2 i j rfl
    simpa [Simd.inputTypes, Simd.outputTypes, Translation.valueType] using
      hC.table_copy i j env.table_types.val[i.val] env.table_types.val[j.val] hi hj rfl rfl (reference_value_injective (hjty.symm.trans hity))

end Itasca.Body

end
