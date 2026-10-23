import Itasca.Wasm2.SignatureEquality
import Itasca.Binary.Wasm1.Subset

/-!
# Wasm 1.0 profile filters

The body reader runs the same rules for both profiles after four checks that only reject under
Wasm 1.0: `code.check_opcode`, `code.check_block_type`, `code.check_table_byte` and
`code.check_table_target`. Each is total, accepts everything under Wasm 2.0, and accepts exactly the
Wasm 1.0 grammar or `br_table` typing under Wasm 1.0.
-/

open Aeneas Aeneas.Std

namespace Itasca

theorem code.check_opcode.wasm2 (op : U8) : code.check_opcode .Wasm2 op = .ok (.Ok ()) := rfl

theorem code.check_opcode.complete (profile : ValidationProfile) (op : U8)
    (h : op.val ∉ Wasm1.extensionOpcodes) : code.check_opcode profile op = .ok (.Ok ()) := by
  cases profile with
  | Wasm2 => rfl
  | Wasm1 =>
    simp only [code.check_opcode]
    split
    all_goals first | rfl | exact absurd (by decide) h

theorem code.check_opcode.reject (op : U8) (h : op.val ∈ Wasm1.extensionOpcodes) :
    code.check_opcode .Wasm1 op = .ok (.Err .UnrecognizedOpcode) := by
  rcases op with ⟨⟨n, hn⟩⟩
  change n ∈ _ at h
  simp only [Wasm1.extensionOpcodes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[step]
theorem code.check_opcode.spec (profile : ValidationProfile) (op : U8) :
    code.check_opcode profile op ⦃ r => r = .Ok () → profile = .Wasm1 →
      op.val ∉ Wasm1.extensionOpcodes ⦄ := by
  by_cases h : op.val ∈ Wasm1.extensionOpcodes
  · cases profile with
    | Wasm2 => simp [code.check_opcode.wasm2]
    | Wasm1 => simp [code.check_opcode.reject op h]
  · simp [code.check_opcode.complete profile op h, h]

theorem code.check_block_type.wasm2 (bt : signature.BlockType) :
    code.check_block_type .Wasm2 bt = .ok (.Ok ()) := rfl

/-- Wasm 1.0 accepts exactly the block types with a one-byte Wasm 1.0 spelling. -/
@[step]
theorem code.check_block_type.spec (profile : ValidationProfile) (bt : signature.BlockType) :
    code.check_block_type profile bt ⦃ r => r = .Ok () → profile = .Wasm1 →
      ∃ b, Wasm1.ScalarBlockByte bt b ⦄ := by
  cases profile with
  | Wasm2 => simp [code.check_block_type.wasm2]
  | Wasm1 =>
    unfold code.check_block_type
    rcases bt with _ | t | _ <;> try cases t
    all_goals simp
    exacts [⟨_, .empty⟩, ⟨_, .i32⟩, ⟨_, .i64⟩, ⟨_, .f32⟩, ⟨_, .f64⟩]

theorem code.check_block_type.complete {bt : signature.BlockType} {b : U8}
    (h : Wasm1.ScalarBlockByte bt b) (profile : ValidationProfile) :
    code.check_block_type profile bt = .ok (.Ok ()) := by
  cases profile <;> cases h <;> rfl

theorem code.check_table_byte.wasm2 (data : Slice U8) (pos : Usize) :
    code.check_table_byte .Wasm2 data pos = .ok (.Ok ()) := rfl

/-- Wasm 1.0 accepts exactly a zero byte at the cursor. -/
@[step]
theorem code.check_table_byte.spec (profile : ValidationProfile) (data : Slice U8) (pos : Usize) :
    code.check_table_byte profile data pos ⦃ r => r = .Ok () → profile = .Wasm1 →
      ∃ h : pos.val < data.length, data.val[pos.val] = 0#u8 ⦄ := by
  cases profile with
  | Wasm2 => simp [code.check_table_byte.wasm2]
  | Wasm1 =>
    unfold code.check_table_byte
    by_cases hp : pos.val < data.length
    · obtain ⟨r, hr, next, rfl, _⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
      rw [hr]
      by_cases hz : data.val[pos.val] = 0#u8
      · simp [core.result.Result.Insts.CoreOpsTry.branch, hz, hp]
      · have hv : (data.val[pos.val]).val ≠ 0 := fun h => hz (UScalar.eq_of_val_eq h)
        simp [core.result.Result.Insts.CoreOpsTry.branch, hv]
    · rw [reader.read_byte.eof data pos (by omega)]
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem code.check_table_byte.complete (profile : ValidationProfile) (data : Slice U8) (pos : Usize)
    (hp : pos.val < data.length) (hz : data.val[pos.val] = 0#u8) :
    code.check_table_byte profile data pos = .ok (.Ok ()) := by
  cases profile with
  | Wasm2 => rfl
  | Wasm1 =>
    unfold code.check_table_byte
    obtain ⟨r, hr, next, rfl, _⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
    rw [hr]
    simp [core.result.Result.Insts.CoreOpsTry.branch, hz]

theorem code.check_table_target.wasm2 (env : module.Env) (first ts : signature.ResultType) :
    code.check_table_target .Wasm2 env first ts = .ok (.Ok ()) := rfl

/-- Wasm 1.0 accepts exactly targets whose types resolve to the first target's types. -/
@[step]
theorem code.check_table_target.spec (profile : ValidationProfile) (env : module.Env)
    (first ts : signature.ResultType) :
    code.check_table_target profile env first ts ⦃ r => r = .Ok () → profile = .Wasm1 →
      ∃ us, Wasm2.resolve env first = some us ∧ Wasm2.resolve env ts = some us ⦄ := by
  cases profile with
  | Wasm2 => simp [code.check_table_target.wasm2]
  | Wasm1 =>
    unfold code.check_table_target
    obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (code.same_types.spec env first ts)
    rw [hr]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok equal =>
      obtain ⟨us, vs, hf, ht, he⟩ := hs
      cases equal <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch]

theorem code.check_table_target.complete (profile : ValidationProfile) (env : module.Env)
    (first ts : signature.ResultType) (us : List types.ValueType)
    (hf : Wasm2.resolve env first = some us) (ht : Wasm2.resolve env ts = some us) :
    code.check_table_target profile env first ts = .ok (.Ok ()) := by
  cases profile with
  | Wasm2 => rfl
  | Wasm1 =>
    unfold code.check_table_target
    rw [code.same_types.complete env first ts us hf ht]
    simp [core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
