import Itasca.Wasm2.SignatureEquality

/-!
# Body profile checks

The retained profile checks accept all inputs under Wasm 2.0.
-/

open Aeneas Aeneas.Std
namespace Itasca

theorem code.check_opcode.wasm2 (op : U8) :
    code.check_opcode .Wasm2 op = .ok (.Ok ()) := rfl

theorem code.check_opcode.complete (profile : ValidationProfile) (op : U8) :
    code.check_opcode profile op = .ok (.Ok ()) := rfl

@[step]
theorem code.check_opcode.spec (profile : ValidationProfile) (op : U8) :
    code.check_opcode profile op ⦃ r => r = .Ok () ⦄ := by
  simp [code.check_opcode]

theorem code.check_block_type.wasm2 (bt : signature.BlockType) :
    code.check_block_type .Wasm2 bt = .ok (.Ok ()) := rfl

theorem code.check_block_type.complete (profile : ValidationProfile) (bt : signature.BlockType) :
    code.check_block_type profile bt = .ok (.Ok ()) := rfl

@[step]
theorem code.check_block_type.spec (profile : ValidationProfile) (bt : signature.BlockType) :
    code.check_block_type profile bt ⦃ r => r = .Ok () ⦄ := by
  simp [code.check_block_type]

theorem code.check_table_byte.wasm2 (data : Slice U8) (pos : Usize) :
    code.check_table_byte .Wasm2 data pos = .ok (.Ok ()) := rfl

theorem code.check_table_byte.complete (profile : ValidationProfile) (data : Slice U8) (pos : Usize) :
    code.check_table_byte profile data pos = .ok (.Ok ()) := rfl

@[step]
theorem code.check_table_byte.spec (profile : ValidationProfile) (data : Slice U8) (pos : Usize) :
    code.check_table_byte profile data pos ⦃ r => r = .Ok () ⦄ := by
  simp [code.check_table_byte]

theorem code.check_table_target.wasm2 (env : metadata.Env) (first ts : signature.ResultType) :
    code.check_table_target .Wasm2 env first ts = .ok (.Ok ()) := rfl

theorem code.check_table_target.complete (profile : ValidationProfile) (env : metadata.Env) (first ts : signature.ResultType) :
    code.check_table_target profile env first ts = .ok (.Ok ()) := rfl

@[step]
theorem code.check_table_target.spec (profile : ValidationProfile) (env : metadata.Env) (first ts : signature.ResultType) :
    code.check_table_target profile env first ts ⦃ r => r = .Ok () ⦄ := by
  simp [code.check_table_target]

end Itasca
