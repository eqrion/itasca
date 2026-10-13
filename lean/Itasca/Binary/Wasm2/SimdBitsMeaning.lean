import Itasca.Binary.Wasm2.Simd

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

theorem vectorConstant_typed (C : context) (low high : U64) (hC : wf_context C) :
    Instr_ok C (vectorConstant low high) (.mk_functype (.mk_list []) (.mk_list [.V128])) :=
  .vconst C _ hC (vectorConstant_wf low high)

theorem vectorConstant_principal (C : context) (low high : U64) (ins outs : List valtype)
    (ht : Instr_ok C (vectorConstant low high) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = [] ∧ outs = [.V128] := by cases ht; exact ⟨rfl, rfl⟩

theorem unpackBytes_payload (bytes : List U8) :
    unpackBytes (FloatBits.payload bytes) bytes.length = bytes.map UScalar.val := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
    have hb : b.val < 256 := by scalar_tac
    simp only [FloatBits.payload, List.length_cons, unpackBytes, List.map_cons]
    have hm : (b.val + 256 * FloatBits.payload bs) % 256 = b.val := by omega
    have hd : (b.val + 256 * FloatBits.payload bs) / 256 = FloatBits.payload bs := by omega
    rw [hm, hd, ih]

theorem shuffleIndices_encoding (low high : U64) (lower upper : List U8)
    (hl : FloatBits.Encoding 8 lower low.val) (hh : FloatBits.Encoding 8 upper high.val) :
    shuffleIndices low high = (lower ++ upper).map (fun b => uN.mk_uN b.val) := by
  have hlo : unpackBytes low.val 8 = lower.map UScalar.val := by
    rw [hl.2, ← hl.1, unpackBytes_payload]
  have hhi : unpackBytes high.val 8 = upper.map UScalar.val := by
    rw [hh.2, ← hh.1, unpackBytes_payload]
  simp [shuffleIndices, hlo, hhi, List.map_append, List.map_map, Function.comp_def]

theorem shuffle_typed (C : context) (low high : U64) (hC : wf_context C)
    (hl : ∀ lane ∈ shuffleIndices low high, proj_uN_0 lane < 32) :
    Instr_ok C (shuffle low high)
      (.mk_functype (.mk_list [.V128, .V128]) (.mk_list [.V128])) := by
  exact .vshuffle C _ _ (.mk_dim 16) (by constructor; constructor; decide)
    hl hC (by constructor; decide) (shuffle_wf low high)

theorem shuffle_principal (C : context) (low high : U64) (ins outs : List valtype)
    (ht : Instr_ok C (shuffle low high) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = [.V128, .V128] ∧ outs = [.V128] := by cases ht; exact ⟨rfl, rfl⟩

theorem shuffle_bound (C : context) (low high : U64) (ins outs : List valtype)
    (ht : Instr_ok C (shuffle low high) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ∀ lane ∈ shuffleIndices low high, proj_uN_0 lane < 32 := by
  cases ht
  cases_type fun_dim
  assumption

theorem vectorConstant_declared (refs : List funcidx) (low high : U64) :
    DeclaredReferences.Instruction refs (vectorConstant low high) := by
  simp [vectorConstant, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

theorem shuffle_declared (refs : List funcidx) (low high : U64) :
    DeclaredReferences.Instruction refs (shuffle low high) := by
  simp [shuffle, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

end Itasca.Wasm2.Simd
