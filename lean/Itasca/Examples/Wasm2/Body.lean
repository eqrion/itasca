import Itasca.Wasm2.Completeness
import Itasca.Wasm2.Complete.Frame
import Itasca.Examples.Wasm2.Grammar

open Aeneas Aeneas.Std

namespace Itasca.MultiValueBody

open MultiValue

def bytes (xs : List U8) (h : xs.length ≤ Usize.max := by scalar_tac) : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from xs h)

def locals : alloc.vec.Vec types.ValueType := alloc.vec.Vec.new _
def pairResult : types.FuncType :=
  ⟨alloc.vec.Vec.new _, alloc.vec.Vec.from [.I32, .I64] (by scalar_tac)⟩
def pairIdentity : types.FuncType :=
  ⟨alloc.vec.Vec.from [.I32, .I64] (by scalar_tac), alloc.vec.Vec.from [.I32, .I64] (by scalar_tac)⟩
def pairLoop : types.FuncType :=
  ⟨alloc.vec.Vec.from [.I32, .I64] (by scalar_tac), alloc.vec.Vec.new _⟩
def emptyResult : types.FuncType := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _⟩
def floatResult : types.FuncType :=
  ⟨alloc.vec.Vec.new _, alloc.vec.Vec.from [.F32, .F64] (by scalar_tac)⟩

def env : module.Env where
  types := alloc.vec.Vec.from [pairResult, pairIdentity, pairLoop, emptyResult, floatResult] (by scalar_tac)
  imports := alloc.vec.Vec.new _
  globals := alloc.vec.Vec.new _
  exports := alloc.vec.Vec.new _
  elements := alloc.vec.Vec.new _
  start := none
  data_count := none
  declared_funcs := alloc.vec.Vec.new _
  func_type_indices := alloc.vec.Vec.new _
  func_types := alloc.vec.Vec.new _
  table_types := alloc.vec.Vec.new _
  mem_types := alloc.vec.Vec.new _
  global_types := alloc.vec.Vec.new _
  num_imported_funcs := 0#usize
  num_imported_globals := 0#usize

theorem environment_limits : EnvironmentWithinLimits env := by
  constructor
  · intro ft hf
    simp [env] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;>
      simp [pairResult, pairIdentity, pairLoop, emptyResult, floatResult]
  · simp [env]

private theorem unsigned (b : U8) (h : b.val < 128) : Leb128.Encoding [b] b.val :=
  ⟨[], b, rfl, by simp, by simp, h, by simp, by simp [Leb128.payload, Nat.mod_eq_of_lt h]⟩

private theorem index_encoding (b : U8) (idx : U32) (hb : b.val < 64) (hi : idx.val = b.val) :
    BlockEncoding (.TypeIndex idx) [b] := by
  refine ⟨[], b, rfl, by simp, by simp, by omega, ?_, ?_, ?_⟩
  · simp [SignedLeb33.finalValue, Leb128.payload, Nat.not_le.mpr hb, hi]
  · omega
  · have := idx.hmax; scalar_tac

private theorem zero32 : SignedLeb.Encoding [0#u8] (0#i32).val := by
  refine ⟨[], 0#u8, rfl, by decide, by simp, by decide, ?_, by decide, by decide⟩
  norm_num [SignedLeb.finalValue, Leb128.payload]

private theorem zero64 : SignedLeb64.Encoding [0#u8] (0#i64).val := by
  refine ⟨[], 0#u8, rfl, by decide, by simp, by decide, ?_, by decide, by decide⟩
  norm_num [SignedLeb64.finalValue, Leb128.payload]

def pairOps : List instr := [Core.i32Const 0#i32, ScalarConst.i64 0#i64]

private theorem pair_wf : Forall wf_instr pairOps := by
  simpa [pairOps, Forall] using And.intro (Core.i32Const_wf 0#i32) (ScalarConst.i64_wf 0#i64)

private theorem pair_typed (C : context) (hC : wf_context C) :
    Instrs_ok C pairOps (.mk_functype (.mk_list []) (.mk_list [.I32, .I64])) := by
  have hp := ((TypedPrefix.start C hC []).i32Const hC 0#i32).i64Const hC 0#i64
  simpa [pairOps, Sequence.stackTypes, Translate.valueType] using hp.typed _
    (Sequence.realizes_default false [.Val .I32, .Val .I64])

private theorem identity_typed (C : context) (hC : wf_context C) (ts : List valtype) :
    Instrs_ok C [] (.mk_functype (.mk_list ts) (.mk_list ts)) := by
  simpa using Instrs_ok.frame C [] ts [] [] (.empty C hC) hC (by simp [Forall])

private def rootContext (ft : types.FuncType) : context :=
  Control.labelContext (ft.results.val.map Translate.valueType) ++ bodyContext env locals ft

private theorem root_wf (ft : types.FuncType) : wf_context (rootContext ft) :=
  Control.enter_context_wf _ (EnvTranslation.context_wf env ⟨locals, ft.results⟩) _

def identityBlock : instr := .BLOCK (blockType (.TypeIndex 1#u32)) []
def blockOps : List instr := pairOps ++ [identityBlock]
def blockBytes : Slice U8 := bytes [0x41#u8, 0#u8, 0x42#u8, 0#u8, 0x02#u8, 1#u8, 0x0B#u8, 0x0B#u8]

private theorem block_wf : wf_instr identityBlock :=
  .instr_case_4 _ _ (blockType_wf _) (by simp [Forall])

/-- Indexed blocks consume and return both ordered parameters. -/
theorem block_typed : FunctionTyped env locals pairResult blockOps := by
  let C := rootContext pairResult
  have hC := root_wf pairResult
  have hbt := blockType_ok env C hC rfl (.TypeIndex 1#u32) [.I32, .I64] [.I32, .I64] rfl rfl
  have hi : Instr_ok C identityBlock (.mk_functype (.mk_list [.I32, .I64]) (.mk_list [.I32, .I64])) :=
    .block C _ [] _ _ hbt (identity_typed _ (Control.enter_context_wf C hC _) _)
      hC block_wf (Control.labelContext_wf _)
  exact .seq C pairOps [identityBlock] [] [.I32, .I64] [.I32, .I64] (pair_typed C hC)
    (.instr C _ _ _ hi hC block_wf) hC pair_wf (by simpa [Forall] using block_wf)

def identityIf : instr := .IFELSE (blockType (.TypeIndex 1#u32)) [] []
def ifOps : List instr := pairOps ++ [Core.i32Const 0#i32, identityIf]
def ifBytes : Slice U8 := bytes
  [0x41#u8, 0#u8, 0x42#u8, 0#u8, 0x41#u8, 0#u8, 0x04#u8, 1#u8, 0x0B#u8, 0x0B#u8]

/-- A missing else arm preserves both parameters because its signature is identity. -/
theorem if_typed : FunctionTyped env locals pairResult ifOps := by
  let C := rootContext pairResult
  have hC := root_wf pairResult
  have hp := (((TypedPrefix.start C hC []).i32Const hC 0#i32).i64Const hC 0#i64).i32Const hC 0#i32
  have hprefix : Instrs_ok C (pairOps ++ [Core.i32Const 0#i32])
      (.mk_functype (.mk_list []) (.mk_list [.I32, .I64, .I32])) := by
    simpa [pairOps, Sequence.stackTypes, Translate.valueType] using hp.typed _
      (Sequence.realizes_default false [.Val .I32, .Val .I64, .Val .I32])
  have hwf : wf_instr identityIf :=
    .instr_case_6 _ _ _ (blockType_wf _) (by simp [Forall]) (by simp [Forall])
  have hi := MultiValueGrammar.identity_if env C hC rfl 1#u32 rfl rfl
  change Instrs_ok C ifOps (.mk_functype (.mk_list []) (.mk_list [.I32, .I64]))
  simpa [ifOps, pairOps, List.append_assoc] using
    Instrs_ok.seq C (pairOps ++ [Core.i32Const 0#i32]) [identityIf] [] [.I32, .I64] [.I32, .I64, .I32]
      hprefix (.instr C _ _ _ hi hC hwf) hC hp.wellFormed (by simpa [Forall] using hwf)

def loopInstr : instr := .LOOP (blockType (.TypeIndex 2#u32)) [.BR (.mk_uN 0)]
def loopOps : List instr := pairOps ++ [loopInstr]
def loopBytes : Slice U8 := bytes
  [0x41#u8, 0#u8, 0x42#u8, 0#u8, 0x03#u8, 2#u8, 0x0C#u8, 0#u8, 0x0B#u8, 0x0B#u8]

/-- A loop branch uses its two input types even though the loop has no results. -/
theorem loop_typed : FunctionTyped env locals emptyResult loopOps := by
  let C := rootContext emptyResult
  let D := Control.labelContext [.I32, .I64] ++ C
  have hC := root_wf emptyResult
  have hD : wf_context D := Control.enter_context_wf C hC _
  have hbr : wf_instr (.BR (.mk_uN 0)) := .instr_case_7 _ (EnvTranslation.index_wf 0#u32)
  have hi : Instr_ok D (.BR (.mk_uN 0)) (.mk_functype (.mk_list [.I32, .I64]) (.mk_list [])) :=
    .br D (.mk_uN 0) [] [.I32, .I64] [] (by simp [D, Control.labelContext_labels, proj_uN_0])
      rfl hD hbr
  have hwf : wf_instr loopInstr := .instr_case_5 _ _ (blockType_wf _) (by simpa [Forall] using hbr)
  have hloop : Instr_ok C loopInstr (.mk_functype (.mk_list [.I32, .I64]) (.mk_list [])) :=
    .loop C _ _ _ _ (blockType_ok env C hC rfl (.TypeIndex 2#u32) [.I32, .I64] [] rfl rfl)
      (.instr D _ _ _ hi hD hbr) hC hwf (Control.labelContext_wf _)
  exact .seq C pairOps [loopInstr] [] [] [.I32, .I64] (pair_typed C hC)
    (.instr C _ _ _ hloop hC hwf) hC pair_wf (by simpa [Forall] using hwf)


private theorem pair_emits : Emits [.plain (Core.i32Const 0#i32), .plain (ScalarConst.i64 0#i64)] pairOps :=
  .simple (.simple .nil (.plain _ (Core.i32Const_wf 0#i32))) (.plain _ (ScalarConst.i64_wf 0#i64))

theorem block_encoded : BodyEncoding blockBytes blockOps := by
  have h0 : At blockBytes 0#usize (.plain (Core.i32Const 0#i32)) 2#usize :=
    ⟨_, ⟨0x41#u8, [0#u8], rfl, .plain (.i32Const 0#i32 zero32)⟩, rfl, rfl, by decide⟩
  have h2 : At blockBytes 2#usize (.plain (ScalarConst.i64 0#i64)) 4#usize :=
    ⟨_, ⟨0x42#u8, [0#u8], rfl, .plain (.i64Const 0#i64 zero64)⟩, rfl, rfl, by decide⟩
  have h4 : At blockBytes 4#usize (.block (.TypeIndex 1#u32)) 6#usize :=
    ⟨_, ⟨0x02#u8, [1#u8], rfl, .block (index_encoding 1#u8 1#u32 (by decide) rfl)⟩, rfl, rfl, by decide⟩
  have h6 : At blockBytes 6#usize (.end_) 7#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  have h7 : At blockBytes 7#usize (.end_) 8#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  exact ⟨_, 8#usize, ((((((Consumed.nil 0#usize (by decide)).snoc h0).snoc h2).snoc h4).snoc h6).snoc h7), rfl, _, rfl, Emits.block (.TypeIndex 1#u32) pair_emits .nil⟩

theorem if_encoded : BodyEncoding ifBytes ifOps := by
  have h0 : At ifBytes 0#usize (.plain (Core.i32Const 0#i32)) 2#usize :=
    ⟨_, ⟨0x41#u8, [0#u8], rfl, .plain (.i32Const 0#i32 zero32)⟩, rfl, rfl, by decide⟩
  have h2 : At ifBytes 2#usize (.plain (ScalarConst.i64 0#i64)) 4#usize :=
    ⟨_, ⟨0x42#u8, [0#u8], rfl, .plain (.i64Const 0#i64 zero64)⟩, rfl, rfl, by decide⟩
  have h4 : At ifBytes 4#usize (.plain (Core.i32Const 0#i32)) 6#usize :=
    ⟨_, ⟨0x41#u8, [0#u8], rfl, .plain (.i32Const 0#i32 zero32)⟩, rfl, rfl, by decide⟩
  have h6 : At ifBytes 6#usize (.if_ (.TypeIndex 1#u32)) 8#usize :=
    ⟨_, ⟨0x04#u8, [1#u8], rfl, .if_ (index_encoding 1#u8 1#u32 (by decide) rfl)⟩, rfl, rfl, by decide⟩
  have h8 : At ifBytes 8#usize (.end_) 9#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  have h9 : At ifBytes 9#usize (.end_) 10#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  exact ⟨_, 10#usize, (((((((Consumed.nil 0#usize (by decide)).snoc h0).snoc h2).snoc h4).snoc h6).snoc h8).snoc h9), rfl, _, rfl, Emits.ifEnd (.TypeIndex 1#u32) (Emits.simple pair_emits (.plain _ (Core.i32Const_wf 0#i32))) .nil⟩

theorem loop_encoded : BodyEncoding loopBytes loopOps := by
  have h0 : At loopBytes 0#usize (.plain (Core.i32Const 0#i32)) 2#usize :=
    ⟨_, ⟨0x41#u8, [0#u8], rfl, .plain (.i32Const 0#i32 zero32)⟩, rfl, rfl, by decide⟩
  have h2 : At loopBytes 2#usize (.plain (ScalarConst.i64 0#i64)) 4#usize :=
    ⟨_, ⟨0x42#u8, [0#u8], rfl, .plain (.i64Const 0#i64 zero64)⟩, rfl, rfl, by decide⟩
  have h4 : At loopBytes 4#usize (.loop (.TypeIndex 2#u32)) 6#usize :=
    ⟨_, ⟨0x03#u8, [2#u8], rfl, .loop (index_encoding 2#u8 2#u32 (by decide) rfl)⟩, rfl, rfl, by decide⟩
  have h6 : At loopBytes 6#usize (.plain (.BR (.mk_uN 0))) 8#usize :=
    ⟨_, ⟨0x0C#u8, [0#u8], rfl, .plain (.br 0#u32 (unsigned 0#u8 (by decide)))⟩, rfl, rfl, by decide⟩
  have h8 : At loopBytes 8#usize (.end_) 9#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  have h9 : At loopBytes 9#usize (.end_) 10#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  exact ⟨_, 10#usize, (((((((Consumed.nil 0#usize (by decide)).snoc h0).snoc h2).snoc h4).snoc h6).snoc h8).snoc h9), rfl, _, rfl, Emits.loop (.TypeIndex 2#u32) pair_emits (Emits.simple .nil (.plain _ (.instr_case_7 _ (EnvTranslation.index_wf 0#u32))))⟩


def heterogeneousTable : instr := BrTable.instruction [0#u32] 1#u32
def tableInner : List instr := [.UNREACHABLE, heterogeneousTable]
def tableBlock : instr := .BLOCK (blockType (.TypeIndex 4#u32)) tableInner
def tableOps : List instr := [tableBlock, .UNREACHABLE]
def tableBytes : Slice U8 := bytes
  [0x02#u8, 4#u8, 0#u8, 0x0E#u8, 1#u8, 0#u8, 1#u8, 0x0B#u8, 0#u8, 0x0B#u8]

private theorem table_wf : wf_instr heterogeneousTable := BrTable.instruction_wf _ _
private theorem table_inner_wf : Forall wf_instr tableInner := by
  simpa [tableInner, Forall] using And.intro wf_instr.instr_case_1 table_wf

/-- Two bottom operands are a common subtype of differently typed, equally
sized table targets. This is permitted by the generated Wasm 2.0 rule. -/
theorem table_typed : FunctionTyped env locals pairResult tableOps := by
  let C := rootContext pairResult
  let D := Control.labelContext [.F32, .F64] ++ C
  have hC := root_wf pairResult
  have hD : wf_context D := Control.enter_context_wf C hC _
  have hlabels : D.LABELS = [.mk_list [.F32, .F64], .mk_list [.I32, .I64]] := rfl
  have hfloat : Resulttype_sub (.mk_list [.BOT, .BOT]) (.mk_list [.F32, .F64]) :=
    .mk_Resulttype_sub _ _ rfl (by simp [Forall₂, Valtype_sub.bot])
  have hint : Resulttype_sub (.mk_list [.BOT, .BOT]) (.mk_list [.I32, .I64]) :=
    .mk_Resulttype_sub _ _ rfl (by simp [Forall₂, Valtype_sub.bot])
  have ht : Instr_ok D heterogeneousTable
      (.mk_functype (.mk_list [.BOT, .BOT, .I32]) (.mk_list [.F32, .F64])) := by
    apply Instr_ok.br_table D [.mk_uN 0] (.mk_uN 1) [] [.BOT, .BOT] [.F32, .F64]
    · simp [Forall, hlabels, proj_uN_0]
    · simpa [Forall, hlabels, proj_uN_0] using hfloat
    · simp [hlabels, proj_uN_0]
    · simpa [hlabels, proj_uN_0] using hint
    · exact hD
    · exact table_wf
  have hi : Instrs_ok D tableInner (.mk_functype (.mk_list []) (.mk_list [.F32, .F64])) :=
    .seq D [.UNREACHABLE] [heterogeneousTable] [] [.F32, .F64] [.BOT, .BOT, .I32]
      (.instr D _ _ _ (.unreachable D _ _ hD .instr_case_1) hD .instr_case_1)
      (.instr D _ _ _ ht hD table_wf) hD
      (by simp [Forall, wf_instr.instr_case_1]) (by simpa [Forall] using table_wf)
  have hwf : wf_instr tableBlock := .instr_case_4 _ _ (blockType_wf _) table_inner_wf
  have hb : Instr_ok C tableBlock (.mk_functype (.mk_list []) (.mk_list [.F32, .F64])) :=
    .block C _ _ _ _ (blockType_ok env C hC rfl (.TypeIndex 4#u32) [] [.F32, .F64] rfl rfl)
      hi hC hwf (Control.labelContext_wf _)
  exact .seq C [tableBlock] [.UNREACHABLE] [] [.I32, .I64] [.F32, .F64]
    (.instr C _ _ _ hb hC hwf)
    (.instr C _ _ _ (.unreachable C _ _ hC .instr_case_1) hC .instr_case_1)
    hC (by simpa [Forall] using hwf) (by simp [Forall, wf_instr.instr_case_1])

theorem table_encoded : BodyEncoding tableBytes tableOps := by
  have h0 : At tableBytes 0#usize (.block (.TypeIndex 4#u32)) 2#usize :=
    ⟨_, ⟨0x02#u8, [4#u8], rfl, .block (index_encoding 4#u8 4#u32 (by decide) rfl)⟩, rfl, rfl, by decide⟩
  have h2 : At tableBytes 2#usize (.plain .UNREACHABLE) 3#usize :=
    ⟨_, ⟨0#u8, [], rfl, .plain .unreachable⟩, rfl, rfl, by decide⟩
  have h3 : At tableBytes 3#usize (.plain heterogeneousTable) 7#usize :=
    ⟨_, ⟨0x0E#u8, [1#u8, 0#u8, 1#u8], rfl,
      .plain (.brTable [0#u32] 1#u32 (unsigned 1#u8 (by decide))
        (.cons (unsigned 0#u8 (by decide)) .nil) (unsigned 1#u8 (by decide)))⟩, rfl, rfl, by decide⟩
  have h7 : At tableBytes 7#usize .end_ 8#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  have h8 : At tableBytes 8#usize (.plain .UNREACHABLE) 9#usize :=
    ⟨_, ⟨0#u8, [], rfl, .plain .unreachable⟩, rfl, rfl, by decide⟩
  have h9 : At tableBytes 9#usize .end_ 10#usize :=
    ⟨_, ⟨0x0B#u8, [], rfl, .end_⟩, rfl, rfl, by decide⟩
  have hi := Emits.simple (Emits.simple .nil (.plain _ .instr_case_1)) (.plain _ table_wf)
  have ho := Emits.simple (Emits.block (.TypeIndex 4#u32) .nil hi) (.plain _ .instr_case_1)
  exact ⟨_, 10#usize, ((((((Consumed.nil 0#usize (by decide)).snoc h0).snoc h2).snoc h3).snoc h7).snoc h8).snoc h9,
    rfl, _, rfl, ho⟩

/-- Public acceptance comes from independent syntax and generated typing,
without evaluating or assuming any handler succeeds. -/
theorem block_accepted : code.validate_multi_value_body blockBytes env locals 0#u32 = .ok (.Ok ()) :=
  code.validate_multi_value_body.wasm_complete_of_typing blockBytes env locals 0#u32 pairResult blockOps
    environment_limits (by simp [blockBytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
    rfl block_encoded block_typed (by simp [blockOps, DeclaredReferences.Instructions, DeclaredReferences.instructionsIndices, DeclaredReferences.instructionIndices, pairOps, identityBlock, identityIf, loopInstr, tableBlock, tableInner, heterogeneousTable, Core.i32Const, ScalarConst.i64, BrTable.instruction])

theorem if_accepted : code.validate_multi_value_body ifBytes env locals 0#u32 = .ok (.Ok ()) :=
  code.validate_multi_value_body.wasm_complete_of_typing ifBytes env locals 0#u32 pairResult ifOps
    environment_limits (by simp [ifBytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
    rfl if_encoded if_typed (by simp [ifOps, DeclaredReferences.Instructions, DeclaredReferences.instructionsIndices, DeclaredReferences.instructionIndices, pairOps, identityBlock, identityIf, loopInstr, tableBlock, tableInner, heterogeneousTable, Core.i32Const, ScalarConst.i64, BrTable.instruction])

theorem loop_accepted : code.validate_multi_value_body loopBytes env locals 3#u32 = .ok (.Ok ()) :=
  code.validate_multi_value_body.wasm_complete_of_typing loopBytes env locals 3#u32 emptyResult loopOps
    environment_limits (by simp [loopBytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
    rfl loop_encoded loop_typed (by simp [loopOps, DeclaredReferences.Instructions, DeclaredReferences.instructionsIndices, DeclaredReferences.instructionIndices, pairOps, identityBlock, identityIf, loopInstr, tableBlock, tableInner, heterogeneousTable, Core.i32Const, ScalarConst.i64, BrTable.instruction])

theorem table_accepted : code.validate_multi_value_body tableBytes env locals 0#u32 = .ok (.Ok ()) :=
  code.validate_multi_value_body.wasm_complete_of_typing tableBytes env locals 0#u32 pairResult tableOps
    environment_limits (by simp [tableBytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
    rfl table_encoded table_typed (by simp [tableOps, DeclaredReferences.Instructions, DeclaredReferences.instructionsIndices, DeclaredReferences.instructionIndices, pairOps, identityBlock, identityIf, loopInstr, tableBlock, tableInner, heterogeneousTable, Core.i32Const, ScalarConst.i64, BrTable.instruction])

/-- The same actual accepted runs produce independent soundness certificates. -/
theorem block_validated : Validated blockBytes env locals 0#u32 :=
  code.validate_multi_value_body.wasm_sound blockBytes env locals 0#u32 block_accepted

theorem if_validated : Validated ifBytes env locals 0#u32 :=
  code.validate_multi_value_body.wasm_sound ifBytes env locals 0#u32 if_accepted

theorem loop_validated : Validated loopBytes env locals 3#u32 :=
  code.validate_multi_value_body.wasm_sound loopBytes env locals 3#u32 loop_accepted

theorem table_validated : Validated tableBytes env locals 0#u32 :=
  code.validate_multi_value_body.wasm_sound tableBytes env locals 0#u32 table_accepted

end Itasca.MultiValueBody
