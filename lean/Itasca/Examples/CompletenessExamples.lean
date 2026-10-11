import Itasca.Body.Wasm1Profile
import Itasca.Binary.WasmBinary
import Itasca.Body.BrTable
import Itasca.Body.EnvTranslation
import Itasca.Body.WasmComplete

open Aeneas Aeneas.Std

namespace Itasca.CompletenessExamples

def bytes (xs : List U8) (h : xs.length ≤ Usize.max := by scalar_tac) : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from xs h)

def i32Context : code.Context :=
  ⟨alloc.vec.Vec.new _, alloc.vec.Vec.from [.I32] (by scalar_tac)⟩

def nestedBytes : Slice U8 := bytes
  [0x02#u8, 0x7F#u8, 0x41#u8, 1#u8, 0x04#u8, 0x7F#u8,
   0x41#u8, 7#u8, 0x05#u8, 0x41#u8, 9#u8, 0x0B#u8, 0x0B#u8, 0x0B#u8]

def choice : instr := .IFELSE (Control.blockType (.Value .I32))
  [Core.i32Const 7#i32] [Core.i32Const 9#i32]
def nestedInner : List instr := [Core.i32Const 1#i32, choice]
def nestedOps : List instr := [.BLOCK (Control.blockType (.Value .I32)) nestedInner]

private theorem constant_encoded (b : U8) (v : I32)
    (hb : b.val < 64) (hv : v.val = b.val) : SignedLeb.Encoding [b] v.val := by
  refine ⟨[], b, rfl, by simp, by simp, by omega, ?_, ?_, ?_⟩
  · simp [SignedLeb.finalValue, Leb128.payload, Nat.not_le.mpr hb, hv]
  · have := v.hmin; norm_num at this ⊢; exact this
  · have := v.hmax; norm_num at this ⊢; omega

private theorem unsigned_encoded (b : U8) (h : b.val < 128) : Leb128.Encoding [b] b.val := by
  exact ⟨[], b, rfl, by simp, by simp, h, by simp, by simp [Leb128.payload, Nat.mod_eq_of_lt h]⟩

private theorem constant_typed (C : context) (hC : wf_context C) (v : I32) :
    Instrs_ok C [Core.i32Const v] (.mk_functype (.mk_list []) (.mk_list [.I32])) :=
  .instr C _ _ _ (Core.i32Const_typed C hC v) hC (Core.i32Const_wf v)

private theorem constant_profile (C : context) (v : I32) : Wasm1.Instructions C [Core.i32Const v] :=
  .cons (.leaf C _ (by trivial)) (.nil C)

private theorem choice_wf : wf_instr choice :=
  .instr_case_6 _ _ _ (Control.blockType_wf _)
    (by simpa [Forall] using Core.i32Const_wf 7#i32)
    (by simpa [Forall] using Core.i32Const_wf 9#i32)

private theorem nested_inner_wf : Forall wf_instr nestedInner := by
  simpa [nestedInner, Forall] using And.intro (Core.i32Const_wf 1#i32) choice_wf

private theorem nested_typed (env : module.Env) :
    Wasm.FunctionTyped env i32Context (.Value .I32) nestedOps := by
  let C := WasmFrames.enter (EnvTranslation.context env i32Context) .body (.Value .I32)
  let D := Control.labelContext [.I32] ++ C
  let E := Control.labelContext [.I32] ++ D
  have hC : wf_context C := WasmFrames.enter_wf _ (EnvTranslation.context_wf env i32Context) _ _
  have hD : wf_context D := Control.enter_context_wf C hC _
  have hE : wf_context E := Control.enter_context_wf D hD _
  have hchoice : Instr_ok D choice (.mk_functype (.mk_list [.I32]) (.mk_list [.I32])) :=
    .if D _ _ _ [] [.I32] (Control.blockType_ok D hD (.Value .I32))
      (constant_typed E hE 7#i32) (constant_typed E hE 9#i32) hD choice_wf
      (Control.labelContext_wf _)
  have hi : Instrs_ok D nestedInner (.mk_functype (.mk_list []) (.mk_list [.I32])) :=
    .seq D _ _ [] [.I32] [.I32] (constant_typed D hD 1#i32)
      (.instr D _ _ _ hchoice hD choice_wf) hD
      (by simpa [Forall] using Core.i32Const_wf 1#i32) (by simpa [Forall] using choice_wf)
  exact .instr C _ _ _ (Control.block_typed C hC (.Value .I32) nestedInner nested_inner_wf hi)
    hC (.instr_case_4 _ _ (Control.blockType_wf _) nested_inner_wf)

private theorem nested_encoded : Wasm.BodyEncoding nestedBytes nestedOps := by
  have h0 : Wasm.At nestedBytes 0#usize (.block (.Value .I32)) 2#usize :=
    ⟨[0x02#u8, 0x7F#u8], ⟨0x02#u8, [0x7F#u8], rfl, .block (.Value .I32) trivial⟩, ⟨rfl, rfl, by decide⟩⟩
  have h2 : Wasm.At nestedBytes 2#usize (.plain (Core.i32Const 1#i32)) 4#usize :=
    ⟨[0x41#u8, 1#u8], ⟨0x41#u8, [1#u8], rfl, .i32Const 1#i32 (constant_encoded _ _ (by decide) rfl)⟩,
      ⟨rfl, rfl, by decide⟩⟩
  have h4 : Wasm.At nestedBytes 4#usize (.if_ (.Value .I32)) 6#usize :=
    ⟨[0x04#u8, 0x7F#u8], ⟨0x04#u8, [0x7F#u8], rfl, .if_ (.Value .I32) trivial⟩, ⟨rfl, rfl, by decide⟩⟩
  have h6 : Wasm.At nestedBytes 6#usize (.plain (Core.i32Const 7#i32)) 8#usize :=
    ⟨[0x41#u8, 7#u8], ⟨0x41#u8, [7#u8], rfl, .i32Const 7#i32 (constant_encoded _ _ (by decide) rfl)⟩,
      ⟨rfl, rfl, by decide⟩⟩
  have h8 : Wasm.At nestedBytes 8#usize .else_ 9#usize :=
    ⟨[0x05#u8], ⟨0x05#u8, [], rfl, .else_⟩, ⟨rfl, rfl, by decide⟩⟩
  have h9 : Wasm.At nestedBytes 9#usize (.plain (Core.i32Const 9#i32)) 11#usize :=
    ⟨[0x41#u8, 9#u8], ⟨0x41#u8, [9#u8], rfl, .i32Const 9#i32 (constant_encoded _ _ (by decide) rfl)⟩,
      ⟨rfl, rfl, by decide⟩⟩
  have h11 : Wasm.At nestedBytes 11#usize .end_ 12#usize :=
    ⟨[0x0B#u8], ⟨0x0B#u8, [], rfl, .end_⟩, ⟨rfl, rfl, by decide⟩⟩
  have h12 : Wasm.At nestedBytes 12#usize .end_ 13#usize :=
    ⟨[0x0B#u8], ⟨0x0B#u8, [], rfl, .end_⟩, ⟨rfl, rfl, by decide⟩⟩
  have h13 : Wasm.At nestedBytes 13#usize .end_ 14#usize :=
    ⟨[0x0B#u8], ⟨0x0B#u8, [], rfl, .end_⟩, ⟨rfl, rfl, by decide⟩⟩
  have hi := Wasm.Emits.ifElse (.Value .I32)
    (Wasm.Emits.simple .nil (.plain _ (Core.i32Const_wf 1#i32)))
    (Wasm.Emits.simple .nil (.plain _ (Core.i32Const_wf 7#i32)))
    (Wasm.Emits.simple .nil (.plain _ (Core.i32Const_wf 9#i32)))
  have ho := Wasm.Emits.block (.Value .I32) .nil hi
  refine ⟨_, 14#usize,
    ((((((((Wasm.Consumed.nil 0#usize (by decide)).snoc h0).snoc h2).snoc h4).snoc h6).snoc h8).snoc h9).snoc h11).snoc h12 |>.snoc h13,
    rfl, ?_⟩
  exact ⟨_, rfl, ho⟩

/-- This premise is constructed solely from byte grammar, generated typing, and the independent profile. -/
theorem nested_body (env : module.Env) : Wasm1.Body nestedBytes env i32Context (.Value .I32) := by
  refine ⟨nestedOps, nested_encoded, nested_typed env, ?_⟩
  apply Wasm1.Instructions.cons
  · apply Wasm1.Instruction.block
    apply Wasm1.Instructions.cons
    · exact .leaf _ _ (by trivial)
    · apply Wasm1.Instructions.cons
      · exact .ifElse _ _ _ _ (constant_profile _ _) (constant_profile _ _)
      · exact .nil _
  · exact .nil _

def tableBytes : Slice U8 := bytes
  [0x02#u8, 0x7F#u8, 0x00#u8, 0x0E#u8, 1#u8, 0#u8, 1#u8, 0x0B#u8, 0x0B#u8]
def table : instr := BrTable.instruction [0#u32] 1#u32
def tableInner : List instr := [.UNREACHABLE, table]
def tableOps : List instr := [.BLOCK (Control.blockType (.Value .I32)) tableInner]

private theorem table_wf : wf_instr table := BrTable.instruction_wf _ _
private theorem table_inner_wf : Forall wf_instr tableInner := by
  simpa [tableInner, Forall] using And.intro wf_instr.instr_case_1 table_wf

private theorem table_typed (C : context) (hC : wf_context C)
    (hlabels : C.LABELS = [.mk_list [.I32], .mk_list [.I32]]) :
    Instr_ok C table (.mk_functype (.mk_list [.BOT, .I32]) (.mk_list [.I32])) := by
  have hsub : Resulttype_sub (.mk_list [.BOT]) (.mk_list [.I32]) :=
    .mk_Resulttype_sub _ _ rfl (by simpa [Forall₂] using Valtype_sub.bot .I32)
  apply Instr_ok.br_table C [.mk_uN 0] (.mk_uN 1) [] [.BOT] [.I32]
  · simp [Forall, hlabels, proj_uN_0]
  · simpa [Forall, hlabels, proj_uN_0] using hsub
  · simp [hlabels, proj_uN_0]
  · simpa [hlabels, proj_uN_0] using hsub
  · exact hC
  · exact table_wf

private theorem table_body_typed (env : module.Env) :
    Wasm.FunctionTyped env i32Context (.Value .I32) tableOps := by
  let C := WasmFrames.enter (EnvTranslation.context env i32Context) .body (.Value .I32)
  let D := Control.labelContext [.I32] ++ C
  have hC : wf_context C := WasmFrames.enter_wf _ (EnvTranslation.context_wf env i32Context) _ _
  have hD : wf_context D := Control.enter_context_wf C hC _
  have hi : Instrs_ok D tableInner (.mk_functype (.mk_list []) (.mk_list [.I32])) :=
    .seq D [.UNREACHABLE] [table] [] [.I32] [.BOT, .I32]
      (.instr D _ _ _ (.unreachable D [] [.BOT, .I32] hD .instr_case_1) hD .instr_case_1)
      (.instr D _ _ _ (table_typed D hD rfl) hD table_wf) hD
      (by simp [Forall, wf_instr.instr_case_1]) (by simpa [Forall] using table_wf)
  exact .instr C _ _ _ (Control.block_typed C hC (.Value .I32) tableInner table_inner_wf hi)
    hC (.instr_case_4 _ _ (Control.blockType_wf _) table_inner_wf)

private theorem table_encoded : Wasm.BodyEncoding tableBytes tableOps := by
  have h0 : Wasm.At tableBytes 0#usize (.block (.Value .I32)) 2#usize :=
    ⟨[0x02#u8, 0x7F#u8], ⟨0x02#u8, [0x7F#u8], rfl, .block (.Value .I32) trivial⟩, ⟨rfl, rfl, by decide⟩⟩
  have h2 : Wasm.At tableBytes 2#usize (.plain .UNREACHABLE) 3#usize :=
    ⟨[0#u8], ⟨0#u8, [], rfl, .unreachable⟩, ⟨rfl, rfl, by decide⟩⟩
  have h3 : Wasm.At tableBytes 3#usize (.plain table) 7#usize :=
    ⟨[0x0E#u8, 1#u8, 0#u8, 1#u8], ⟨0x0E#u8, [1#u8, 0#u8, 1#u8], rfl,
      .brTable [0#u32] 1#u32 (unsigned_encoded 1#u8 (by decide))
        (.cons (unsigned_encoded 0#u8 (by decide)) .nil) (unsigned_encoded 1#u8 (by decide))⟩,
      ⟨rfl, rfl, by decide⟩⟩
  have h7 : Wasm.At tableBytes 7#usize .end_ 8#usize :=
    ⟨[0x0B#u8], ⟨0x0B#u8, [], rfl, .end_⟩, ⟨rfl, rfl, by decide⟩⟩
  have h8 : Wasm.At tableBytes 8#usize .end_ 9#usize :=
    ⟨[0x0B#u8], ⟨0x0B#u8, [], rfl, .end_⟩, ⟨rfl, rfl, by decide⟩⟩
  have hi := Wasm.Emits.simple (Wasm.Emits.simple .nil (.plain _ .instr_case_1))
    (.plain table table_wf)
  have ho := Wasm.Emits.block (.Value .I32) .nil hi
  exact ⟨_, 9#usize, ((((Wasm.Consumed.nil 0#usize (by decide)).snoc h0).snoc h2).snoc h3).snoc h7 |>.snoc h8,
    rfl, ⟨_, rfl, ho⟩⟩

/-- A bottom-typed payload branches to distinct labels with the same nonempty signature. -/
theorem table_body (env : module.Env) : Wasm1.Body tableBytes env i32Context (.Value .I32) := by
  refine ⟨tableOps, table_encoded, table_body_typed env, ?_⟩
  apply Wasm1.Instructions.cons
  · apply Wasm1.Instruction.block
    apply Wasm1.Instructions.cons
    · exact .leaf _ _ (by trivial)
    · apply Wasm1.Instructions.cons
      · apply Wasm1.Instruction.leaf
        simp [Wasm1.Leaf, Wasm1.SameTargets, table, BrTable.instruction, proj_uN_0,
          WasmFrames.enter, WasmFrames.Form.label, EnvTranslation.context,
          Control.resultTypes, Control.results, Translate.valueType]
      · exact .nil _
  · exact .nil _

def callMemoryBytes : Slice U8 := bytes [0x3F#u8, 0#u8, 0x10#u8, 0#u8, 0x0B#u8]
def callMemoryOps : List instr := [.MEMORY_SIZE, .CALL (.mk_uN 0)]
def scalarFunction : types.FuncType :=
  ⟨alloc.vec.Vec.from [.I32] (by scalar_tac), alloc.vec.Vec.from [.I32] (by scalar_tac)⟩

def exampleEnv : module.Env where
  types := alloc.vec.Vec.from [scalarFunction] (by scalar_tac)
  imports := alloc.vec.Vec.new _
  globals := alloc.vec.Vec.new _
  exports := alloc.vec.Vec.new _
  elements := alloc.vec.Vec.new _
  start := none
  data_count := none
  declared_funcs := alloc.vec.Vec.new _
  func_type_indices := alloc.vec.Vec.from [0#u32] (by scalar_tac)
  func_types := alloc.vec.Vec.from [scalarFunction] (by scalar_tac)
  table_types := alloc.vec.Vec.new _
  mem_types := alloc.vec.Vec.from [⟨⟨1#u32, none⟩⟩] (by scalar_tac)
  global_types := alloc.vec.Vec.new _
  num_imported_funcs := 0#usize
  num_imported_globals := 0#usize

theorem example_environment : Wasm1.Environment exampleEnv := by
  constructor <;> simp [exampleEnv, scalarFunction]

private theorem call_memory_typed :
    Wasm.FunctionTyped exampleEnv i32Context (.Value .I32) callMemoryOps := by
  let C := WasmFrames.enter (EnvTranslation.context exampleEnv i32Context) .body (.Value .I32)
  have hm : EnvTranslation.Matches exampleEnv i32Context C :=
    (EnvTranslation.Matches.root exampleEnv i32Context).enter _
  have hmemory : Instr_ok C .MEMORY_SIZE (.mk_functype (.mk_list []) (.mk_list [.I32])) :=
    hm.memory_size (by simp [exampleEnv])
  have hcall : Instr_ok C (.CALL (.mk_uN 0)) (.mk_functype (.mk_list [.I32]) (.mk_list [.I32])) :=
    hm.call 0#u32 scalarFunction (by simp [exampleEnv]) rfl
  exact .seq C [.MEMORY_SIZE] [.CALL (.mk_uN 0)] [] [.I32] [.I32]
    (.instr C _ _ _ hmemory hm.wf .instr_case_62)
    (.instr C _ _ _ hcall hm.wf (.instr_case_10 _ (EnvTranslation.index_wf 0#u32))) hm.wf
    (by simp [Forall, wf_instr.instr_case_62])
    (by simpa [Forall] using wf_instr.instr_case_10 (.mk_uN 0) (EnvTranslation.index_wf 0#u32))

private theorem call_memory_encoded : Wasm.BodyEncoding callMemoryBytes callMemoryOps := by
  have h0 : Wasm.At callMemoryBytes 0#usize (.plain .MEMORY_SIZE) 2#usize :=
    ⟨[0x3F#u8, 0#u8], ⟨0x3F#u8, [0#u8], rfl, .memorySize⟩, ⟨rfl, rfl, by decide⟩⟩
  have h2 : Wasm.At callMemoryBytes 2#usize (.plain (.CALL (.mk_uN 0))) 4#usize :=
    ⟨[0x10#u8, 0#u8], ⟨0x10#u8, [0#u8], rfl, .call 0#u32 (unsigned_encoded 0#u8 (by decide))⟩,
      ⟨rfl, rfl, by decide⟩⟩
  have h4 : Wasm.At callMemoryBytes 4#usize .end_ 5#usize :=
    ⟨[0x0B#u8], ⟨0x0B#u8, [], rfl, .end_⟩, ⟨rfl, rfl, by decide⟩⟩
  have ho := Wasm.Emits.simple (Wasm.Emits.simple .nil (.plain _ .instr_case_62))
    (.plain _ (.instr_case_10 _ (EnvTranslation.index_wf 0#u32)))
  exact ⟨_, 5#usize, ((Wasm.Consumed.nil 0#usize (by decide)).snoc h0).snoc h2 |>.snoc h4,
    rfl, ⟨_, rfl, ho⟩⟩

/-- Memory size supplies the argument of a directly called scalar signature. -/
theorem call_memory_body : Wasm1.Body callMemoryBytes exampleEnv i32Context (.Value .I32) := by
  refine ⟨callMemoryOps, call_memory_encoded, call_memory_typed, ?_⟩
  exact .cons (.leaf _ _ (by trivial)) (.cons (.leaf _ _ (by trivial)) (.nil _))

/-- Public acceptance follows from independent nested control-flow premises. -/
theorem nested_accepted (env : module.Env) (henv : Wasm1.Environment env) :
    code.validate_body nestedBytes env i32Context = .ok (.Ok ()) :=
  code.validate_body.wasm_complete nestedBytes env i32Context (.Value .I32) henv rfl
    (by simp [nestedBytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
    (nested_body env)

/-- Completeness includes unreachable branch-table arguments and nonempty results. -/
theorem table_accepted (env : module.Env) (henv : Wasm1.Environment env) :
    code.validate_body tableBytes env i32Context = .ok (.Ok ()) :=
  code.validate_body.wasm_complete tableBytes env i32Context (.Value .I32) henv rfl
    (by simp [tableBytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
    (table_body env)

/-- A concrete call/memory environment meets all public completeness premises. -/
theorem call_memory_accepted :
    code.validate_body callMemoryBytes exampleEnv i32Context = .ok (.Ok ()) :=
  code.validate_body.wasm_complete callMemoryBytes exampleEnv i32Context (.Value .I32)
    example_environment rfl
    (by simp [callMemoryBytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
    call_memory_body

end Itasca.CompletenessExamples
