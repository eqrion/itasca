import Itasca.Examples.Module.Basic
import Itasca.Module.Completeness

open Aeneas Aeneas.Std

namespace Itasca.ModuleImportedGlobalExamples

open ModuleBinary ModuleEnv

private theorem leb (b : U8) (h : b.val < 128 := by decide) : Leb128.Encoding [b] b.val :=
  ⟨[], b, rfl, by simp, by simp, h, by simp, by simp [Leb128.payload, Nat.mod_eq_of_lt h]⟩

private theorem one {α : Type} {R : α → List U8 → Prop} {x bs}
    (h : R x bs) : VecEncoding R [x] (1#u8 :: bs) :=
  ⟨[1#u8], bs, leb 1#u8, by simpa using Rep.cons h Rep.nil, rfl⟩

private theorem padded {α : Type} {R : α → List U8 → Prop} (id size : U8)
    (absent : α) {x bs} (h : R x bs) (hlen : bs.length = size.val)
    (hsize : size.val < 128 := by decide) :
    PaddedEncoding id R absent x (id :: size :: bs) :=
  ⟨[], _, .nil, .present ⟨[size], bs, hlen ▸ leb size hsize, h, rfl⟩, rfl⟩

private theorem omitted {α : Type} (id : U8) (R : α → List U8 → Prop) (absent : α) :
    PaddedEncoding id R absent absent [] := ⟨[], [], .nil, .absent, rfl⟩

def globalType : types.GlobalType := ⟨.Const, .I32⟩
def imported : ModuleBinary.Import := ⟨[0x6D#u8], [0xF0#u8,0x9F#u8,0x98#u8,0x80#u8], .Global globalType⟩
def global : module.Global := ⟨globalType, .GlobalGet 0#u32⟩
def declarations : Declarations := { imports := [imported], globals := [global] }
def raw : ModuleBinary.Module := declarations.module [] []
def layout : Layout :=
  { imports := [2#u8,11#u8,1#u8,1#u8,0x6D#u8,4#u8,0xF0#u8,0x9F#u8,0x98#u8,0x80#u8,3#u8,0x7F#u8,0#u8]
    globals := [6#u8,6#u8,1#u8,0x7F#u8,0#u8,0x23#u8,0#u8,0x0B#u8] }
def input : Slice U8 := ModuleExamples.bytes (magicVersion ++ layout.bytes)
  (by simp [magicVersion, layout, Layout.bytes]; scalar_tac)

private theorem layout_valid : Layout.Valid 9 declarations layout := by
  constructor
  · exact omitted _ _ _
  · refine padded _ 11#u8 _ (one ?_) rfl
    refine ⟨[1#u8,0x6D#u8], [4#u8,0xF0#u8,0x9F#u8,0x98#u8,0x80#u8], [3#u8,0x7F#u8,0#u8], ?_, ?_, .global _ rfl, rfl⟩
    · exact ⟨ByteVecEncoding.iff.mpr ⟨[1#u8], leb 1#u8, rfl⟩, .cons (.one _ (by decide)) .nil⟩
    · exact ⟨ByteVecEncoding.iff.mpr ⟨[4#u8], leb 4#u8, rfl⟩,
        .cons (.four _ _ _ _ (Or.inl ⟨rfl, by decide, by decide⟩) (by decide) (by decide) (by decide) (by decide)) .nil⟩
  · exact omitted _ _ _
  · exact omitted _ _ _
  · exact omitted _ _ _
  · exact padded _ 6#u8 _ (one ⟨[0x7F#u8,0#u8], [0x23#u8,0#u8,0x0B#u8], rfl, .globalGet 0#u32 (leb 0#u8), rfl⟩) rfl
  · exact omitted _ _ _
  · exact omitted _ _ _
  · exact omitted _ _ _
  · exact ⟨rfl, rfl⟩
  · exact .nil
  · simp [Layout.Future, layout]
  · simp [ModuleTypesAllowed, ValueTypeAllowed, ConstAllowed, declarations,
      Declarations.module, globalType, imported, global]

private theorem init_typed : Expr_ok_const (ModuleElaboration.initializerContextOf raw)
    (ModuleConstants.expression (.GlobalGet 0#u32)) (Translate.valueType .I32) := by
  let env : module.Env := { ModuleExamples.emptyEnv with
    global_types := alloc.vec.Vec.from [globalType] (by simp; scalar_tac)
    num_imported_globals := 1#usize }
  have hv : ModuleConstants.Valid env (.GlobalGet 0#u32) .I32 :=
    .globalGet _ globalType (by simp [env]) rfl (by simp [env]) rfl
  apply hv.expr_ok_const
  · constructor <;> simp [ModuleElaboration.contextOf,
      raw, declarations, Declarations.module, imported, ModuleElaboration.importType,
      ModuleTranslation.tables, ModuleTranslation.mems, Forall]
  · rfl
  · rfl

private theorem requirements : Requirements raw := by
  intro id decls env hlo hhi hr
  interval_cases id
  · simp [SectionValid, raw, declarations, Declarations.module]
  · constructor
    · intro e he
      have he : e = imported := by simpa [raw, declarations, Declarations.module] using he
      subst e
      trivial
    · simp [hr.empty_tables (by decide), ModuleSections.rawTables, raw, declarations, Declarations.module, imported]
    · simp [hr.empty_memories (by decide), ModuleSections.rawMemories, raw, declarations, Declarations.module, imported]
  · simp [SectionValid, raw, declarations, Declarations.module]
  · constructor
    · simp [raw, declarations, Declarations.module]
    · rw [hr.tables_count (by decide) (by decide)]
      simp [raw, declarations, Declarations.module, imported, ModuleElaboration.importType, ModuleTranslation.tables]
  · constructor
    · simp [raw, declarations, Declarations.module]
    · rw [hr.memories_count (by decide) (by decide)]
      simp [raw, declarations, Declarations.module, imported, ModuleElaboration.importType, ModuleTranslation.mems]
  · intro g hg
    have hg : g = global := by simpa [raw, declarations, Declarations.module] using hg
    subst g
    exact ModuleConstants.valid_of_typing (hr.initializer_globals (by decide))
      (by simpa [ModuleConstants.FunctionContext, ModuleElaboration.initializerContextOf]
        using hr.funcs_context (by decide)) init_typed
  · constructor <;> simp [raw, declarations, Declarations.module]
  · simp [SectionValid, raw, declarations, Declarations.module]
  · simp [SectionValid, raw, declarations, Declarations.module]
  · trivial

/-- A four-byte emoji import name remains Unicode, and the imported immutable
I32 global is available to a defined global's `global.get` initializer. -/
theorem imported_initializer_accepted : ∃ decoded, module.validate_module input .Wasm1 = .ok (.Ok decoded) := by
  have hp : At PrefixEncoding input 0#usize declarations (Slice.len input) := by
    refine ⟨magicVersion ++ layout.bytes, layout_valid.encoding, ?_⟩
    constructor <;> simp [input, ModuleExamples.bytes, alloc.vec.Vec.deref,
      magicVersion, layout, Layout.bytes]
  obtain ⟨env, decls, he, hr⟩ := module.validate_env.complete input raw declarations (Slice.len input)
    hp rfl (.inl rfl) requirements
  exact ⟨⟨env, ⟨alloc.vec.Vec.new _⟩⟩, ModuleExamples.accepted_at_end input env
    (by simp [input, ModuleExamples.bytes, alloc.vec.Vec.deref,
      magicVersion, layout, Layout.bytes, limits.MAX_MODULE_BYTES])
    (hr.functions_eq (by decide)) he⟩

/-- The exact emoji/import/initializer bytes receive the full module certificate. -/
theorem imported_initializer_validated : ∃ decoded, module.validate_module input .Wasm1 = .ok (.Ok decoded) ∧
    ModuleSound.Validated input decoded := by
  obtain ⟨decoded, ha⟩ := imported_initializer_accepted
  exact ⟨decoded, ha, module.validate_module.wasm_sound _ _ ha⟩

def definedGlobalInput : Slice U8 := ModuleExamples.bytes (magicVersion ++
  [6#u8,11#u8,2#u8,0x7F#u8,0#u8,0x41#u8,0#u8,0x0B#u8,
    0x7F#u8,0#u8,0x23#u8,0#u8,0x0B#u8])
  (by simp [magicVersion]; scalar_tac)

/-- An earlier defined immutable global is still unavailable in a Wasm 1.0
constant expression; only imported immutable globals may be referenced. -/
theorem defined_global_initializer_rejected : module.validate_module definedGlobalInput .Wasm1 =
    .ok (.Err .MutableGlobalInConstExpr) := by
  let data := definedGlobalInput
  let initial := ModuleExamples.emptyEnv
  have hheader := module.read_header.complete data 8#usize (by
    constructor <;> simp [data, definedGlobalInput, ModuleExamples.bytes, alloc.vec.Vec.deref, magicVersion])
  have hh : SectionHeader data 8#usize 6#u8 10#usize 21#usize := by
    refine ⟨9#usize, 11#u32, ⟨[6#u8], rfl, ?_⟩, ?_, rfl, by decide⟩
    · constructor <;> simp [data, definedGlobalInput, ModuleExamples.bytes, alloc.vec.Vec.deref, magicVersion]
    · refine ⟨[11#u8], ?_, rfl, by decide, leb 11#u8⟩
      simp [data, definedGlobalInput, ModuleExamples.bytes, alloc.vec.Vec.deref, magicVersion]
  have hcount := (show At IndexEncoding data 10#usize 2#u32 11#usize from
    ⟨[2#u8], leb 2#u8, by constructor <;> simp [data, definedGlobalInput, ModuleExamples.bytes, alloc.vec.Vec.deref, magicVersion]⟩).read_index
  have hg1 := module.decode_global_type.complete data 11#usize globalType 13#usize
    ⟨[0x7F#u8,0#u8], rfl, by constructor <;> simp [data, definedGlobalInput, ModuleExamples.bytes, alloc.vec.Vec.deref, magicVersion]⟩
    .Wasm1 trivial
  have hz : ConstEncoding (.I32 0#i32) [0x41#u8,0#u8,0x0B#u8] :=
    .i32 _ ⟨[], 0#u8, rfl, by simp, by simp, by decide, rfl, by decide, by decide⟩
  have he1 := module.decode_const_expr.complete
    (env := initial) (ty := .I32)
    (show At ConstEncoding data 13#usize (.I32 0#i32) 16#usize from
      ⟨_, hz, by constructor <;> simp [data, definedGlobalInput, ModuleExamples.bytes, alloc.vec.Vec.deref, magicVersion]⟩) (.i32 _) .Wasm1 trivial
  obtain ⟨types, htypes, htval⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec initial.global_types globalType (by simp [initial, ModuleExamples.emptyEnv]; scalar_tac))
  obtain ⟨globals, hglobals, hgval⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec initial.globals (⟨globalType, .I32 0#i32⟩ : module.Global)
      (by simp [initial, ModuleExamples.emptyEnv]; scalar_tac))
  let updated := {initial with global_types := types, globals := globals}
  have hgt : updated.global_types.val = [globalType] := by simpa [updated, initial, ModuleExamples.emptyEnv] using htval
  have hglobal : module.const_global updated 0#u32 = .ok (.Err .MutableGlobalInConstExpr) := by
    have hcast : UScalar.cast .Usize 0#u32 = 0#usize := by scalar_tac
    simp [module.const_global, hcast, lift, hgt, updated, initial, ModuleExamples.emptyEnv]
  have hg2 := module.decode_global_type.complete data 16#usize globalType 18#usize
    ⟨[0x7F#u8,0#u8], rfl, by constructor <;> simp [data, definedGlobalInput, ModuleExamples.bytes, alloc.vec.Vec.deref, magicVersion]⟩
    .Wasm1 trivial
  have hop := (show At ByteEncoding data 18#usize 0x23#u8 19#usize from
    ⟨[0x23#u8], rfl, by constructor <;> simp [data, definedGlobalInput, ModuleExamples.bytes, alloc.vec.Vec.deref, magicVersion]⟩).read_byte
  have hidx := (show At IndexEncoding data 19#usize 0#u32 20#usize from
    ⟨[0#u8], leb 0#u8, by constructor <;> simp [data, definedGlobalInput, ModuleExamples.bytes, alloc.vec.Vec.deref, magicVersion]⟩).read_index
  have he2 : module.decode_const_expr data 18#usize updated .I32 .Wasm1 = .ok (.Err .MutableGlobalInConstExpr) := by
    simp [module.decode_const_expr, hop, hidx, hglobal, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  have hrest : module.decode_global_section_loop data updated .Wasm1 2#u32 16#usize 1#u32 =
      .ok (.Err .MutableGlobalInConstExpr, updated) := by
    unfold module.decode_global_section_loop
    rw [loop]
    simp [module.decode_global_section_loop.body, hg2, he2, globalType,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  have hinc : (0#u32 + 1#u32 : Result U32) = .ok 1#u32 := by
    have hs : (0#u32 + 1#u32 : Result U32) ⦃ x => x = 1#u32 ⦄ := by step*
    obtain ⟨x, hx, rfl⟩ := WP.spec_imp_exists hs
    exact hx
  simp only [globalType] at htypes hglobals
  have hread : module.decode_global_section data 10#usize initial .Wasm1 =
      .ok (.Err .MutableGlobalInConstExpr, updated) := by
    simp [module.decode_global_section, hcount, core.result.Result.Insts.CoreOpsTry.branch]
    unfold module.decode_global_section_loop
    rw [loop]
    simpa [module.decode_global_section_loop.body, hg1, he1, globalType,
      htypes, hglobals, hinc, core.result.Result.Insts.CoreOpsTry.branch,
      module.decode_global_section_loop, module.declare_initializer, updated] using hrest
  have hloop : parseLoop data initial 8#usize 0#u8 = .ok (.Err .MutableGlobalInConstExpr, ()) := by
    unfold parseLoop module.validate_env_with_loop
    rw [loop]
    have hmore : ¬ 8#usize ≥ Slice.len data := by decide
    simp [module.validate_env_with_loop.body, hmore,
      module.read_section_header.complete data 8#usize 6#u8 10#usize 21#usize hh,
      module.decode_env_section, hread, module.SECTION_CUSTOM, module.SECTION_CODE,
      module.SECTION_DATA, module.section_order,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  have hsplit : stream.find_code_region data = .ok (Slice.len data, Slice.len data) := by
    unfold stream.find_code_region
    rw [split_skip_section data 8#usize 10#usize 21#usize 6#u8 hh (by decide)]
    have hlen : Slice.len data = 21#usize := UScalar.eq_of_val_eq rfl
    simpa [hlen] using split_loop_eof data
  apply ModuleExamples.environment_error data _
    (by simp [data, definedGlobalInput, ModuleExamples.bytes, alloc.vec.Vec.deref, magicVersion, limits.MAX_MODULE_BYTES]) hsplit
  simp [module.validate_env, module.validate_env_with, module.Env.new, hheader,
    core.result.Result.Insts.CoreOpsTry.branch, initial, ModuleExamples.emptyEnv,
    parseLoop] at hloop ⊢
  simp [hloop]

end Itasca.ModuleImportedGlobalExamples
