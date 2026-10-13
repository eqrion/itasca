import Itasca.Examples.Module.Basic
import Itasca.Module.Completeness
import Itasca.Stream.SliceLayout
import Itasca.Examples.Module.Support

open Aeneas Aeneas.Std

namespace Itasca.Examples.ModuleFunctions

open ModuleSupport (leb one padded omitted)

open ModuleBinary ModuleEnv

def functionType : types.FuncType := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _⟩
def imported : ModuleBinary.Import := ⟨[0x6D#u8], [0x66#u8], .Func 0#u32⟩
def exported : ModuleBinary.Export := ⟨[0x72#u8], .Func 1#u32⟩
def entry : ModuleBinary.Code := ⟨[(1#u32, .I32)], [.CALL (.mk_uN 0)]⟩
def declarations : Declarations :=
  { types := [functionType], imports := [imported], functions := [0#u32],
    exports := [exported], start := some 1#u32 }
def raw : ModuleBinary.Module := declarations.module [entry] []
def layout : Layout :=
  { types := [1#u8,4#u8,1#u8,0x60#u8,0#u8,0#u8]
    imports := [2#u8,7#u8,1#u8,1#u8,0x6D#u8,1#u8,0x66#u8,0#u8,0#u8]
    functions := [3#u8,2#u8,1#u8,0#u8]
    exports := [7#u8,5#u8,1#u8,1#u8,0x72#u8,0#u8,1#u8]
    start := [8#u8,1#u8,1#u8] }
def codeBytes : List U8 := [10#u8,8#u8,1#u8,6#u8,1#u8,1#u8,0x7F#u8,0x10#u8,0#u8,0x0B#u8]
def input : Slice U8 := Examples.ModuleSupport.bytes (magicVersion ++ layout.bytes ++ codeBytes)
  (by simp [magicVersion, layout, Layout.bytes, codeBytes]; scalar_tac)

private theorem ascii (b : U8) (hb : b.val ≤ 127) : NameEncoding [b] [1#u8,b] :=
  ⟨ByteVecEncoding.iff.mpr ⟨[1#u8], leb 1#u8, rfl⟩, .cons (.one _ hb) .nil⟩

theorem layout_valid : Layout.Valid 9 declarations layout := by
  constructor
  · exact padded _ 4#u8 _ (one ⟨[0#u8], [0#u8],
      ⟨[0#u8], [], leb 0#u8, .nil, rfl⟩, ⟨[0#u8], [], leb 0#u8, .nil, rfl⟩, rfl⟩) rfl
  · exact padded _ 7#u8 _ (one ⟨[1#u8,0x6D#u8], [1#u8,0x66#u8], [0#u8,0#u8],
      ascii _ (by decide), ascii _ (by decide), .func _ (leb 0#u8), rfl⟩) rfl
  · exact padded _ 2#u8 _ (one (leb 0#u8)) rfl
  · exact omitted _ _ _
  · exact omitted _ _ _
  · exact omitted _ _ _
  · exact padded _ 5#u8 _ (one ⟨[1#u8,0x72#u8], [0#u8,1#u8], ascii _ (by decide), .func _ (leb 1#u8), rfl⟩) rfl
  · exact padded _ 1#u8 _ ⟨1#u32, rfl, leb 1#u8⟩ rfl
  · exact omitted _ _ _
  · exact ⟨rfl, rfl⟩
  · exact .nil
  · simp [Layout.Future, layout]
  · simp [ModuleTypesAllowed, ValueTypeAllowed, declarations, Declarations.module,
      functionType, imported, exported]

private theorem functions_context {last decls env} (h : Ready raw last decls env) (hn : 3 ≤ last) :
    env.func_types.val.map EnvTranslation.funcType =
      [.mk_functype (.mk_list []) (.mk_list []), .mk_functype (.mk_list []) (.mk_list [])] := by
  simpa [ModuleElaboration.contextOf, raw, declarations, Declarations.module, imported,
    ModuleElaboration.importType, ModuleElaboration.functionType, ModuleTranslation.funcs,
    functionType, EnvTranslation.funcType] using (h.funcs_context hn).symm

theorem requirements : Requirements raw := by
  intro id decls env hlo hhi hr
  interval_cases id
  · simp [SectionValid, Profile.FuncTypeAdmissible, raw, declarations, Declarations.module, functionType]
  · constructor
    · intro e he
      have he : e = imported := by simpa [raw, declarations, Declarations.module] using he
      subst e
      simp [imported, hr.types_eq (by decide), raw, declarations, Declarations.module]
    · simp [hr.empty_tables (by decide), ModuleSections.rawTables, raw, declarations, Declarations.module, imported]
    · simp [hr.empty_memories (by decide), ModuleSections.rawMemories, raw, declarations, Declarations.module, imported]
  · simp [SectionValid, hr.types_eq (by decide), raw, declarations, Declarations.module]
  · constructor
    · simp [raw, declarations, Declarations.module]
    · rw [hr.tables_count (by decide) (by decide)]
      simp [raw, declarations, Declarations.module, imported, ModuleElaboration.importType, ModuleTranslation.tables]
  · constructor
    · simp [raw, declarations, Declarations.module]
    · rw [hr.memories_count (by decide) (by decide)]
      simp [raw, declarations, Declarations.module, imported, ModuleElaboration.importType, ModuleTranslation.mems]
  · simp [SectionValid, raw, declarations, Declarations.module]
  · constructor
    · simp [raw, declarations, Declarations.module]
    · intro e he
      have he : e = exported := by simpa [raw, declarations, Declarations.module] using he
      subst e
      have hlen := congrArg List.length (functions_context hr (by decide))
      simp only [List.length_map, List.length_cons, List.length_nil] at hlen
      change 1 < env.func_types.val.length
      omega
  · intro idx hi
    have he : idx = 1#u32 := by simpa [raw, declarations, Declarations.module] using hi.symm
    subst idx
    apply ModuleElaboration.start_valid_of_typing (hr.moduleContext (by decide))
    apply Start_ok.mk_Start_ok
    · simp [ModuleElaboration.contextOf, raw, declarations, Declarations.module,
        ModuleTranslation.funcs, ModuleElaboration.importType, imported, proj_uN_0]
    · rfl
    · exact (hr.moduleContext (by decide)).wf
    · exact .start_case_0 _ (EnvTranslation.index_wf 1#u32)
  · simp [SectionValid, raw, declarations, Declarations.module]
  · trivial

theorem code_encoding : SectionEncoding 10#u8 (VecEncoding CodeEncodingWithinLimits) [entry] codeBytes := by
  refine ⟨[8#u8], [1#u8,6#u8,1#u8,1#u8,0x7F#u8,0x10#u8,0#u8,0x0B#u8], leb 8#u8, one ?_, rfl⟩
  refine ⟨by simp [entry, Code.declared, limits.MAX_LOCALS], [6#u8], [1#u8,1#u8,0x7F#u8],
    [0x10#u8,0#u8,0x0B#u8], leb 6#u8, one ⟨[1#u8], leb 1#u8, rfl⟩, ?_, by simp [limits.MAX_FUNCTION_BYTES], rfl⟩
  refine ⟨[.plain (.CALL (.mk_uN 0)), .end_], ?_, ?_⟩
  · exact Rep.cons (show Wasm1.TokenEncoding (.plain (.CALL (.mk_uN 0))) [0x10#u8,0#u8] from
      ⟨0x10#u8, [0#u8], rfl, .call 0#u32 (leb 0#u8)⟩)
      (Rep.cons (show Wasm1.TokenEncoding .end_ [0x0B#u8] from ⟨0x0B#u8, [], rfl, .end_⟩) Rep.nil)
  · exact ⟨[.plain (.CALL (.mk_uN 0))], rfl,
      .simple .nil (.plain _ (.instr_case_10 _ (EnvTranslation.index_wf 0#u32)))⟩

theorem entry_typed {decls env} (hr : Ready raw 10 decls env) : CodeEntry.Typed env 0#u32 entry := by
  have htypes : env.types.val = [functionType] := hr.types_eq (by decide)
  refine ⟨by simp [htypes], ?_, ?_, ?_, ?_⟩
  · let C := CodeEntry.bodyContext env [] entry.declared []
    have hf : C.FUNCS = [.mk_functype (.mk_list []) (.mk_list []), .mk_functype (.mk_list []) (.mk_list [])] :=
      functions_context hr (by decide)
    have hw : wf_context C := by
      constructor <;> simp only [Forall, List.mem_map]
      · rintro _ ⟨tt, _, rfl⟩; exact EnvTranslation.tableType_wf tt
      · rintro _ ⟨tt, _, rfl⟩; exact EnvTranslation.memType_wf tt
    have hi : Instr_ok C (.CALL (.mk_uN 0)) (.mk_functype (.mk_list []) (.mk_list [])) :=
      .call C _ [] [] (by simp [hf, proj_uN_0]) (by simp [hf, proj_uN_0]) hw
        (.instr_case_10 _ (EnvTranslation.index_wf 0#u32))
    simpa [htypes, functionType, entry, CodeEntry.instructionType, C] using
      Instrs_ok.instr C _ _ _ hi hw (.instr_case_10 _ (EnvTranslation.index_wf 0#u32))
  · exact .cons (.leaf _ _ trivial) (.nil _)
  · simp [entry, ModuleBinary.ValueTypeAllowed]
  · simp [entry, DeclaredReferences.Instructions, DeclaredReferences.instructionsIndices,
      DeclaredReferences.instructionIndices]

theorem prefix_encoding : At PrefixEncoding input 0#usize declarations 37#usize := by
  refine ⟨magicVersion ++ layout.bytes, layout_valid.encoding, ?_⟩
  constructor <;> simp [input, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref,
    magicVersion, layout, Layout.bytes, codeBytes]

theorem code_at : At (SectionEncoding 10#u8 (VecEncoding CodeEncodingWithinLimits))
    input 37#usize [entry] 47#usize := by
  refine ⟨codeBytes, code_encoding, ?_⟩
  constructor <;> simp [input, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref,
    magicVersion, layout, Layout.bytes, codeBytes]

/-- The parsed prefix has one imported and one defined function, and stops
exactly before the code section. This witness is reusable for visitor tests. -/
theorem environment : ∃ env decls, module.validate_env input .Wasm1 = .ok (.Ok (env, 37#usize)) ∧
    Ready raw 10 decls env := by
  obtain ⟨first, hh, _⟩ := code_at.section_split
  exact module.validate_env.complete input raw declarations 37#usize prefix_encoding rfl
    (.inr ⟨10#u8, first, 47#usize, hh, by decide⟩) requirements

/-- Public acceptance checks the declared local vector and a direct call into
the imported function space, together with the export and start declaration. -/
theorem functions_accepted : ∃ decoded, module.validate_module input .Wasm1 = .ok (.Ok decoded) := by
  let tail : module.Tail := ⟨alloc.vec.Vec.new _⟩
  have ht : At ModuleTail.Encoding input 47#usize raw.data (Slice.len input) := by
    refine ⟨[], ⟨[], [], ⟨[], [], .nil, .absent, rfl⟩, .nil, rfl⟩, ?_⟩
    constructor <;> simp [input, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref,
      magicVersion, layout, Layout.bytes, codeBytes]
  obtain ⟨first, hh, _⟩ := code_at.section_split
  have hl : ModuleLayout.Layout input raw declarations 37#usize 47#usize :=
    ⟨rfl, prefix_encoding, .inl code_at, ht, .inr ⟨10#u8, first, 47#usize, hh, by decide⟩⟩
  obtain ⟨env, ha⟩ := StreamSliceExamplesSupport.accepted_layout input raw declarations
    37#usize 47#usize hl (by
      simp [input, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref,
        magicVersion, layout, Layout.bytes, codeBytes, limits.MAX_MODULE_BYTES])
    requirements tail rfl (by
      intro decls env hr
      rw [hr.functions_eq (by decide)]
      exact .cons (entry_typed hr) .nil) (by
      intro decls env hr
      simp [tail])
  exact ⟨⟨env, tail⟩, ha⟩

/-- Whole-module soundness certifies these exact import/code/export/start bytes. -/
theorem functions_validated : ∃ decoded, module.validate_module input .Wasm1 = .ok (.Ok decoded) ∧
    ModuleSound.Validated input decoded := by
  obtain ⟨decoded, ha⟩ := functions_accepted
  exact ⟨decoded, ha, module.validate_module.wasm_sound _ _ ha⟩

end Itasca.Examples.ModuleFunctions
