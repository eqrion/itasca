import Itasca.ModuleDeferred
import Itasca.ModuleFunctionExamples
import Itasca.ModuleDeferredValidation
import Itasca.WasmExamples

open Aeneas Aeneas.Std

namespace Itasca.ModuleConsumerExamples

open ModuleBinary ModuleCodeVisitor

private theorem one_room : 1 ≤ Usize.max := by scalar_tac

private theorem leb (b : U8) (h : b.val < 128 := by decide) : Leb128.Encoding [b] b.val :=
  ⟨[], b, rfl, by simp, by simp, h, by simp, by simp [Leb128.payload, Nat.mod_eq_of_lt h]⟩

private theorem code_section (data : Slice U8) (env : module.Env) (pos first entries last : Usize)
    (hlen : env.func_type_indices.val.length = 1)
    (hh : SectionHeader data pos 10#u8 first last)
    (hc : Leb128.Decoded data first 1#u32 entries) :
    module.code_section data pos env = .ok (.Ok (some ⟨1#u32, entries, last⟩)) := by
  have hm : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
  have hs : module.code_section data pos env ⦃ r => r = .Ok (some ⟨1#u32, entries, last⟩) ⦄ := by
    simp [module.code_section, hm, module.read_section_header.complete data pos 10#u8 first last hh,
      reader.read_u32_leb.complete data first 1#u32 entries hc,
      module.SECTION_CODE, core.result.Result.Insts.CoreOpsTry.branch]
    step
    have he : i1 = alloc.vec.Vec.len env.func_type_indices := by apply UScalar.eq_of_val_eq; scalar_tac
    simp [he]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

private theorem one_recorded (data : Slice U8) (env : module.Env) (pos entries content last : Usize)
    (hlen : env.func_type_indices.val.length = 1)
    (hp : pos.val + 11 ≤ Usize.max) (he : entries.val + limits.MAX_LEB_BYTES.val ≤ Usize.max)
    (hcs : module.code_section data pos env = .ok (.Ok (some ⟨1#u32, entries, last⟩)))
    (hf : module.code_entry_extent data entries = .ok (.Ok (content, last))) :
    module.validate_code_with recorder data pos env [] = .ok (.Ok last, [(0#usize, entries)]) := by
  have hs : limits.MAX_CODE_HEADER_BYTES = .ok 11#usize := by
    have hs : limits.MAX_CODE_HEADER_BYTES ⦃ n => n = 11#usize ⦄ := by
      simp [limits.MAX_CODE_HEADER_BYTES, limits.MAX_LEB_BYTES]
      step*
    obtain ⟨n, hn, rfl⟩ := WP.spec_imp_exists hs
    exact hn
  obtain ⟨need, hn, _⟩ := WP.spec_imp_exists (Usize.add_spec (x := pos) (y := 11#usize) (by simpa using hp))
  obtain ⟨needEntry, hne, _⟩ := WP.spec_imp_exists (Usize.add_spec (x := entries) (y := limits.MAX_LEB_BYTES) he)
  have hj : (0#usize + 1#usize : Result Usize) = .ok 1#usize := by
    obtain ⟨j, hj, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := 0#usize) (y := 1#usize) (by scalar_tac))
    have he : j = 1#usize := UScalar.eq_of_val_eq (by simpa using hv)
    simpa only [he] using hj
  apply SectionRun.accepted
  apply SectionRun.present hs hn (by rfl) hcs
  exact EntriesRun.more (by simp [hlen]) hne rfl hf rfl rfl hj
    (.done _ _ _ (by simp [hlen]))

/-- This section has one framed body containing an unknown opcode. -/
def badBytes : Slice U8 := ModuleExamples.bytes [10#u8,4#u8,1#u8,2#u8,0#u8,0xFF#u8]

def badEnv : module.Env :=
  { ModuleExamples.emptyEnv with
    types := alloc.vec.Vec.from [WasmExamples.voidFunction] (by simp; scalar_tac)
    func_type_indices := alloc.vec.Vec.from [0#u32] (by simp; scalar_tac)
    func_types := alloc.vec.Vec.from [WasmExamples.voidFunction] (by simp; scalar_tac) }

private theorem bad_header : SectionHeader badBytes 0#usize 10#u8 2#usize 6#usize := by
  refine ⟨1#usize, 4#u32, ⟨[10#u8], rfl, ?_⟩, ?_, rfl, by decide⟩
  · constructor <;> simp [badBytes, ModuleExamples.bytes, alloc.vec.Vec.deref]
  · exact (show Wasm.BytesAt badBytes 1#usize [4#u8] 2#usize by
      constructor <;> simp [badBytes, ModuleExamples.bytes, alloc.vec.Vec.deref]).u32_decoded _ (leb 4#u8)

private theorem bad_count : Leb128.Decoded badBytes 2#usize 1#u32 3#usize :=
  (show Wasm.BytesAt badBytes 2#usize [1#u8] 3#usize by
    constructor <;> simp [badBytes, ModuleExamples.bytes, alloc.vec.Vec.deref]).u32_decoded _ (leb 1#u8)

private theorem bad_size : Leb128.Decoded badBytes 3#usize 2#u32 4#usize :=
  (show Wasm.BytesAt badBytes 3#usize [2#u8] 4#usize by
    constructor <;> simp [badBytes, ModuleExamples.bytes, alloc.vec.Vec.deref]).u32_decoded _ (leb 2#u8)

/-- Recording only frames the entry; it can succeed before a worker rejects
its body. This regression makes the deferred obligation visibly necessary. -/
theorem bad_body_recorded : module.validate_code_with recorder badBytes 0#usize badEnv [] =
    .ok (.Ok 6#usize, [(0#usize, 3#usize)]) := by
  apply one_recorded badBytes badEnv 0#usize 3#usize 4#usize 6#usize rfl
    (by scalar_tac) (by simp [limits.MAX_LEB_BYTES]; scalar_tac)
  · exact code_section badBytes badEnv 0#usize 2#usize 3#usize 6#usize rfl bad_header bad_count
  · exact module.code_entry_extent.complete badBytes 3#usize 4#usize 6#usize ⟨2#u32, bad_size, rfl, by decide⟩

private theorem bad_locals : module.decode_locals badBytes 4#usize =
    .ok (.Ok (alloc.vec.Vec.new _, 5#usize)) := by
  obtain ⟨locals, hl, hv⟩ := module.decode_locals.complete badBytes 4#usize [] 5#usize
    ⟨[0#u8], ⟨[0#u8], [], leb 0#u8, .nil, rfl⟩, by
      constructor <;> simp [badBytes, ModuleExamples.bytes, alloc.vec.Vec.deref]⟩
    (by simp [ModuleLocals.declared, limits.MAX_LOCALS])
  have he : locals = alloc.vec.Vec.new _ := alloc.vec.Vec.ext _ _ (by simpa [ModuleLocals.declared] using hv)
  simpa [he] using hl

private theorem bad_body_with : code.validate_body_with code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
    (WasmExamples.bytes [0xFF#u8]) badEnv WasmExamples.emptyContext () =
      .ok (.Err .UnrecognizedOpcode, ()) := by
  obtain ⟨⟨r, v⟩, hr⟩ := code.validate_body_with.wasm_total
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total
    (WasmExamples.bytes [0xFF#u8]) badEnv WasmExamples.emptyContext ()
  have he : r = .Err .UnrecognizedOpcode := by
    simpa [code.validate_body, hr] using WasmExamples.unknown_opcode_rejected badEnv
  simpa [he] using hr

/-- The worker rejects the body that the dispatch-only recorder handed out. -/
theorem bad_body_entry_rejected : module.validate_code_entry badBytes 3#usize badEnv 0#usize =
    .ok (.Err (.Body .UnrecognizedOpcode)) := by
  have hread := reader.read_u32_leb.complete badBytes 3#usize 2#u32 4#usize bad_size
  have htypes : badEnv.types.val = [WasmExamples.voidFunction] := rfl
  have hfuncs : badEnv.func_type_indices.val = [0#u32] := rfl
  have hs : module.validate_code_entry badBytes 3#usize badEnv 0#usize ⦃ r =>
      r = .Err (.Body .UnrecognizedOpcode) ⦄ := by
    unfold module.validate_code_entry module.validate_code_entry_with
    simp [hfuncs, hread, core.result.Result.Insts.CoreOpsTry.branch]
    step as ⟨n, n_post⟩
    have hn : n = 2#usize := by scalar_tac
    rw [hn]
    rw [module.have_bytes.complete badBytes 4#usize 2#usize (by decide)]
    simp only [bind_ok]
    step as ⟨last, last_post⟩
    have hend : last = 6#usize := by scalar_tac
    rw [hend]
    simp [bad_locals]
    step as ⟨type_idx, type_idx_post⟩
    have hi : type_idx = 0#u32 := by simpa [hfuncs] using type_idx_post
    rw [hi]
    step as ⟨t, t_post⟩
    have hti : t = 0#usize := by scalar_tac
    rw [hti]
    simp [htypes]
    step as ⟨ft, ft_post⟩
    have hft : ft = WasmExamples.voidFunction := by simpa [htypes] using ft_post
    rw [hft]
    step as ⟨v1, v1_post⟩ by simp [WasmExamples.voidFunction, alloc.vec.Vec.deref]
    have hv1 : v1 = alloc.vec.Vec.new types.ValueType :=
      alloc.vec.Vec.ext _ _ (by simpa [WasmExamples.voidFunction, alloc.vec.Vec.deref] using v1_post)
    subst v1
    step as ⟨v2, v2_post⟩
    have hv2 : v2 = alloc.vec.Vec.new types.ValueType :=
      alloc.vec.Vec.ext _ _ (by simpa [WasmExamples.voidFunction, alloc.vec.Vec.deref] using v2_post)
    subst v2
    simp [code.OpVisitor.on_function_start.default]
    step as ⟨body, body_post, body_post1⟩ by simp [badBytes, ModuleExamples.bytes, alloc.vec.Vec.deref]
    have hb : body = WasmExamples.bytes [0xFF#u8] one_room := by
      apply Slice.ext
      simpa [badBytes, ModuleExamples.bytes, WasmExamples.bytes, alloc.vec.Vec.deref] using body_post
    rw [hb]
    have hh := bad_body_with
    simp only [WasmExamples.emptyContext] at hh
    simp [hh]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

theorem bad_body_has_no_deferred_validation :
    ¬ EntriesValidate badBytes badEnv [(0#usize, 3#usize)] := by
  intro h
  obtain ⟨next, hn⟩ := h 0#usize 3#usize (by simp)
  rw [bad_body_entry_rejected] at hn
  simp at hn

def environmentBuffer : Slice U8 := ModuleExamples.bytes
  (magicVersion ++ ModuleFunctionExamples.layout.bytes)
  (by simp [magicVersion, ModuleFunctionExamples.layout, ModuleEnv.Layout.bytes]; scalar_tac)

def codeBuffer : Slice U8 := ModuleExamples.bytes ModuleFunctionExamples.codeBytes
  (by simp [ModuleFunctionExamples.codeBytes]; scalar_tac)

def tailBuffer : Slice U8 := ModuleExamples.bytes [0#u8,1#u8,0#u8]

def joinedInput : Slice U8 := ModuleExamples.bytes
  (environmentBuffer.val ++ codeBuffer.val ++ tailBuffer.val)
  (by simp [environmentBuffer, codeBuffer, tailBuffer, ModuleExamples.bytes, alloc.vec.Vec.deref,
    ModuleFunctionExamples.codeBytes, magicVersion, ModuleFunctionExamples.layout, ModuleEnv.Layout.bytes]; scalar_tac)

def emptyTail : module.Tail := ⟨alloc.vec.Vec.new _⟩

private theorem good_section_header : SectionHeader codeBuffer 0#usize 10#u8 2#usize 10#usize := by
  refine ⟨1#usize, 8#u32, ⟨[10#u8], rfl, ?_⟩, ?_, rfl, by decide⟩
  · constructor <;> simp [codeBuffer, ModuleFunctionExamples.codeBytes, ModuleExamples.bytes, alloc.vec.Vec.deref]
  · exact (show Wasm.BytesAt codeBuffer 1#usize [8#u8] 2#usize by
      constructor <;> simp [codeBuffer, ModuleFunctionExamples.codeBytes, ModuleExamples.bytes, alloc.vec.Vec.deref]).u32_decoded _ (leb 8#u8)

private theorem good_count : Leb128.Decoded codeBuffer 2#usize 1#u32 3#usize :=
  (show Wasm.BytesAt codeBuffer 2#usize [1#u8] 3#usize by
    constructor <;> simp [codeBuffer, ModuleFunctionExamples.codeBytes, ModuleExamples.bytes, alloc.vec.Vec.deref]).u32_decoded _ (leb 1#u8)

private theorem good_size : Leb128.Decoded codeBuffer 3#usize 6#u32 4#usize :=
  (show Wasm.BytesAt codeBuffer 3#usize [6#u8] 4#usize by
    constructor <;> simp [codeBuffer, ModuleFunctionExamples.codeBytes, ModuleExamples.bytes, alloc.vec.Vec.deref]).u32_decoded _ (leb 6#u8)

private theorem good_code_at : At (SectionEncoding 10#u8 (VecEncoding CodeEncodingWithinLimits))
    codeBuffer 0#usize [ModuleFunctionExamples.entry] 10#usize := by
  refine ⟨_, ModuleFunctionExamples.code_encoding, ?_⟩
  constructor <;> simp [codeBuffer, ModuleFunctionExamples.codeBytes, ModuleExamples.bytes, alloc.vec.Vec.deref]

private theorem good_env : ∃ env decls,
    module.validate_env environmentBuffer = .ok (.Ok (env, Slice.len environmentBuffer)) ∧
      ModuleEnv.Ready ModuleFunctionExamples.raw 9 decls env := by
  apply module.validate_env.complete environmentBuffer ModuleFunctionExamples.raw
    ModuleFunctionExamples.declarations (Slice.len environmentBuffer)
  · refine ⟨_, ModuleFunctionExamples.layout_valid.encoding, ?_⟩
    constructor <;> simp [environmentBuffer, ModuleExamples.bytes, alloc.vec.Vec.deref]
  · rfl
  · exact .inl rfl
  · exact ModuleFunctionExamples.requirements

private theorem good_tail (env : module.Env) :
    module.validate_tail tailBuffer 0#usize env = .ok (.Ok emptyTail) := by
  apply module.validate_tail.complete emptyTail
  · refine ⟨[0#u8,1#u8,0#u8], ?_, ?_⟩
    · refine ⟨[], [0#u8,1#u8,0#u8], ⟨[], [], .nil, .absent, rfl⟩, ?_, rfl⟩
      have hc : CustomEncoding [0#u8,1#u8,0#u8] := by
        refine ⟨[], [], [0#u8], ?_, ?_⟩
        · exact ⟨ByteVecEncoding.iff.mpr ⟨[0#u8], leb 0#u8, rfl⟩, .nil⟩
        · exact ⟨[1#u8], [0#u8], leb 1#u8, rfl, rfl⟩
      simpa using CustomsEncoding.cons hc CustomsEncoding.nil
    · constructor <;> simp [tailBuffer, ModuleExamples.bytes, alloc.vec.Vec.deref]
  · simp [emptyTail]

private theorem good_workers {env decls}
    (hr : ModuleEnv.Ready ModuleFunctionExamples.raw 9 decls env) :
    EntriesValidate codeBuffer env [(0#usize, 3#usize)] := by
  have hfunctions : env.func_type_indices.val = [0#u32] := hr.functions_eq (by decide)
  have htypes : env.types.val = [ModuleFunctionExamples.functionType] := hr.types_eq (by decide)
  have harity : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1 := by
    simp [htypes, ModuleFunctionExamples.functionType]
  have hbound : CodeEntry.Bounds env := by
    intro ft hm
    have he : ft = ModuleFunctionExamples.functionType := by simpa [htypes] using hm
    subst ft
    simp [ModuleFunctionExamples.functionType, limits.MAX_LOCALS]
    scalar_tac
  have hcs := code_section codeBuffer env 0#usize 2#usize 3#usize 10#usize
    (by simp [hfunctions]) good_section_header good_count
  obtain ⟨cs, hknown, _, he⟩ := module.code_section.complete_present
    codeBuffer 0#usize 10#usize env [ModuleFunctionExamples.entry] (by simp [hfunctions]) good_code_at
  have hcsEq : cs = ⟨1#u32, 3#usize, 10#usize⟩ := by simpa using hknown.symm.trans hcs
  subst cs
  obtain ⟨middle, hentry, hend⟩ := he.rep_cons
  have hm := hend.rep_nil
  have hentry' : At CodeEncodingWithinLimits codeBuffer 3#usize ModuleFunctionExamples.entry 10#usize := by
    simpa [hm] using hentry
  intro index pos hmem
  have he : index = 0#usize ∧ pos = 3#usize := by simpa using hmem
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨10#usize, module.validate_code_entry.complete codeBuffer 3#usize env 0#usize
    ModuleFunctionExamples.entry 10#usize (by simp [hfunctions]) ?_
    ⟨hr.represents.cache.func_arity harity, harity⟩ hbound hentry'⟩
  simpa [hfunctions] using ModuleFunctionExamples.entry_typed hr

/-- Independent buffers retain the imported/defined function context, while
the code entry's recorded offset is rebased from 40 in the full fixture to 3.
Workers discharge that exact recorded entry before module soundness is used. -/
theorem separate_buffers_deferred_validated : ∃ env,
    module.validate_env environmentBuffer = .ok (.Ok (env, Slice.len environmentBuffer)) ∧
    module.validate_code_with recorder codeBuffer 0#usize env [] =
      .ok (.Ok 10#usize, [(0#usize, 3#usize)]) ∧
    EntriesValidate codeBuffer env [(0#usize, 3#usize)] ∧
    ModuleSound.Validated joinedInput ⟨env, emptyTail⟩ := by
  obtain ⟨env, decls, he, hr⟩ := good_env
  have hfunctions : env.func_type_indices.val = [0#u32] := hr.functions_eq (by decide)
  have hcs := code_section codeBuffer env 0#usize 2#usize 3#usize 10#usize
    (by simp [hfunctions]) good_section_header good_count
  have hf := module.code_entry_extent.complete codeBuffer 3#usize 4#usize 10#usize
    ⟨6#u32, good_size, rfl, by decide⟩
  have hrecord := one_recorded codeBuffer env 0#usize 3#usize 4#usize 10#usize
    (by simp [hfunctions]) (by scalar_tac) (by simp [limits.MAX_LEB_BYTES]; scalar_tac) hcs hf
  have hworkers := good_workers hr
  refine ⟨env, he, hrecord, hworkers, ?_⟩
  apply module.validate_module.regions_deferred_wasm_sound recorder id recorder_records
    joinedInput environmentBuffer codeBuffer tailBuffer env emptyTail [] [(0#usize, 3#usize)]
  · rfl
  · simp [joinedInput, environmentBuffer, codeBuffer, tailBuffer, ModuleExamples.bytes, alloc.vec.Vec.deref,
      ModuleFunctionExamples.codeBytes, magicVersion, ModuleFunctionExamples.layout, ModuleEnv.Layout.bytes,
      limits.MAX_MODULE_BYTES]
  · exact he
  · have hlen : Slice.len codeBuffer = 10#usize := UScalar.eq_of_val_eq rfl
    simpa only [hlen] using hrecord
  · exact hworkers
  · exact good_tail env

/-- A custom-section observer can share the work list and leave it intact. -/
def observeCustoms : module.ModuleVisitor (List Entry) where
  on_custom_section v _ := .ok (.Ok (), v)

private theorem observe_customs_accept : ModuleTail.HooksAccept observeCustoms := by
  intro v chunk
  exact ⟨v, rfl⟩

private theorem observe_customs_preserve : ModuleTail.Preserves observeCustoms id := by
  intro v chunk v' h
  simpa [observeCustoms, Eq.comm] using h

/-- The final custom section cannot erase the outstanding entry obligation. -/
theorem tail_custom_preserves_work (env : module.Env) :
    module.validate_tail_with observeCustoms tailBuffer 0#usize env [(0#usize, 3#usize)] =
      .ok (.Ok emptyTail, [(0#usize, 3#usize)]) := by
  obtain ⟨v', hv⟩ := module.validate_tail_with.accepted_lift observeCustoms observe_customs_accept
    tailBuffer 0#usize env [(0#usize, 3#usize)] emptyTail (good_tail env)
  have he := module.validate_tail_with.accepted_preserves observeCustoms id observe_customs_preserve
    tailBuffer 0#usize env [(0#usize, 3#usize)] emptyTail v' hv
  change v' = [(0#usize, 3#usize)] at he
  simpa only [he] using hv

end Itasca.ModuleConsumerExamples
