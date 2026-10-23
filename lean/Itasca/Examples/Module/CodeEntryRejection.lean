import Itasca.Main
import Itasca.Examples.Module.Basic
import Itasca.Examples.Wasm1.Support
import Itasca.Examples.Module.Support

/-!
# A rejected code entry and the batch obligation

A code entry `02 00 ff` has a well-formed size and local declarations but an unknown opcode in its
body. `bad_body_entry_rejected` shows `module.validate_code_entry` reports `UnrecognizedOpcode`.
`bad_batch_validation_rejected` and `bad_batch_finish_rejected` show the streaming worker
`stream.CodeBatch.validate_func` records that error so `stream.CodeBatch.finish` rejects the batch,
and `tail_custom_preserves_work` shows a trailing custom section leaves the outstanding batch list
intact.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.ModuleCodeEntryRejection

open ModuleSupport (leb)

open ModuleBinary

private theorem one_room : 1 ≤ Usize.max := by scalar_tac

/-- A code entry of size 2 with no local declarations and the body byte `0xff`, an unknown
opcode. -/
def badBytes : Slice U8 := Examples.ModuleSupport.bytes [2#u8,0#u8,0xFF#u8]

/-- An environment with one function of type `[] -> []`. -/
def badEnv : module.Env :=
  { Examples.ModuleBasic.emptyEnv with
    types := alloc.vec.Vec.from [Examples.BodySupport.voidFunction] (by simp; scalar_tac)
    func_type_indices := alloc.vec.Vec.from [0#u32] (by simp; scalar_tac)
    func_types := alloc.vec.Vec.from [Examples.BodySupport.voidFunction] (by simp; scalar_tac) }

private theorem bad_size : Leb128.Decoded badBytes 0#usize 2#u32 1#usize :=
  (show Wasm1.BytesAt badBytes 0#usize [2#u8] 1#usize by
    constructor <;> simp [badBytes, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref]).u32_decoded _ (leb 2#u8)

private theorem bad_locals : module.decode_locals badBytes 1#usize .Wasm1 =
    .ok (.Ok (alloc.vec.Vec.new _, 2#usize)) := by
  obtain ⟨locals, hl, hv⟩ := module.decode_locals.complete badBytes 1#usize .Wasm1 [] 2#usize
    ⟨[0#u8], ⟨[0#u8], [], leb 0#u8, .nil, rfl⟩, by
      constructor <;> simp [badBytes, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref]⟩
    (by simp)
    (by simp [ModuleLocals.declared, limits.MAX_LOCALS])
  have he : locals = alloc.vec.Vec.new _ := alloc.vec.Vec.ext _ _ (by simpa [ModuleLocals.declared] using hv)
  simpa [he] using hl

private theorem bad_body_with : code.validate_body_with code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
    (Examples.BodySupport.bytes [0xFF#u8]) badEnv Examples.BodySupport.emptyContext 0#u32 .Wasm1 () =
      .ok (.Err .UnrecognizedOpcode, ()) := by
  obtain ⟨⟨r, v⟩, hr⟩ := code.validate_body_with.total
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total
    (Examples.BodySupport.bytes [0xFF#u8]) badEnv Examples.BodySupport.emptyContext 0#u32 .Wasm1 ()
  have he := code.validate_body_with.eq_core (Examples.BodySupport.bytes [0xFF#u8]) badEnv
    Examples.BodySupport.emptyContext 0#u32 .Wasm1
  rw [show Examples.BodySupport.emptyContext.locals = alloc.vec.Vec.new _ from rfl,
    show Examples.BodySupport.emptyContext.results = alloc.vec.Vec.new _ from rfl,
    Examples.BodySupport.unknown_opcode_rejected badEnv .Wasm1 rfl, hr] at he
  cases v
  simp at he
  subst he
  exact hr

/-- `module.validate_code_entry` on `badBytes` returns `Body UnrecognizedOpcode`. -/
theorem bad_body_entry_rejected : module.validate_code_entry badBytes 0#usize badEnv 0#usize .Wasm1 =
    .ok (.Err (.Body .UnrecognizedOpcode)) := by
  have hread := reader.read_u32_leb.complete badBytes 0#usize 2#u32 1#usize bad_size
  have htypes : badEnv.types.val = [Examples.BodySupport.voidFunction] := rfl
  have hfuncs : badEnv.func_type_indices.val = [0#u32] := rfl
  have hs : module.validate_code_entry badBytes 0#usize badEnv 0#usize .Wasm1 ⦃ r =>
      r = .Err (.Body .UnrecognizedOpcode) ⦄ := by
    unfold module.validate_code_entry module.validate_code_entry_with
    simp [hfuncs, hread, core.result.Result.Insts.CoreOpsTry.branch]
    step as ⟨n, n_post⟩
    have hn : n = 2#usize := by scalar_tac
    rw [hn]
    rw [module.have_bytes.complete badBytes 1#usize 2#usize (by decide)]
    simp only [bind_ok]
    step as ⟨last, last_post⟩
    have hend : last = 3#usize := by scalar_tac
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
    have hft : ft = Examples.BodySupport.voidFunction := by simpa [htypes] using ft_post
    rw [hft]
    step as ⟨v1, v1_post⟩ by simp [Examples.BodySupport.voidFunction, alloc.vec.Vec.deref]
    have hv1 : v1 = alloc.vec.Vec.new types.ValueType :=
      alloc.vec.Vec.ext _ _ (by simpa [Examples.BodySupport.voidFunction, alloc.vec.Vec.deref] using v1_post)
    subst v1
    step as ⟨v2, v2_post⟩
    have hv2 : v2 = alloc.vec.Vec.new types.ValueType :=
      alloc.vec.Vec.ext _ _ (by simpa [Examples.BodySupport.voidFunction, alloc.vec.Vec.deref] using v2_post)
    subst v2
    simp [code.OpVisitor.on_function_start.default]
    step as ⟨body, body_post, body_post1⟩ by simp [badBytes, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref]
    have hb : body = Examples.BodySupport.bytes [0xFF#u8] one_room := by
      apply Slice.ext
      simpa [badBytes, Examples.ModuleSupport.bytes, Examples.BodySupport.bytes, alloc.vec.Vec.deref] using body_post
    rw [hb]
    have hh := bad_body_with
    simp only [Examples.BodySupport.emptyContext] at hh
    simp [hh]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

/-- An issued batch for module 0, batch 0, covering function 0 at code offset 0 of `badBytes`
under Wasm 1.0. -/
def badIssued : StreamBatch.Issued := ⟨0#u64, 0#usize, badEnv, badBytes, 0#usize, 0#usize, 1#usize, .Wasm1⟩

private theorem bad_bounds : CodeEntry.Bounds badEnv := by
  intro ft hm
  have he : ft = Examples.BodySupport.voidFunction := by simpa [badEnv] using hm
  subst ft
  simp [Examples.BodySupport.voidFunction, limits.MAX_LOCALS]
  scalar_tac

/-- The batch worker `stream.CodeBatch.validate_func` rejects the well-framed entry with
`Body UnrecognizedOpcode` and stores the error in the batch. -/
theorem bad_batch_validation_rejected : ∃ after,
    stream.CodeBatch.validate_func code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      badIssued.seed 0#usize () = .ok (.Err (.Body .UnrecognizedOpcode), after, ()) ∧
    after.error = some (.Body .UnrecognizedOpcode) := by
  obtain ⟨⟨r, v⟩, hr⟩ := module.validate_code_entry_with.profile_total
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total
    badBytes 0#usize badEnv 0#usize () bad_bounds .Wasm1
  cases v
  have he : r = .Err (.Body .UnrecognizedOpcode) := by
    simpa [module.validate_code_entry, hr] using bad_body_entry_rejected
  subst r
  have hz : (0#usize + 0#usize : Result Usize) = .ok 0#usize := by
    obtain ⟨n, hn, hv⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := 0#usize) (y := 0#usize) (by scalar_tac))
    have he : n = 0#usize := by apply UScalar.eq_of_val_eq; simpa using hv
    simpa [he] using hn
  refine ⟨{ badIssued.seed with error := some (.Body .UnrecognizedOpcode) }, ?_, rfl⟩
  simp [stream.CodeBatch.validate_func, stream.CodeBatch.validate_next,
    badIssued, StreamBatch.Issued.seed, hr, hz, core.option.Option.is_none]

/-- After the worker fails, `stream.CodeBatch.finish` on the resulting batch returns the same
error. -/
theorem bad_batch_finish_rejected : ∃ after,
    stream.CodeBatch.validate_func code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      badIssued.seed 0#usize () = .ok (.Err (.Body .UnrecognizedOpcode), after, ()) ∧
    stream.CodeBatch.finish after = .ok (.Err (.Body .UnrecognizedOpcode)) := by
  obtain ⟨after, hr, he⟩ := bad_batch_validation_rejected
  exact ⟨after, hr, by simp [stream.CodeBatch.finish, he]⟩

/-- A trailing custom section with an empty name and no payload: `00 01 00`. -/
def tailBuffer : Slice U8 := Examples.ModuleSupport.bytes [0#u8,1#u8,0#u8]
/-- A tail with no data segments. -/
def emptyTail : module.Tail := ⟨alloc.vec.Vec.new _⟩

private theorem good_tail (env : module.Env) (hcount : env.data_count = none) :
    module.validate_tail tailBuffer 0#usize env .Wasm1 = .ok (.Ok emptyTail) := by
  apply module.validate_tail.complete emptyTail
  · refine ⟨[0#u8,1#u8,0#u8], ?_, ?_⟩
    · refine ⟨[], [0#u8,1#u8,0#u8], ⟨[], [], .nil, .absent, rfl⟩, ?_, rfl⟩
      have hc : CustomEncoding [0#u8,1#u8,0#u8] := by
        refine ⟨[], [], [0#u8], ?_, ?_⟩
        · exact ⟨ByteVecEncoding.iff.mpr ⟨[0#u8], leb 0#u8, rfl⟩, .nil⟩
        · exact ⟨[1#u8], [0#u8], leb 1#u8, rfl, rfl⟩
      simpa using CustomsEncoding.cons hc CustomsEncoding.nil
    · constructor <;> simp [tailBuffer, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref]
  · simp [emptyTail]
  · simp [hcount]

/-- A visitor whose custom-section callback leaves its state, here a list of issued batches,
unchanged. -/
def observeCustoms : module.ModuleVisitor (List StreamBatch.Issued) where
  on_custom_section v _ := .ok (.Ok (), v)

private theorem observe_customs_accept : ModuleTail.HooksAccept observeCustoms := by
  intro v chunk
  exact ⟨v, rfl⟩

private theorem observe_customs_preserve : ModuleTail.Preserves observeCustoms id := by
  intro v chunk v' h
  simpa [observeCustoms, Eq.comm] using h

/-- Validating the trailing custom section with `observeCustoms` accepts and returns the
outstanding batch list `[badIssued]` unchanged. -/
theorem tail_custom_preserves_work (env : module.Env) (hcount : env.data_count = none) :
    module.validate_tail_with observeCustoms tailBuffer 0#usize env .Wasm1 [badIssued] =
      .ok (.Ok emptyTail, [badIssued]) := by
  obtain ⟨v', hv⟩ := module.validate_tail_with.accepted_lift observeCustoms observe_customs_accept
    tailBuffer 0#usize env [badIssued] emptyTail (good_tail env hcount)
  have he := module.validate_tail_with.accepted_preserves observeCustoms id observe_customs_preserve
    tailBuffer 0#usize env [badIssued] emptyTail v' hv
  change v' = [badIssued] at he
  simpa only [he] using hv

end Itasca.Examples.ModuleCodeEntryRejection
