import Itasca
import Itasca.Examples.Module.Basic
import Itasca.Examples.Module.SliceLayout

/-!
Proofs for Examples / Module.

This module collects BodySupport, CodeEntryRejection.
Each section documents its contracts and consumers.
-/

/-! ## BodySupport -/

section

/-!
# Shared helpers for body examples

Lemmas that run the extracted body loop one opcode at a time with the empty
visitor: `run_step` continues after an accepted step, `run_error` stops at a rejected step,
and `body_core_of_run` connects a run from
the initial frame to `code.bodyCore`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.BodySupport

/-- A byte slice with the listed contents. -/
def bytes (xs : List U8) (h : xs.length ≤ Usize.max := by scalar_tac) : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from xs h)

/-- A context with no locals and no results. -/
def emptyContext : code.Context := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _⟩

/-- The function type `[] -> []`. -/
def voidFunction : wasm_types.FuncType := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _⟩

/-- A run of the body loop from the initial frame determines the result of `code.bodyCore`. -/
theorem body_core_of_run (data : Slice U8) (env : metadata.Env)
    (locals results : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (result : core.result.Result Unit error.OpError)
    (hi : env.types.val[index.val]? = some ft)
    (hparams : ft.params.val.length ≤ 1000) (hresults : ft.results.val.length ≤ 1000)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hrun : Body.run data env ⟨locals, results⟩ index (Body.initial index) = .ok result) :
    code.bodyCore data env locals results index = .ok result := by
  have hb : index.val < env.types.val.length := List.getElem?_eq_some_iff.mp hi |>.1
  suffices hs : code.bodyCore data env locals results index ⦃ r => r = result ⦄ by
    obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
    exact hr
  unfold code.bodyCore
  dsimp only
  split
  · scalar_tac
  · step
    split
    · scalar_tac
    · step as ⟨actual, hactual⟩
      have he : actual = ft := by
        have hx := (List.getElem?_eq_some_iff.mp hi).2
        simp_all
      rw [he, code.check_func_type.complete ft hparams hresults]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, code.push_frame.initial]
      change Body.run data env ⟨locals, results⟩ index (Body.initial index) ⦃ r => r = result ⦄
      simp [hrun]

/-- An accepted step continues the loop from the step's state. -/
theorem run_step (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (st next : code.BodyState) (opcode : U8) (pos : Usize)
    (hc : st.blocks.val ≠ [])
    (hr : reader.read_byte data st.core.pos = .ok (.Ok (opcode, pos)))
    (hs : Body.step { st with core := { st.core with pos := pos } } data env ctx index
      opcode = .ok (.Ok (), next)) :
    Body.run data env ctx index st = Body.run data env ctx index next :=
  (Body.Execution.single hc hr hs).loop_eq

/-- A rejected step ends the loop with the step's error. -/
theorem run_error (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (st next : code.BodyState) (opcode : U8) (pos : Usize)
    (e : error.OpError) (hc : st.blocks.val ≠ [])
    (hr : reader.read_byte data st.core.pos = .ok (.Ok (opcode, pos)))
    (hs : Body.step { st with core := { st.core with pos := pos } } data env ctx index
      opcode = .ok (.Err e, next)) :
    Body.run data env ctx index st = .ok (.Err e) := by
  rw [Body.run_unfold, Body.loop_body_eq]
  have hc' : st.core.ctrls.val ≠ [] := by simpa using hc
  simp [hc', hr, hs, Body.continueStep]

/-- Reading an in-bounds byte returns it and advances the cursor by one. -/
theorem read_at (data : Slice U8) (pos next : Usize) (opcode : U8)
    (hp : pos.val < data.length) (hn : next.val = pos.val + 1)
    (hb : data.val[pos.val] = opcode) :
    reader.read_byte data pos = .ok (.Ok (opcode, next)) := by
  obtain ⟨r, hr, p, rfl, hq⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
  have heq : p = next := UScalar.eq_of_val_eq (hq.trans hn.symm)
  simpa [heq, hb] using hr

/-- The byte `0xff` is not a recognized opcode. -/
theorem step_unknown (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
     (ctx : code.Context) (index : U32)
    (h : st.core.vals.val.length < Usize.max) :
    Body.step st data env ctx index 0xFF#u8 = .ok (.Err .UnrecognizedOpcode, st) := by
  have hn : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by scalar_tac
  simp [Body.step, hn, code.step_wasm2, code.step_extended, code.step_numeric, global_simps,
    code.sign_extension_type]

/-- The body `ff` of a function of type `[] -> []` is rejected with `UnrecognizedOpcode`. -/
theorem unknown_opcode_rejected (env : metadata.Env)
    (hi : env.types.val[0]? = some voidFunction) :
    code.bodyCore (bytes [0xFF#u8]) env (alloc.vec.Vec.new _) (alloc.vec.Vec.new _) 0#u32 =
      .ok (.Err .UnrecognizedOpcode) := by
  apply body_core_of_run _ env _ _ 0#u32 voidFunction _ hi (by simp [voidFunction])
    (by simp [voidFunction]) (by simp [bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
  exact run_error _ env _ 0#u32 _ _ 0xFF#u8 1#usize .UnrecognizedOpcode
    (by simp [Body.initial])
    (read_at _ _ _ _ (by simp [Body.initial, bytes, alloc.vec.Vec.deref]) rfl rfl)
    (step_unknown _ _ env _ 0#u32 (by simp [Body.initial]; scalar_tac))

end Itasca.Examples.BodySupport

end

/-! ## CodeEntryRejection -/

section

/-!
# A rejected code entry and the batch obligation

A code entry `02 00 ff` has a well-formed size and local declarations but an unknown opcode in its
body. `bad_body_entry_rejected` shows `metadata.validate_code_entry` reports `UnrecognizedOpcode`.
`bad_batch_validation_rejected` and `bad_batch_finish_rejected` show the streaming worker
`stream.CodeBatch.validate_func` records that error so `stream.CodeBatch.finish` rejects the batch,
and `tail_custom_preserves_work` shows a trailing custom section leaves the outstanding batch list
intact.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.Module.CodeEntryRejection

open Itasca.Examples.Module.Support (leb)

open Binary

private theorem one_room : 1 ≤ Usize.max := by scalar_tac

/-- A code entry of size 2 with no local declarations and the body byte `0xff`, an unknown
opcode. -/
def badBytes : Slice U8 := Examples.Module.Support.bytes [2#u8,0#u8,0xFF#u8]

/-- An environment with one function of type `[] -> []`. -/
def badEnv : metadata.Env :=
  { Examples.Module.Basic.emptyEnv with
    types := alloc.vec.Vec.from [Examples.BodySupport.voidFunction] (by simp; scalar_tac)
    func_type_indices := alloc.vec.Vec.from [0#u32] (by simp; scalar_tac)
    func_types := alloc.vec.Vec.from [Examples.BodySupport.voidFunction] (by simp; scalar_tac) }

private theorem bad_size : Binary.Leb128.Decoded badBytes 0#usize 2#u32 1#usize :=
  (show Body.Scalar.BytesAt badBytes 0#usize [2#u8] 1#usize by
    constructor <;> simp [badBytes, Examples.Module.Support.bytes, alloc.vec.Vec.deref]).u32_decoded _ (leb 2#u8)

private theorem bad_locals : metadata.decode_locals badBytes 1#usize =
    .ok (.Ok (alloc.vec.Vec.new _, 2#usize)) := by
  obtain ⟨locals, hl, hv⟩ := metadata.decode_locals.complete badBytes 1#usize [] 2#usize
    ⟨[0#u8], ⟨[0#u8], [], leb 0#u8, .nil, rfl⟩, by
      constructor <;> simp [badBytes, Examples.Module.Support.bytes, alloc.vec.Vec.deref]⟩
    (by simp [CodeEntry.Locals.declared, limits.MAX_LOCALS])
  have he : locals = alloc.vec.Vec.new _ := alloc.vec.Vec.ext _ _ (by simpa [CodeEntry.Locals.declared] using hv)
  simpa [he] using hl

private theorem bad_body_with : code.validate_body_with code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
    (Examples.BodySupport.bytes [0xFF#u8]) badEnv Examples.BodySupport.emptyContext 0#u32 () =
      .ok (.Err .UnrecognizedOpcode, ()) := by
  obtain ⟨⟨r, v⟩, hr⟩ := code.validate_body_with.total
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor Visitor.empty_total
    (Examples.BodySupport.bytes [0xFF#u8]) badEnv Examples.BodySupport.emptyContext 0#u32 ()
  have he := code.validate_body_with.eq_core (Examples.BodySupport.bytes [0xFF#u8]) badEnv
    Examples.BodySupport.emptyContext 0#u32
  rw [show Examples.BodySupport.emptyContext.locals = alloc.vec.Vec.new _ from rfl,
    show Examples.BodySupport.emptyContext.results = alloc.vec.Vec.new _ from rfl,
    Examples.BodySupport.unknown_opcode_rejected badEnv rfl, hr] at he
  cases v
  simp at he
  subst he
  exact hr

/-- `metadata.validate_code_entry` on `badBytes` returns `Body UnrecognizedOpcode`. -/
theorem bad_body_entry_rejected : metadata.validate_code_entry badBytes 0#usize badEnv 0#usize =
    .ok (.Err (.Body .UnrecognizedOpcode)) := by
  have hread := reader.read_u32_leb.complete badBytes 0#usize 2#u32 1#usize bad_size
  have htypes : badEnv.types.val = [Examples.BodySupport.voidFunction] := rfl
  have hfuncs : badEnv.func_type_indices.val = [0#u32] := rfl
  have hs : metadata.validate_code_entry badBytes 0#usize badEnv 0#usize ⦃ r =>
      r = .Err (.Body .UnrecognizedOpcode) ⦄ := by
    unfold metadata.validate_code_entry metadata.validate_code_entry_with
    simp [hfuncs, hread, core.result.Result.Insts.CoreOpsTry.branch]
    step as ⟨n, n_post⟩
    have hn : n = 2#usize := by scalar_tac
    rw [hn]
    rw [metadata.have_bytes.complete badBytes 1#usize 2#usize (by decide)]
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
    have hv1 : v1 = alloc.vec.Vec.new wasm_types.ValueType :=
      alloc.vec.Vec.ext _ _ (by simpa [Examples.BodySupport.voidFunction, alloc.vec.Vec.deref] using v1_post)
    subst v1
    step as ⟨v2, v2_post⟩
    have hv2 : v2 = alloc.vec.Vec.new wasm_types.ValueType :=
      alloc.vec.Vec.ext _ _ (by simpa [Examples.BodySupport.voidFunction, alloc.vec.Vec.deref] using v2_post)
    subst v2
    simp [code.OpVisitor.on_function_start.default]
    step as ⟨body, body_post, body_post1⟩ by simp [badBytes, Examples.Module.Support.bytes, alloc.vec.Vec.deref]
    have hb : body = Examples.BodySupport.bytes [0xFF#u8] one_room := by
      apply Slice.ext
      simpa [badBytes, Examples.Module.Support.bytes, Examples.BodySupport.bytes, alloc.vec.Vec.deref] using body_post
    rw [hb]
    have hh := bad_body_with
    simp only [Examples.BodySupport.emptyContext] at hh
    simp [hh]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

/-- An issued batch for module 0, batch 0, covering function 0 at code offset 0 of `badBytes`
under Wasm 2.0. -/
def badIssued : Stream.Batch.Issued := ⟨0#u64, 0#usize, badEnv, badBytes, 0#usize, 0#usize, 1#usize⟩

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
  obtain ⟨⟨r, v⟩, hr⟩ := metadata.validate_code_entry_with.total
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor Visitor.empty_total
    badBytes 0#usize badEnv 0#usize () bad_bounds
  cases v
  have he : r = .Err (.Body .UnrecognizedOpcode) := by
    simpa [metadata.validate_code_entry, hr] using bad_body_entry_rejected
  subst r
  have hz : (0#usize + 0#usize : Result Usize) = .ok 0#usize := by
    obtain ⟨n, hn, hv⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := 0#usize) (y := 0#usize) (by scalar_tac))
    have he : n = 0#usize := by apply UScalar.eq_of_val_eq; simpa using hv
    simpa [he] using hn
  refine ⟨{ badIssued.seed with error := some (.Body .UnrecognizedOpcode) }, ?_, rfl⟩
  simp [stream.CodeBatch.validate_func, stream.CodeBatch.validate_next,
    badIssued, Stream.Batch.Issued.seed, hr, hz, core.option.Option.is_none]

/-- After the worker fails, `stream.CodeBatch.finish` on the resulting batch returns the same
error. -/
theorem bad_batch_finish_rejected : ∃ after,
    stream.CodeBatch.validate_func code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      badIssued.seed 0#usize () = .ok (.Err (.Body .UnrecognizedOpcode), after, ()) ∧
    stream.CodeBatch.finish after = .ok (.Err (.Body .UnrecognizedOpcode)) := by
  obtain ⟨after, hr, he⟩ := bad_batch_validation_rejected
  exact ⟨after, hr, by simp [stream.CodeBatch.finish, he]⟩

/-- A trailing custom section with an empty name and no payload: `00 01 00`. -/
def tailBuffer : Slice U8 := Examples.Module.Support.bytes [0#u8,1#u8,0#u8]
/-- A tail with no data segments. -/
def emptyTail : metadata.Tail := ⟨alloc.vec.Vec.new _⟩

private theorem good_tail (env : metadata.Env) (hcount : env.data_count = none) :
    metadata.validate_tail tailBuffer 0#usize env = .ok (.Ok emptyTail) := by
  apply metadata.validate_tail.complete emptyTail
  · refine ⟨[0#u8,1#u8,0#u8], ?_, ?_⟩
    · refine ⟨[], [0#u8,1#u8,0#u8], ⟨[], [], .nil, .absent, rfl⟩, ?_, rfl⟩
      have hc : CustomEncoding [0#u8,1#u8,0#u8] := by
        refine ⟨[], [], [0#u8], ?_, ?_⟩
        · exact ⟨ByteVecEncoding.iff.mpr ⟨[0#u8], leb 0#u8, rfl⟩, .nil⟩
        · exact ⟨[1#u8], [0#u8], leb 1#u8, rfl, rfl⟩
      simpa using CustomsEncoding.cons hc CustomsEncoding.nil
    · constructor <;> simp [tailBuffer, Examples.Module.Support.bytes, alloc.vec.Vec.deref]
  · simp [emptyTail]
  · simp [hcount]

/-- A visitor whose custom-section callback leaves its state, here a list of issued batches,
unchanged. -/
def observeCustoms : metadata.ModuleVisitor (List Stream.Batch.Issued) where
  on_custom_section v _ := .ok (.Ok (), v)

private theorem observe_customs_accept : Module.Tail.HooksAccept observeCustoms := by
  intro v chunk
  exact ⟨v, rfl⟩

private theorem observe_customs_preserve : Module.Tail.Preserves observeCustoms id := by
  intro v chunk v' h
  simpa [observeCustoms, Eq.comm] using h

/-- Validating the trailing custom section with `observeCustoms` accepts and returns the
outstanding batch list `[badIssued]` unchanged. -/
theorem tail_custom_preserves_work (env : metadata.Env) (hcount : env.data_count = none) :
    metadata.validate_tail_with observeCustoms tailBuffer 0#usize env [badIssued] =
      .ok (.Ok emptyTail, [badIssued]) := by
  obtain ⟨v', hv⟩ := metadata.validate_tail_with.accepted_lift observeCustoms observe_customs_accept
    tailBuffer 0#usize env [badIssued] emptyTail (good_tail env hcount)
  have he := metadata.validate_tail_with.accepted_preserves observeCustoms id observe_customs_preserve
    tailBuffer 0#usize env [badIssued] emptyTail v' hv
  change v' = [badIssued] at he
  simpa only [he] using hv

end Itasca.Examples.Module.CodeEntryRejection

end
