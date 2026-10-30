import Itasca.Main

/-!
# Shared helpers for body examples

Lemmas that run the extracted body loop of either profile one opcode at a time with the empty
visitor: `run_step` continues after an accepted step, `run_error` stops at a rejected step,
`run_filtered` stops at an opcode outside the profile, and `bodyCore_of_run` connects a run from
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
theorem bodyCore_of_run (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (locals results : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (result : core.result.Result Unit error.OpError)
    (hi : env.types.val[index.val]? = some ft)
    (hparams : ft.params.val.length ≤ 1000) (hresults : ft.results.val.length ≤ 1000)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hrun : Wasm2.run data env profile ⟨locals, results⟩ index (Wasm2.initial index) = .ok result) :
    code.bodyCore data env locals results index profile = .ok result := by
  have hb : index.val < env.types.val.length := List.getElem?_eq_some_iff.mp hi |>.1
  suffices hs : code.bodyCore data env locals results index profile ⦃ r => r = result ⦄ by
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
      change Wasm2.run data env profile ⟨locals, results⟩ index (Wasm2.initial index) ⦃ r => r = result ⦄
      simp [hrun]

/-- An accepted step continues the loop from the step's state. -/
theorem run_step (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (ctx : code.Context) (index : U32) (st next : code.BodyState) (opcode : U8) (pos : Usize)
    (hc : st.blocks.val ≠ [])
    (hr : reader.read_byte data st.core.pos = .ok (.Ok (opcode, pos)))
    (ho : code.check_opcode profile opcode = .ok (.Ok ()))
    (hs : Wasm2.step { st with core := { st.core with pos := pos } } data env profile ctx index
      opcode = .ok (.Ok (), next)) :
    Wasm2.run data env profile ctx index st = Wasm2.run data env profile ctx index next :=
  (Wasm2.Execution.single hc hr ho hs).loop_eq

/-- A rejected step ends the loop with the step's error. -/
theorem run_error (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (ctx : code.Context) (index : U32) (st next : code.BodyState) (opcode : U8) (pos : Usize)
    (e : error.OpError) (hc : st.blocks.val ≠ [])
    (hr : reader.read_byte data st.core.pos = .ok (.Ok (opcode, pos)))
    (ho : code.check_opcode profile opcode = .ok (.Ok ()))
    (hs : Wasm2.step { st with core := { st.core with pos := pos } } data env profile ctx index
      opcode = .ok (.Err e, next)) :
    Wasm2.run data env profile ctx index st = .ok (.Err e) := by
  rw [Wasm2.run_unfold, Wasm2.loopBody_eq]
  have hc' : st.core.ctrls.val ≠ [] := by simpa using hc
  simp [hc', hr, ho, hs, Wasm2.continueStep]

/-- An opcode outside the profile ends the loop with the filter's error. -/
theorem run_filtered (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (ctx : code.Context) (index : U32) (st : code.BodyState) (opcode : U8) (pos : Usize)
    (e : error.OpError) (hc : st.blocks.val ≠ [])
    (hr : reader.read_byte data st.core.pos = .ok (.Ok (opcode, pos)))
    (ho : code.check_opcode profile opcode = .ok (.Err e)) :
    Wasm2.run data env profile ctx index st = .ok (.Err e) := by
  rw [Wasm2.run_unfold, Wasm2.loopBody_eq]
  have hc' : st.core.ctrls.val ≠ [] := by simpa using hc
  simp [hc', hr, ho]

/-- Reading an in-bounds byte returns it and advances the cursor by one. -/
theorem read_at (data : Slice U8) (pos next : Usize) (opcode : U8)
    (hp : pos.val < data.length) (hn : next.val = pos.val + 1)
    (hb : data.val[pos.val] = opcode) :
    reader.read_byte data pos = .ok (.Ok (opcode, next)) := by
  obtain ⟨r, hr, p, rfl, hq⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
  have heq : p = next := UScalar.eq_of_val_eq (hq.trans hn.symm)
  simpa [heq, hb] using hr

/-- The byte `0xff` is no opcode in either profile. -/
theorem step_unknown (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (profile : ValidationProfile) (ctx : code.Context) (index : U32)
    (h : st.core.vals.val.length < Usize.max) :
    Wasm2.step st data env profile ctx index 0xFF#u8 = .ok (.Err .UnrecognizedOpcode, st) := by
  have hn : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by scalar_tac
  simp [Wasm2.step, hn, code.step_wasm2, code.step_extended, code.step_numeric, global_simps,
    code.sign_extension_type]

/-- The body `ff` of a function of type `[] -> []` is rejected with `UnrecognizedOpcode`. -/
theorem unknown_opcode_rejected (env : metadata.Env) (profile : ValidationProfile)
    (hi : env.types.val[0]? = some voidFunction) :
    code.bodyCore (bytes [0xFF#u8]) env (alloc.vec.Vec.new _) (alloc.vec.Vec.new _) 0#u32 profile =
      .ok (.Err .UnrecognizedOpcode) := by
  apply bodyCore_of_run _ env profile _ _ 0#u32 voidFunction _ hi (by simp [voidFunction])
    (by simp [voidFunction]) (by simp [bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
  exact run_error _ env profile _ 0#u32 _ _ 0xFF#u8 1#usize .UnrecognizedOpcode
    (by simp [Wasm2.initial])
    (read_at _ _ _ _ (by simp [Wasm2.initial, bytes, alloc.vec.Vec.deref]) rfl rfl)
    (code.check_opcode.complete profile _ (by decide))
    (step_unknown _ _ env profile _ 0#u32 (by simp [Wasm2.initial]; scalar_tac))

end Itasca.Examples.BodySupport
