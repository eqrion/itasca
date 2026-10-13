import Itasca.Handler.Control
import Itasca.Wasm1.SharedLoop
import Itasca.Binary.ReadByte

open Aeneas Aeneas.Std

namespace Itasca.Body

def initial (bt : code.BlockType) : code.OpIterState :=
  ⟨alloc.vec.Vec.new _,
    alloc.vec.Vec.from [⟨.Body, bt, Control.signature bt, 0#usize, false⟩] (by scalar_tac), 0#usize⟩

theorem initial_shape (bt : code.BlockType) : Control.Shape (initial bt) := by
  constructor <;> simp [initial]

theorem byte_limit_room : limits.MAX_FUNCTION_BYTES.val + 2 < Usize.max := by
  simp only [limits.MAX_FUNCTION_BYTES]
  scalar_tac

/-- Successful loop iterations preserve an invariant and advance through the
bounded input. Errors remain ordinary validator errors and need no invariant. -/
def StepContract {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (inv : V → code.OpIterState → Prop) : Prop :=
  ∀ st v, inv v st → st.ctrls.val ≠ [] → ∀ (hpos : st.pos.val < data.length)
    (next : Usize), next.val = st.pos.val + 1 →
    code.step visitor { st with pos := next } data env ctx data.val[st.pos.val] v ⦃ r =>
      r.1 = .Ok () → inv r.2.2 r.2.1 ∧
        next.val ≤ r.2.1.pos.val ∧ r.2.1.pos.val ≤ data.length ⦄

end Itasca.Body

namespace Itasca

theorem code.start_function.spec (results : Slice types.ValueType) (bt : code.BlockType)
    (hresults : results.val = Control.results bt) :
    code.start_function results = .ok (Body.initial bt) := by
  cases bt with
  | Empty =>
      simp only [Control.results] at hresults
      have hlen : Slice.len results = 0#usize := by scalar_tac
      simp [code.start_function, hlen, code.push_ctrl, Body.initial,
        alloc.vec.Vec.push, U32.max, U32.numBits]
      rfl
  | Value ty =>
      simp only [Control.results] at hresults
      have hlen : Slice.len results = 1#usize := by scalar_tac
      have hindex : Slice.index_usize results 0#usize = .ok ty := by
        obtain ⟨x, hx, heq⟩ := WP.spec_imp_exists
          (Slice.index_usize_spec results 0#usize (by simp [Slice.length, hresults]))
        have heq' : x = ty := by simpa [hresults] using heq
        exact heq' ▸ hx
      simp [code.start_function, hlen, hindex, code.push_ctrl, Body.initial,
        alloc.vec.Vec.push, U32.max, U32.numBits]
      rfl

theorem code.read_op.eof (st : code.OpIterState) (data : Slice U8)
    (h : data.length ≤ st.pos.val) :
    code.read_op st data = .ok (.Err .UnexpectedEof, st) := by
  simp [code.read_op, reader.read_byte.eof data st.pos h,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Termination and invariant induction for the Wasm 1.0 view of the shared
loop. `code.validate_body_with.eq_model` connects this view to the extracted
worker. The profile-specific step proof is an explicit parameter here. -/
theorem code.validate_body_with_loop.spec {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (inv : V → code.OpIterState → Prop) (post : V → Prop)
    (hstep : Body.StepContract visitor data env ctx inv)
    (hclosed : ∀ st v, inv v st → st.ctrls.val = [] →
      st.pos.val = data.length → post v)
    (v : V) (st : code.OpIterState) (hinv : inv v st) :
    code.validate_body_with_loop visitor data env ctx.locals ctx.results v st ⦃ r =>
      r.1 = .Ok () → post r.2 ⦄ := by
  unfold code.validate_body_with_loop
  apply loop.spec_decr_nat (fun s => data.length - s.2.pos.val)
    (fun s => inv s.1 s.2)
  · rintro ⟨v, st⟩ hi
    unfold code.validate_body_with_loop.body
    simp only [code.control_stack_empty, alloc.vec.Vec.is_empty, bind_ok]
    by_cases hc : st.ctrls.val = []
    · simp only [hc, List.isEmpty_nil, ↓reduceIte]
      split
      · rename_i hp
        simp only [WP.spec_ok]
        intro _
        apply hclosed st v hi hc
        have := congrArg UScalar.val hp
        simpa using this
      · simp [WP.spec_ok]
    · have hne : st.ctrls.val.isEmpty = false := by simpa using hc
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      by_cases hp : st.pos.val < data.length
      · obtain ⟨next, hr, hn⟩ := code.read_op_success st data hp
        rw [hr]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        obtain ⟨⟨r, st', v'⟩, hrun, hs⟩ := WP.spec_imp_exists (hstep st v hi hc hp next hn)
        dsimp only at hs
        cases r with
        | Err e =>
            simp [hrun,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok u =>
            cases u
            obtain ⟨hi', hge, hbound⟩ := hs rfl
            have hmeasure : data.length - st'.pos.val < data.length - st.pos.val := by omega
            simp [hrun]
            exact ⟨hi', by simpa only [Slice.length] using hmeasure⟩
      · rw [code.read_op.eof st data (by omega)]
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · exact hinv

/-- Lifts a profile's step invariant through initialization, the size guard,
and the public validator entry point. -/
theorem code.validate_body_with.spec {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt)
    (inv : V → code.OpIterState → Prop) (post : V → Prop)
    (hstep : Body.StepContract visitor data env ctx inv)
    (hclosed : ∀ st v, inv v st → st.ctrls.val = [] →
      st.pos.val = data.length → post v)
    (v : V) (hinit : data.length ≤ limits.MAX_FUNCTION_BYTES.val → inv v (Body.initial bt)) :
    code.validate_body_with visitor data env ctx v ⦃ r => r.1 = .Ok () → post r.2 ⦄ := by
  rw [code.validate_body_with.eq_model]
  unfold code.validate_body_with_model
  dsimp only
  split
  · simp [WP.spec_ok]
  · rename_i hsize
    rw [code.start_function.spec (alloc.vec.Vec.deref ctx.results) bt
      (by simpa [alloc.vec.Vec.deref] using hresults)]
    simp only [bind_ok]
    apply code.validate_body_with_loop.spec visitor data env ctx inv post hstep hclosed
    apply hinit
    scalar_tac

/-- The non-visiting public validator follows from the same checked loop. -/
theorem code.validate_body.spec
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt)
    (inv : code.OpIterState → Prop) (post : Prop)
    (hstep : Body.StepContract code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx (fun _ st => inv st))
    (hclosed : ∀ st, inv st → st.ctrls.val = [] → st.pos.val = data.length → post)
    (hinit : data.length ≤ limits.MAX_FUNCTION_BYTES.val → inv (Body.initial bt)) :
    code.validate_body data env ctx ⦃ r => r = .Ok () → post ⦄ := by
  obtain ⟨⟨res, v⟩, hr, hp⟩ := WP.spec_imp_exists
    (code.validate_body_with.spec code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx bt hresults (fun _ st => inv st) (fun _ => post)
      hstep (fun st _ => hclosed st) () hinit)
  simpa [code.validate_body, hr] using hp

end Itasca

namespace Itasca.Body

/-- Initialization mirrors the extracted implementation even for an arbitrary
caller-supplied result list. Soundness separately restricts Wasm 1.0 results. -/
def initialBlockType (results : List types.ValueType) : code.BlockType :=
  match results with
  | [t] => .Value t
  | _ => .Empty

theorem initialBlockType_results (bt : code.BlockType) :
    initialBlockType (Control.results bt) = bt := by
  cases bt <;> rfl

end Itasca.Body

namespace Itasca

theorem code.start_function.raw_spec (results : Slice types.ValueType) :
    code.start_function results = .ok (Body.initial (Body.initialBlockType results.val)) := by
  cases hv : results.val with
  | nil => simpa [Body.initialBlockType, hv] using code.start_function.spec results .Empty hv
  | cons t ts =>
    cases ts with
    | nil => simpa [Body.initialBlockType, hv] using code.start_function.spec results (.Value t) hv
    | cons u us =>
      have hlen : Slice.len results ≠ 1#usize := by scalar_tac
      simp [code.start_function, hlen, code.push_ctrl, Body.initial,
        Body.initialBlockType, alloc.vec.Vec.push, U32.max, U32.numBits]
      rfl

end Itasca
