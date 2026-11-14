import Itasca.Visitor.Events
import Itasca.Visitor.EventTables
import Itasca.Handler.EnvDispatch
import Itasca.Handler.Select
import Itasca.Visitor.Total
import Itasca.Support.Result
import Itasca.Binary.Wasm1.EncodingComplete
import Itasca.Visitor.RunTrace
import Itasca.Handler.RawControl
import Itasca.Binary.Leb128
import Itasca.Wasm2.Visitor.Step
import Itasca.Wasm2.Visitor.Total

/-!
Sections, each formerly its own module: EventDispatch, StepRefinement, TraceBytes, ReachedTableLabels, InvariantBodyLoop, ReaderAcceptedProgress, ReaderAcceptance, BodyReplay.
-/

/-! ## EventDispatch -/

section

/-!
# Step dispatch to events

The `VisitorTrace.dispatch_*` theorems restate the dispatch of `code.step` for every instruction
as `CoreVisitor.run` of its reader followed by `invoke` of the matching `Event`. Together with
`Visitor/EventTables` they let trace proofs treat each instruction step as reading its immediates
and then reporting one event. Covers the Wasm 1.0 instructions.
-/

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- `code.step` on `code.OP_NOP` reads no immediates and calls the hook for the `nop` event. -/
theorem dispatch_nop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_NOP v =
      CoreVisitor.run (.ok (.Ok (), st)) (fun v s _ => invoke visitor v (.op s (.nop))) v := by
  simpa only [invoke] using OpDispatch.dispatch_nop visitor st data env ctx v

/-- `code.step` on `code.OP_UNREACHABLE` runs `code.read_unreachable` and then calls the hook for
the `unreachable` event. -/
theorem dispatch_unreachable {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_UNREACHABLE v =
      CoreVisitor.run (code.read_unreachable st) (fun v s _ => invoke visitor v (.op s (.unreachable))) v := by
  simpa only [invoke] using OpDispatch.dispatch_unreachable visitor st data env ctx v

/-- `code.step` on `code.OP_DROP` runs `code.read_drop` and then calls the hook for the `drop`
event. -/
theorem dispatch_drop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_DROP v =
      CoreVisitor.run (code.read_drop st) (fun v s a => invoke visitor v (.op s (.drop a))) v := by
  simpa only [invoke] using OpDispatch.dispatch_drop visitor st data env ctx v

/-- `code.step` on `code.OP_I32_CONST` runs `code.read_i32_const` and then calls the hook for the
`i32_const` event. -/
theorem dispatch_i32_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I32_CONST v =
      CoreVisitor.run (code.read_i32_const st data) (fun v s a => invoke visitor v (.op s (.i32_const a))) v := by
  simpa only [invoke] using OpDispatch.dispatch_i32_const visitor st data env ctx v

/-- `code.step` on `code.OP_I64_CONST` runs `code.read_i64_const` and then calls the hook for the
`i64_const` event. -/
theorem dispatch_i64_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I64_CONST v =
      CoreVisitor.run (code.read_i64_const st data) (fun v s a => invoke visitor v (.op s (.i64_const a))) v := by
  simpa only [invoke] using OpDispatch.dispatch_i64_const visitor st data env ctx v

/-- `code.step` on `code.OP_F32_CONST` runs `code.read_f32_const` and then calls the hook for the
`f32_const` event. -/
theorem dispatch_f32_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F32_CONST v =
      CoreVisitor.run (code.read_f32_const st data) (fun v s a => invoke visitor v (.op s (.f32_const a))) v := by
  simpa only [invoke] using OpDispatch.dispatch_f32_const visitor st data env ctx v

/-- `code.step` on `code.OP_F64_CONST` runs `code.read_f64_const` and then calls the hook for the
`f64_const` event. -/
theorem dispatch_f64_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F64_CONST v =
      CoreVisitor.run (code.read_f64_const st data) (fun v s a => invoke visitor v (.op s (.f64_const a))) v := by
  simpa only [invoke] using OpDispatch.dispatch_f64_const visitor st data env ctx v

/-- `code.step` on `code.OP_SELECT` runs `code.read_select` and then calls the hook for the `select`
event. -/
theorem dispatch_select {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_SELECT v =
      CoreVisitor.run (code.read_select st) (fun v s a => invoke visitor v (.op s (.select a))) v :=
  code.step_select.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_LOCAL_GET` runs `code.read_local_get` and then calls the hook for the
`local_get` event. -/
theorem dispatch_local_get {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOCAL_GET v =
      CoreVisitor.run (code.read_local_get st data ctx) (fun v s a => invoke visitor v (.op s (.local_get a))) v :=
  code.step_local_get.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_LOCAL_SET` runs `code.read_local_set` and then calls the hook for the
`local_set` event. -/
theorem dispatch_local_set {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOCAL_SET v =
      CoreVisitor.run (code.read_local_set st data ctx) (fun v s a => invoke visitor v (.op s (.local_set a))) v :=
  code.step_local_set.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_LOCAL_TEE` runs `code.read_local_tee` and then calls the hook for the
`local_tee` event. -/
theorem dispatch_local_tee {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOCAL_TEE v =
      CoreVisitor.run (code.read_local_tee st data ctx) (fun v s a => invoke visitor v (.op s (.local_tee a))) v :=
  code.step_local_tee.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_GLOBAL_GET` runs `code.read_global_get` and then calls the hook for the
`global_get` event. -/
theorem dispatch_global_get {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_GLOBAL_GET v =
      CoreVisitor.run (code.read_global_get st data env) (fun v s a => invoke visitor v (.op s (.global_get a))) v :=
  code.step_global_get.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_GLOBAL_SET` runs `code.read_global_set` and then calls the hook for the
`global_set` event. -/
theorem dispatch_global_set {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_GLOBAL_SET v =
      CoreVisitor.run (code.read_global_set st data env) (fun v s a => invoke visitor v (.op s (.global_set a))) v :=
  code.step_global_set.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_MEMORY_SIZE` runs `code.read_memory_size` and then calls the hook for
the `memory_size` event. -/
theorem dispatch_memory_size {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_MEMORY_SIZE v =
      CoreVisitor.run (code.read_memory_size st data env) (fun v s _ => invoke visitor v (.op s (.memory_size))) v :=
  code.step_memory_size.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_MEMORY_GROW` runs `code.read_memory_grow` and then calls the hook for
the `memory_grow` event. -/
theorem dispatch_memory_grow {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_MEMORY_GROW v =
      CoreVisitor.run (code.read_memory_grow st data env) (fun v s _ => invoke visitor v (.op s (.memory_grow))) v :=
  code.step_memory_grow.dispatch visitor st data env ctx v

/-- A numeric opcode with a binary row and a callback runs `Numeric.read` and then reports the
numeric event of that callback. -/
theorem dispatch_numeric {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V)
    (opcode : U8) (operation : Numeric.Operation) (hook : NumericHook)
    (hrow : Numeric.opcodeMeaning opcode = some operation)
    (hhook : NumericHook.ofOpcode opcode = some hook) :
    code.step visitor st data env ctx opcode v =
      CoreVisitor.run (Numeric.read operation st)
        (fun v s (_ : Unit) => invoke visitor v (.op s (.numeric hook))) v := by
  rw [code.step.numeric_dispatch visitor st data env ctx opcode v (Numeric.NumericOp.bounds hrow).1,
    code.step_numeric.dispatch visitor st opcode operation v hrow]
  simp only [visit_numeric, hhook]

/-- A load or store opcode with a binary row and a callback runs `code.read_load` or
`code.read_store` and then reports the memory event of that callback. -/
theorem dispatch_memory {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V)
    (opcode : U8) (operation : MemoryMeaning.Operation) (hook : MemoryHook)
    (hrow : MemoryMeaning.opcodeMeaning opcode = some operation)
    (hhook : MemoryHook.ofOpcode opcode = some hook) :
    code.step visitor st data env ctx opcode v =
      CoreVisitor.run
        (if operation.store then code.read_store st data env operation.ty operation.naturalAlign
          else code.read_load st data env operation.ty operation.naturalAlign)
        (fun v s arg => invoke visitor v (.op s (.memory hook arg))) v := by
  rw [code.step_memory.dispatch visitor st data env ctx v opcode operation hrow]
  simp only [visit_memory, hhook]

end Itasca.VisitorTrace

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

end Itasca.VisitorTrace

end

/-! ## StepRefinement -/

section

/-!
# Refinement of an instruction step

`code.step.refines` lifts a `VisitorTrace.Refines` relation between two visitors to the whole
extracted `code.step`. `code.step.instrument_forward` and `code.step.instrument_backward` specialise
it to the recording wrapper `instrument`, so a step can be run with or without recording and
return the same result and validator state. Covers the Wasm 1.0 step `code.step`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open VisitorTrace

/-- A refinement of hooks lifts to `code.step` for every opcode. Every normal return, including
rejections and malformed instructions, is reproduced with the same result and validator state. -/
theorem code.step.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (opcode : U8) (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (st' : code.OpIterState) (v' : V)
    (h : code.step visitor st data env ctx opcode v = .ok (res, st', v')) :
    ∃ w', code.step replacement st data env ctx opcode w =
      .ok (res, st', w') ∧ related v' w' := by
  cases hn : Numeric.opcodeMeaning opcode with
  | some operation =>
    obtain ⟨hook, hhook, _, _⟩ := NumericHook.of_meaning hn
    rw [dispatch_numeric visitor st data env ctx v opcode operation hook hn hhook] at h
    rw [dispatch_numeric replacement st data env ctx w opcode operation hook hn hhook]
    exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
  | none =>
    cases hm : MemoryMeaning.opcodeMeaning opcode with
    | some operation =>
      obtain ⟨hook, hhook, _, _⟩ := MemoryHook.of_meaning hm
      rw [dispatch_memory visitor st data env ctx v opcode operation hook hm hhook] at h
      rw [dispatch_memory replacement st data env ctx w opcode operation hook hm hhook]
      exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
    | none =>
      by_cases h_nop : opcode = code.OP_NOP
      · subst opcode
        rw [dispatch_nop visitor st data env ctx v] at h
        rw [dispatch_nop replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_unreachable : opcode = code.OP_UNREACHABLE
      · subst opcode
        rw [dispatch_unreachable visitor st data env ctx v] at h
        rw [dispatch_unreachable replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_i32_const : opcode = code.OP_I32_CONST
      · subst opcode
        rw [dispatch_i32_const visitor st data env ctx v] at h
        rw [dispatch_i32_const replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_i64_const : opcode = code.OP_I64_CONST
      · subst opcode
        rw [dispatch_i64_const visitor st data env ctx v] at h
        rw [dispatch_i64_const replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_f32_const : opcode = code.OP_F32_CONST
      · subst opcode
        rw [dispatch_f32_const visitor st data env ctx v] at h
        rw [dispatch_f32_const replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_f64_const : opcode = code.OP_F64_CONST
      · subst opcode
        rw [dispatch_f64_const visitor st data env ctx v] at h
        rw [dispatch_f64_const replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_drop : opcode = code.OP_DROP
      · subst opcode
        rw [dispatch_drop visitor st data env ctx v] at h
        rw [dispatch_drop replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_select : opcode = code.OP_SELECT
      · subst opcode
        rw [dispatch_select visitor st data env ctx v] at h
        rw [dispatch_select replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_local_get : opcode = code.OP_LOCAL_GET
      · subst opcode
        rw [dispatch_local_get visitor st data env ctx v] at h
        rw [dispatch_local_get replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_local_set : opcode = code.OP_LOCAL_SET
      · subst opcode
        rw [dispatch_local_set visitor st data env ctx v] at h
        rw [dispatch_local_set replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
      · subst opcode
        rw [dispatch_local_tee visitor st data env ctx v] at h
        rw [dispatch_local_tee replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_global_get : opcode = code.OP_GLOBAL_GET
      · subst opcode
        rw [dispatch_global_get visitor st data env ctx v] at h
        rw [dispatch_global_get replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_global_set : opcode = code.OP_GLOBAL_SET
      · subst opcode
        rw [dispatch_global_set visitor st data env ctx v] at h
        rw [dispatch_global_set replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
      · subst opcode
        rw [dispatch_memory_size visitor st data env ctx v] at h
        rw [dispatch_memory_size replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
      · subst opcode
        rw [dispatch_memory_grow visitor st data env ctx v] at h
        rw [dispatch_memory_grow replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      have heqval (a b : U8) : a = b ↔ a.val = b.val :=
        ⟨fun h => congrArg UScalar.val h, UScalar.eq_of_val_eq⟩
      have hdispatch {W : Type} (hooks : code.OpVisitor W) (w : W) :
          code.step hooks st data env ctx opcode w = code.step_memory hooks st data env opcode w := by
        unfold code.step
        split <;> simp_all [global_simps, U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]
      rw [hdispatch visitor v] at h
      rw [hdispatch replacement w]
      rw [OpDispatch.memory_fallback visitor st data env opcode v hm h_memory_size h_memory_grow,
        code.step_numeric.unrecognized visitor st opcode v hn] at h
      rw [OpDispatch.memory_fallback replacement st data env opcode w hm h_memory_size h_memory_grow,
        code.step_numeric.unrecognized replacement st opcode w hn]
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨w, rfl, hrelated⟩

end Itasca

end

/-! ## TraceBytes -/

section

/-!
# Callback traces and byte provenance

Describes callback traces without mentioning the extracted code. `LabelsAt` and `PartialTable`
relate the label callbacks of an unfinished `br_table` to the bytes they decode, and `Outcomes`
relates observations to the validator result.
-/

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- The result of validating an instruction or a body. -/
abbrev BodyResult := core.result.Result Unit error.OpError

/-- Converts a callback reply to a validator result: a rejection becomes `OpError.Visitor`. -/
def outcome : VisitResult → BodyResult
  | .Ok () => .Ok ()
  | .Err e => .Err (.Visitor e)

/-- Every observation in the list was accepted. -/
def AllAccepted (observations : List Observation) : Prop :=
  ∀ observation ∈ observations, observation.outcome = .Ok ()

theorem AllAccepted.append {xs ys} (hx : AllAccepted xs) (hy : AllAccepted ys) :
    AllAccepted (xs ++ ys) := by
  intro o ho
  exact (List.mem_append.mp ho).elim (hx o) (hy o)

/-- The observations are consistent with a result. A success has only accepted callbacks. A visitor
error is either the reply of a rejecting last callback that follows accepted ones, or follows only
accepted callbacks. Any other error follows only accepted callbacks. -/
def Outcomes (observations : List Observation) : BodyResult → Prop
  | .Ok () => AllAccepted observations
  | .Err (.Visitor e) => AllAccepted observations ∨ ∃ before event,
      observations = before ++ [⟨event, .Err e⟩] ∧ AllAccepted before
  | .Err _ => AllAccepted observations

theorem Outcomes.of_accepted {observations} (h : AllAccepted observations) (result : BodyResult) :
    Outcomes observations result := by
  cases result with
  | Ok u => cases u; exact h
  | Err e => cases e <;> first | exact h | exact Or.inl h

theorem Outcomes.empty (result : BodyResult) : Outcomes [] result :=
  .of_accepted (by simp [AllAccepted]) result

theorem Outcomes.single (event : Event) (reply : VisitResult) :
    Outcomes [⟨event, reply⟩] (outcome reply) := by
  cases reply with
  | Ok u => cases u; simp [Outcomes, outcome, AllAccepted]
  | Err e => exact Or.inr ⟨[], event, rfl, by simp [AllAccepted]⟩

theorem Outcomes.prepend {before observations result}
    (hp : AllAccepted before) (h : Outcomes observations result) :
    Outcomes (before ++ observations) result := by
  cases result with
  | Ok u => cases u; exact hp.append h
  | Err e =>
      cases e <;> try (exact hp.append h)
      rcases h with h | h
      · exact Or.inl (hp.append h)
      obtain ⟨xs, event, rfl, hb⟩ := h
      exact Or.inr ⟨before ++ xs, event, by simp [List.append_assoc], hp.append hb⟩

/-- The observations of the `br_table` vector entries, with their label depths in order and the
byte cursor after each entry. The relation is defined by the binary encoding alone. -/
inductive LabelsAt (data : Slice U8) : Usize → List Observation → List U32 → Usize → Prop where
  | nil (pos : Usize) : LabelsAt data pos [] [] pos
  | cons {pos depth st reply observations depths last} :
      Leb128.Decoded data pos depth st.pos →
      LabelsAt data st.pos observations depths last →
      LabelsAt data pos (⟨.op st (.br_table_label depth), reply⟩ :: observations)
        (depth :: depths) last

/-- The callbacks of a `br_table` that stopped before its closing callback. They cover some or all
of the vector entries, including an entry whose target merge failed after its callback ran. -/
def PartialTable (data : Slice U8) (start : Usize) (observations : List Observation) : Prop :=
  ∃ pos count first depths last,
    Wasm1.BytesAt data start [0x0E#u8] pos ∧
    Leb128.Decoded data pos count first ∧
    LabelsAt data first observations depths last ∧ depths.length ≤ count.val

end Itasca.VisitorTrace

end

/-! ## ReachedTableLabels -/

section

namespace Itasca
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

end Itasca

end

/-! ## InvariantBodyLoop -/

section

namespace Itasca
open Aeneas Aeneas.Std

namespace ReachedBody
/-- Only the reader/visitor pairs actually retained by the prefix invariant
must return. Bytes may be malformed, and a callback may reject normally. -/
def StepTotalOn {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (typeIndex : U32)
    (inv : V → code.BodyState → Prop) : Prop :=
  ∀ (st : code.BodyState) (v : V), inv v st → st.core.ctrls.val ≠ [] →
    ∀ (inbounds : st.core.pos.val < data.length) (next : Usize), next.val = st.core.pos.val + 1 →
      code.step_profile visitor {core := {st.core with pos := next}} data env ctx typeIndex
        data.val[st.core.pos.val] v ⦃ out => out.1 = .Ok () →
          inv out.2.2 out.2.1 ∧ next.val ≤ out.2.1.core.pos.val ⦄
end ReachedBody

/-- The actual common body loop returns from normal reader steps at reached
states. Its termination measure uses the concrete byte cursor, independently of
source validity or callback behavior at unreachable states. -/
theorem code.body_loop_loop.total_on {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (typeIndex : U32)
     (inv : V → code.BodyState → Prop) (post : V → Prop)
    (steps : ReachedBody.StepTotalOn visitor data env ctx typeIndex inv)
    (closed : ∀ st v, inv v st → st.core.ctrls.val = [] → st.core.pos.val = data.length → post v)
    (v : V) (st : code.BodyState) (initial : inv v st) :
    code.body_loop_loop visitor data env ctx typeIndex v st ⦃ out =>
      out.1 = .Ok () → post out.2 ⦄ := by
  unfold code.body_loop_loop
  apply loop.spec_decr_nat (fun state => Usize.max - state.2.core.pos.val)
    (fun state => inv state.1 state.2)
  · rintro ⟨v,st⟩ held
    unfold code.body_loop_loop.body
    simp only [alloc.vec.Vec.is_empty,bind_ok]
    by_cases empty : st.core.ctrls.val = []
    · simp only [empty,List.isEmpty_nil,↓reduceIte]
      split
      · simp
      · rename_i atEnd
        simp only [WP.spec_ok]
        intro _
        apply closed st v held empty
        simpa using atEnd
    · have nonempty : st.core.ctrls.val.isEmpty = false := by simpa using empty
      simp only [nonempty,Bool.false_eq_true,↓reduceIte]
      by_cases inbounds : st.core.pos.val < data.length
      · obtain ⟨result,read,next,resultEq,advance⟩ := WP.spec_imp_exists
          (reader.read_byte.spec data st.core.pos inbounds)
        rw [resultEq] at read
        rw [read]
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
        obtain ⟨⟨status,after,visitorAfter⟩,run,retained⟩ := WP.spec_imp_exists
          (steps st v held empty inbounds next advance)
        rw [run]
        cases status with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok acceptedUnit =>
          cases acceptedUnit
          obtain ⟨fresh,forward⟩ := retained rfl
          simp only [Std.uncurry,bind_ok,WP.spec_ok]
          refine ⟨fresh, ?_⟩
          dsimp only at forward
          have bound : after.core.pos.val ≤ Usize.max := by scalar_tac
          omega
      · rw [reader.read_byte.eof data st.core.pos (by omega)]
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · exact initial

/-- The outer size guard and initialization preserve the reached-state loop
contract. Initialization errors and oversized bodies return without callbacks. -/
theorem code.validate_body_with.total_on {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (typeIndex : U32)
     (inv : V → code.BodyState → Prop) (post : V → Prop)
    (v : V)
    (initialization : code.initial_state env typeIndex ⦃ result =>
      ∀ st, result = .Ok st → inv v st ⦄)
    (steps : ReachedBody.StepTotalOn visitor data env ctx typeIndex inv)
    (closed : ∀ st v, inv v st → st.core.ctrls.val = [] → st.core.pos.val = data.length → post v) :
    code.validate_body_with visitor data env ctx typeIndex v ⦃ out =>
      out.1 = .Ok () → post out.2 ⦄ := by
  unfold code.validate_body_with
  dsimp only
  split
  · simp
  · obtain ⟨result,started,held⟩ := WP.spec_imp_exists initialization
    rw [started]
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok st =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,code.body_loop]
      exact code.body_loop_loop.total_on visitor data env ctx typeIndex inv post
        steps closed v st (held st rfl)
end Itasca

end

/-! ## ReaderAcceptedProgress -/

section

namespace Itasca
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000

/-- The accepted reader advances the concrete cursor even when later bytes are malformed. Only
the reached raw control geometry is needed. -/
theorem code.step_profile.accepted_progress {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (typeIndex : U32)

    (st final : code.BodyState) (value after : V)
    (dataBound : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (shape : Control.Shape st.core)
    (blocks : st.blocks.val.length = st.core.ctrls.val.length)
    (controlBound : st.blocks.val.length ≤ st.core.pos.val+1)
    (nonempty : st.core.ctrls.val ≠ []) (inbounds : st.core.pos.val<data.length)
    (next : Usize) (advance : next.val=st.core.pos.val+1)
    (accepted : code.step_profile visitor ⟨{st.core with pos:=next}⟩ data env ctx typeIndex
      data.val[st.core.pos.val] value = .ok (.Ok (),final,after)) :
    next.val ≤ final.core.pos.val := by
  obtain ⟨unitValue,erased⟩ := Wasm2.Visitor.step_transfer visitor
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts
    data env ctx ctx rfl typeIndex data.val[st.core.pos.val]
    ⟨{st.core with pos:=next}⟩ final value () after accepted
  cases unitValue
  obtain ⟨result,read,position,equal,positionEq⟩ := WP.spec_imp_exists
    (reader.read_byte.spec data st.core.pos inbounds)
  have same : position=next := UScalar.eq_of_val_eq (by omega)
  subst position
  rw [equal] at read
  have body : code.body_loop_loop.body code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx typeIndex () st = .ok (.cont ((),final)) := by
    have nonemptyBool : st.core.ctrls.val.isEmpty=false := by simpa using nonempty
    simp [code.body_loop_loop.body,alloc.vec.Vec.is_empty,nonemptyBool,read,
      core.result.Result.Insts.CoreOpsTry.branch,erased]
  have checked := code.body_loop_loop.body.total
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total
    data env ctx typeIndex st () dataBound shape blocks controlBound
  rw [body,WP.spec_ok] at checked
  have progress := checked.2
  have bound : final.core.pos.val≤Usize.max := by scalar_tac
  dsimp only at progress
  omega
end Itasca

end

/-! ## ReaderAcceptance -/

section

/-!
Replay a successful reader with a replacement callback at the actual decoded state.
The replacement supplies its own postcondition; acceptance at unrelated states is
not required. Compiler capacity proofs instantiate these visitor-only lemmas.
-/

namespace Itasca.CoreVisitor
open Aeneas Aeneas.Std VisitorTrace

/-- A source-validated scalar reader output and an available actual callback
produce ordinary acceptance with the exact reader state. -/
theorem run.available_of_read {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (VisitResult × V))
    (before : V) (value : A) (final : code.OpIterState) (post : V → Prop)
    (readCalled : read = .ok (.Ok value,final))
    (accepts : hook before final value ⦃ out => out.1 = .Ok () ∧ post out.2 ⦄) :
    run read hook before ⦃ out => out.1 = .Ok () ∧ out.2.1 = final ∧ post out.2.2 ⦄ := by
  obtain ⟨⟨reply,after⟩,called,accepted,held⟩ := WP.spec_imp_exists accepts
  dsimp only at accepted held
  subst reply
  refine WP.exists_imp_spec ⟨(.Ok (),final,after),?_,rfl,rfl,held⟩
  exact (run.returned_iff _ _ _ _ _ _).mpr (Or.inr ⟨value,.Ok (),readCalled,called,rfl⟩)

/-- An independently accepted reference reader/hook run transfers to a
replacement that accepts the actual reader result. No acceptance at unrelated
reader outputs or unreachable visitor states is required. -/
theorem run.accepted_lift_on {A V W : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (sourceHook : V → code.OpIterState → A → Result (VisitResult × V))
    (targetHook : W → code.OpIterState → A → Result (VisitResult × W))
    (sourceBefore sourceAfter : V) (targetBefore : W) (final : code.OpIterState)
    (post : W → Prop)
    (reference : run read sourceHook sourceBefore = .ok (.Ok (),final,sourceAfter))
    (accepts : ∀ a, read = .ok (.Ok a,final) →
      sourceHook sourceBefore final a = .ok (.Ok (),sourceAfter) →
      targetHook targetBefore final a ⦃ out => out.1 = .Ok () ∧ post out.2 ⦄) :
    run read targetHook targetBefore ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = final ∧ post out.2.2 ⦄ := by
  obtain ⟨value, readCalled, sourceCalled⟩ := run.accepted _ _ _ _ _ reference
  exact run.available_of_read read targetHook targetBefore value final post readCalled
    (accepts value readCalled sourceCalled)

end Itasca.CoreVisitor

end

/-! ## BodyReplay -/

section

/-!
Replay an independently accepted body through reached-step callback obligations.
The source suffix supplies validation evidence; the target must construct actual
success, including cursor progress and the final closed state, for either profile.
-/
namespace Itasca
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ReachedBody

/-- A refinement may inspect the independent accepted suffix, for example to
bound the sizes of all remaining source observations. This supplies source
validation evidence only, never an accepted target run. -/
def AcceptingSuffixRefinement {V W : Type} (source : code.OpVisitor V) (target : code.OpVisitor W)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (typeIndex : U32)
     (final : V) (related : code.BodyState → V → W → Prop) : Prop :=
  ∀ st v w, related st v w →
    code.body_loop_loop source data env ctx typeIndex v st = .ok (.Ok (),final) →
    st.core.ctrls.val ≠ [] →
    ∀ (inbounds : st.core.pos.val < data.length) (next : Usize), next.val = st.core.pos.val+1 →
    ∀ out middle, code.step_profile source {core := {st.core with pos := next}} data env ctx typeIndex
      data.val[st.core.pos.val] v = .ok (.Ok (),out,middle) →
    code.step_profile target {core := {st.core with pos := next}} data env ctx typeIndex
      data.val[st.core.pos.val] w ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        related out middle result.2.2 ∧ next.val ≤ out.core.pos.val ⦄
end ReachedBody

/-- Isolate the independently accepted suffix after a reached step. The
byte read and source step are the actual extracted loop operations. -/
theorem code.body_loop_loop.accepted_tail {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (typeIndex : U32) (st out : code.BodyState)
    (before middle final : V) (nonempty : st.core.ctrls.val ≠ [])
    (inbounds : st.core.pos.val < data.length) (next : Usize)
    (advance : next.val = st.core.pos.val+1)
    (called : code.step_profile visitor {core := {st.core with pos := next}} data env ctx typeIndex
      data.val[st.core.pos.val] before = .ok (.Ok (),out,middle))
    (reference : code.body_loop_loop visitor data env ctx typeIndex before st = .ok (.Ok (),final)) :
    code.body_loop_loop visitor data env ctx typeIndex middle out = .ok (.Ok (),final) := by
  obtain ⟨result,read,position,resultEq,positionEq⟩ := WP.spec_imp_exists
    (reader.read_byte.spec data st.core.pos inbounds)
  have same : position = next := UScalar.eq_of_val_eq (by omega)
  subst position
  rw [resultEq] at read
  have nonemptyBool : st.core.ctrls.val.isEmpty = false := by simpa using nonempty
  unfold code.body_loop_loop at reference ⊢
  rw [loop] at reference
  simpa [code.body_loop_loop.body,alloc.vec.Vec.is_empty,nonemptyBool,read,called,
    core.result.Result.Insts.CoreOpsTry.branch,Std.bind_assoc,Std.uncurry] using reference

/-- Replay an independently accepted reference body through reached-state
acceptance proofs. Both complete profiles use this actual common extracted
loop. The theorem assumes neither target body success nor a target trace. -/
theorem code.body_loop_loop.accepted_suffix_replay_on {V W : Type}
    (source : code.OpVisitor V) (target : code.OpVisitor W)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (typeIndex : U32)
     (related : code.BodyState → V → W → Prop)
    (final : V)
    (stepRefinement : ReachedBody.AcceptingSuffixRefinement source target data env ctx typeIndex final related)
    (st : code.BodyState) (v : V) (w : W) (initial : related st v w)
    (reference : code.body_loop_loop source data env ctx typeIndex v st = .ok (.Ok (),final)) :
    code.body_loop_loop target data env ctx typeIndex w st ⦃ result =>
      result.1 = .Ok () ∧ ∃ closed, related closed final result.2 ∧
        closed.core.ctrls.val = [] ∧ closed.core.pos = Slice.len data ⦄ := by
  generalize measure : Usize.max-st.core.pos.val = remaining
  induction remaining using Nat.strong_induction_on generalizing st v w with
  | h remaining ih =>
    have suffix := reference
    unfold code.body_loop_loop at reference ⊢
    rw [loop] at reference ⊢
    simp only [code.body_loop_loop.body,alloc.vec.Vec.is_empty,bind_ok] at reference ⊢
    by_cases empty : st.core.ctrls.val = []
    · simp only [empty,List.isEmpty_nil,↓reduceIte] at reference ⊢
      by_cases finished : st.core.pos = Slice.len data
      · simp [finished] at reference ⊢
        subst final
        exact ⟨st,initial,empty,finished⟩
      · simp [finished] at reference
    · have nonempty : st.core.ctrls.val.isEmpty = false := by simpa using empty
      simp only [nonempty,Bool.false_eq_true,↓reduceIte] at reference ⊢
      by_cases inbounds : st.core.pos.val < data.length
      · obtain ⟨result,read,next,resultEq,advance⟩ := WP.spec_imp_exists
          (reader.read_byte.spec data st.core.pos inbounds)
        rw [resultEq] at read
        rw [read] at reference ⊢
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.bind_assoc,Std.uncurry] at reference ⊢
        obtain ⟨⟨status,out,middle⟩,called,tail⟩ := ResultFacts.bind_ok_inv _ _ _ reference
        cases status with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
        | Ok unit =>
          cases unit
          obtain ⟨⟨status,targetOut,targetAfter⟩,targetCalled,accepted,same,held,progress⟩ := WP.spec_imp_exists
            (stepRefinement st v w initial suffix empty inbounds next advance out middle called)
          dsimp only at accepted same held progress
          subst status targetOut
          rw [targetCalled]
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
          have smaller : Usize.max-out.core.pos.val < remaining := by
            have maximum := out.core.pos.hmax
            scalar_tac
          have tail' : code.body_loop_loop source data env ctx typeIndex middle out = .ok (.Ok (),final) := by
            simpa [code.body_loop_loop,code.body_loop_loop.body,alloc.vec.Vec.is_empty,Std.bind_assoc,Std.uncurry,
              core.result.Result.Insts.CoreOpsTry.branch] using tail
          simpa [code.body_loop_loop,code.body_loop_loop.body,alloc.vec.Vec.is_empty,Std.bind_assoc,Std.uncurry,
            core.result.Result.Insts.CoreOpsTry.branch] using
            ih _ smaller out middle targetAfter held tail' rfl
      · rw [reader.read_byte.eof data st.core.pos (by omega)] at reference
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at reference

/-- Lift reached-step acceptance through the actual size check and the shared,
visitor-independent initial-state construction. The reference may be the
validator's accepting recorder; no successful target run is assumed. -/
theorem code.validate_body_with.accepted_suffix_replay_on {V W : Type}
    (source : code.OpVisitor V) (target : code.OpVisitor W)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (typeIndex : U32)
     (related : code.BodyState → V → W → Prop)
    (final : V)
    (stepRefinement : ReachedBody.AcceptingSuffixRefinement source target data env ctx typeIndex final related)
    (v : V) (w : W)
    (initial : ∀ st, code.initial_state env typeIndex = .ok (.Ok st) → related st v w)
    (reference : code.validate_body_with source data env ctx typeIndex v =
      .ok (.Ok (),final)) :
    code.validate_body_with target data env ctx typeIndex w ⦃ result =>
      result.1 = .Ok () ∧ ∃ closed, related closed final result.2 ∧
        closed.core.ctrls.val = [] ∧ closed.core.pos = Slice.len data ⦄ := by
  unfold code.validate_body_with at reference ⊢
  dsimp only at reference ⊢
  split at reference
  · simp at reference
  · rename_i size
    rw [if_neg size]
    obtain ⟨status,started,tail⟩ := ResultFacts.bind_ok_inv _ _ _ reference
    cases status with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
    | Ok st =>
      rw [started]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      apply code.body_loop_loop.accepted_suffix_replay_on source target data env ctx typeIndex related final
        stepRefinement st v w (initial st started)
      simpa [core.result.Result.Insts.CoreOpsTry.branch,code.body_loop] using tail

end Itasca

end
