import Itasca.Results.Definitions.Visitor
import Itasca.Visitor.RunTrace
import Itasca.Visitor.EventTables
import Itasca.Handler.ScalarCompleteness
import Itasca.Handler.ScalarOperations
import Itasca.Visitor.Total
import Itasca.Support.Translation
import Itasca.Binary.Scalar.Encoding
import Itasca.Binary.LebReaders
import Itasca.Body.Visitor.BrTable

/-!
# Body Replay

Dispatched callback events refine source steps and exact bytes.
-/

/-! ## EventDispatch -/

section

/-!
# Step dispatch to events

The `Visitor.Trace.dispatch_*` theorems restate the dispatch of `code.step` for every instruction
as `Visitor.Core.run` of its reader followed by `invoke` of the matching `Event`. Together with
`Visitor/EventTables` they let trace proofs treat each instruction step as reading its immediates
and then reporting one event. Covers the scalar instructions.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor.Trace

/-- `code.step` on `code.OP_NOP` reads no immediates and calls the hook for the `nop` event. -/
theorem dispatch_nop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_NOP v =
      Visitor.Core.run (.ok (.Ok (), st)) (fun v s _ => invoke visitor v (.op s (.nop))) v := by
  simpa only [invoke] using Visitor.Dispatch.dispatch_nop visitor st data env ctx v

/-- `code.step` on `code.OP_UNREACHABLE` runs `code.read_unreachable` and then calls the hook for
the `unreachable` event. -/
theorem dispatch_unreachable {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_UNREACHABLE v =
      Visitor.Core.run (code.read_unreachable st) (fun v s _ => invoke visitor v (.op s (.unreachable))) v := by
  simpa only [invoke] using Visitor.Dispatch.dispatch_unreachable visitor st data env ctx v

/-- `code.step` on `code.OP_DROP` runs `code.read_drop` and then calls the hook for the `drop`
event. -/
theorem dispatch_drop {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_DROP v =
      Visitor.Core.run (code.read_drop st) (fun v s a => invoke visitor v (.op s (.drop a))) v := by
  simpa only [invoke] using Visitor.Dispatch.dispatch_drop visitor st data env ctx v

/-- `code.step` on `code.OP_I32_CONST` runs `code.read_i32_const` and then calls the hook for the
`i32_const` event. -/
theorem dispatch_i32_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I32_CONST v =
      Visitor.Core.run (code.read_i32_const st data) (fun v s a => invoke visitor v (.op s (.i32_const a))) v := by
  simpa only [invoke] using Visitor.Dispatch.dispatch_i32_const visitor st data env ctx v

/-- `code.step` on `code.OP_I64_CONST` runs `code.read_i64_const` and then calls the hook for the
`i64_const` event. -/
theorem dispatch_i64_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I64_CONST v =
      Visitor.Core.run (code.read_i64_const st data) (fun v s a => invoke visitor v (.op s (.i64_const a))) v := by
  simpa only [invoke] using Visitor.Dispatch.dispatch_i64_const visitor st data env ctx v

/-- `code.step` on `code.OP_F32_CONST` runs `code.read_f32_const` and then calls the hook for the
`f32_const` event. -/
theorem dispatch_f32_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F32_CONST v =
      Visitor.Core.run (code.read_f32_const st data) (fun v s a => invoke visitor v (.op s (.f32_const a))) v := by
  simpa only [invoke] using Visitor.Dispatch.dispatch_f32_const visitor st data env ctx v

/-- `code.step` on `code.OP_F64_CONST` runs `code.read_f64_const` and then calls the hook for the
`f64_const` event. -/
theorem dispatch_f64_const {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F64_CONST v =
      Visitor.Core.run (code.read_f64_const st data) (fun v s a => invoke visitor v (.op s (.f64_const a))) v := by
  simpa only [invoke] using Visitor.Dispatch.dispatch_f64_const visitor st data env ctx v

/-- `code.step` on `code.OP_SELECT` runs `code.read_select` and then calls the hook for the `select`
event. -/
theorem dispatch_select {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_SELECT v =
      Visitor.Core.run (code.read_select st) (fun v s a => invoke visitor v (.op s (.select a))) v :=
  code.step_select.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_LOCAL_GET` runs `code.read_local_get` and then calls the hook for the
`local_get` event. -/
theorem dispatch_local_get {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOCAL_GET v =
      Visitor.Core.run (code.read_local_get st data ctx) (fun v s a => invoke visitor v (.op s (.local_get a))) v :=
  code.step_local_get.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_LOCAL_SET` runs `code.read_local_set` and then calls the hook for the
`local_set` event. -/
theorem dispatch_local_set {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOCAL_SET v =
      Visitor.Core.run (code.read_local_set st data ctx) (fun v s a => invoke visitor v (.op s (.local_set a))) v :=
  code.step_local_set.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_LOCAL_TEE` runs `code.read_local_tee` and then calls the hook for the
`local_tee` event. -/
theorem dispatch_local_tee {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOCAL_TEE v =
      Visitor.Core.run (code.read_local_tee st data ctx) (fun v s a => invoke visitor v (.op s (.local_tee a))) v :=
  code.step_local_tee.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_GLOBAL_GET` runs `code.read_global_get` and then calls the hook for the
`global_get` event. -/
theorem dispatch_global_get {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_GLOBAL_GET v =
      Visitor.Core.run (code.read_global_get st data env) (fun v s a => invoke visitor v (.op s (.global_get a))) v :=
  code.step_global_get.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_GLOBAL_SET` runs `code.read_global_set` and then calls the hook for the
`global_set` event. -/
theorem dispatch_global_set {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_GLOBAL_SET v =
      Visitor.Core.run (code.read_global_set st data env) (fun v s a => invoke visitor v (.op s (.global_set a))) v :=
  code.step_global_set.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_MEMORY_SIZE` runs `code.read_memory_size` and then calls the hook for
the `memory_size` event. -/
theorem dispatch_memory_size {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_MEMORY_SIZE v =
      Visitor.Core.run (code.read_memory_size st data env) (fun v s _ => invoke visitor v (.op s (.memory_size))) v :=
  code.step_memory_size.dispatch visitor st data env ctx v

/-- `code.step` on `code.OP_MEMORY_GROW` runs `code.read_memory_grow` and then calls the hook for
the `memory_grow` event. -/
theorem dispatch_memory_grow {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_MEMORY_GROW v =
      Visitor.Core.run (code.read_memory_grow st data env) (fun v s _ => invoke visitor v (.op s (.memory_grow))) v :=
  code.step_memory_grow.dispatch visitor st data env ctx v

/-- A numeric opcode with a binary row and a callback runs `Body.Numeric.read` and then reports the
numeric event of that callback. -/
theorem dispatch_numeric {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V)
    (opcode : U8) (operation : Body.Numeric.Operation) (hook : NumericHook)
    (hrow : Body.Numeric.opcodeMeaning opcode = some operation)
    (hhook : NumericHook.ofOpcode opcode = some hook) :
    code.step visitor st data env ctx opcode v =
      Visitor.Core.run (Body.Numeric.read operation st)
        (fun v s (_ : Unit) => invoke visitor v (.op s (.numeric hook))) v := by
  rw [code.step.numeric_dispatch visitor st data env ctx opcode v (Body.Numeric.NumericOp.bounds hrow).1,
    code.step_numeric.dispatch visitor st opcode operation v hrow]
  simp only [visit_numeric, hhook]

/-- A load or store opcode with a binary row and a callback runs `code.read_load` or
`code.read_store` and then reports the memory event of that callback. -/
theorem dispatch_memory {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V)
    (opcode : U8) (operation : Body.MemoryMeaning.Operation) (hook : MemoryHook)
    (hrow : Body.MemoryMeaning.opcodeMeaning opcode = some operation)
    (hhook : MemoryHook.ofOpcode opcode = some hook) :
    code.step visitor st data env ctx opcode v =
      Visitor.Core.run
        (if operation.store then code.read_store st data env operation.ty operation.naturalAlign
          else code.read_load st data env operation.ty operation.naturalAlign)
        (fun v s arg => invoke visitor v (.op s (.memory hook arg))) v := by
  rw [code.step_memory.dispatch visitor st data env ctx v opcode operation hrow]
  simp only [visit_memory, hhook]

end Itasca.Visitor.Trace

open Aeneas Aeneas.Std

end

/-! ## StepRefinement -/

section

/-!
# Refinement of an instruction step

`code.step.refines` lifts `Visitor.Trace.Refines` through the extracted scalar
step. Related visitors return the same ordinary reply and validator state,
with visitor states related by the supplied relation. The relation constrains
all returning outcomes, including callback rejection.
-/

open Aeneas Aeneas.Std

namespace Itasca

open Visitor.Trace

/-- A refinement of hooks lifts to `code.step` for every opcode. Every normal return, including
rejections and malformed instructions, is reproduced with the same result and validator state. -/
theorem code.step.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context)
    (opcode : U8) (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (st' : code.OpIterState) (v' : V)
    (h : code.step visitor st data env ctx opcode v = .ok (res, st', v')) :
    ∃ w', code.step replacement st data env ctx opcode w =
      .ok (res, st', w') ∧ related v' w' := by
  cases hn : Body.Numeric.opcodeMeaning opcode with
  | some operation =>
    obtain ⟨hook, hhook, _, _⟩ := NumericHook.of_meaning hn
    rw [dispatch_numeric visitor st data env ctx v opcode operation hook hn hhook] at h
    rw [dispatch_numeric replacement st data env ctx w opcode operation hook hn hhook]
    exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
  | none =>
    cases hm : Body.MemoryMeaning.opcodeMeaning opcode with
    | some operation =>
      obtain ⟨hook, hhook, _, _⟩ := MemoryHook.of_meaning hm
      rw [dispatch_memory visitor st data env ctx v opcode operation hook hm hhook] at h
      rw [dispatch_memory replacement st data env ctx w opcode operation hook hm hhook]
      exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
    | none =>
      by_cases h_nop : opcode = code.OP_NOP
      · subst opcode
        rw [dispatch_nop visitor st data env ctx v] at h
        rw [dispatch_nop replacement st data env ctx w]
        exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_unreachable : opcode = code.OP_UNREACHABLE
      · subst opcode
        rw [dispatch_unreachable visitor st data env ctx v] at h
        rw [dispatch_unreachable replacement st data env ctx w]
        exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_i32_const : opcode = code.OP_I32_CONST
      · subst opcode
        rw [dispatch_i32_const visitor st data env ctx v] at h
        rw [dispatch_i32_const replacement st data env ctx w]
        exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_i64_const : opcode = code.OP_I64_CONST
      · subst opcode
        rw [dispatch_i64_const visitor st data env ctx v] at h
        rw [dispatch_i64_const replacement st data env ctx w]
        exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_f32_const : opcode = code.OP_F32_CONST
      · subst opcode
        rw [dispatch_f32_const visitor st data env ctx v] at h
        rw [dispatch_f32_const replacement st data env ctx w]
        exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_f64_const : opcode = code.OP_F64_CONST
      · subst opcode
        rw [dispatch_f64_const visitor st data env ctx v] at h
        rw [dispatch_f64_const replacement st data env ctx w]
        exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_drop : opcode = code.OP_DROP
      · subst opcode
        rw [dispatch_drop visitor st data env ctx v] at h
        rw [dispatch_drop replacement st data env ctx w]
        exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_select : opcode = code.OP_SELECT
      · subst opcode
        rw [dispatch_select visitor st data env ctx v] at h
        rw [dispatch_select replacement st data env ctx w]
        exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_local_get : opcode = code.OP_LOCAL_GET
      · subst opcode
        rw [dispatch_local_get visitor st data env ctx v] at h
        rw [dispatch_local_get replacement st data env ctx w]
        exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_local_set : opcode = code.OP_LOCAL_SET
      · subst opcode
        rw [dispatch_local_set visitor st data env ctx v] at h
        rw [dispatch_local_set replacement st data env ctx w]
        exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
      · subst opcode
        rw [dispatch_local_tee visitor st data env ctx v] at h
        rw [dispatch_local_tee replacement st data env ctx w]
        exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_global_get : opcode = code.OP_GLOBAL_GET
      · subst opcode
        rw [dispatch_global_get visitor st data env ctx v] at h
        rw [dispatch_global_get replacement st data env ctx w]
        exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_global_set : opcode = code.OP_GLOBAL_SET
      · subst opcode
        rw [dispatch_global_set visitor st data env ctx v] at h
        rw [dispatch_global_set replacement st data env ctx w]
        exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
      · subst opcode
        rw [dispatch_memory_size visitor st data env ctx v] at h
        rw [dispatch_memory_size replacement st data env ctx w]
        exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
      · subst opcode
        rw [dispatch_memory_grow visitor st data env ctx v] at h
        rw [dispatch_memory_grow replacement st data env ctx w]
        exact Visitor.Core.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      have heqval (a b : U8) : a = b ↔ a.val = b.val :=
        ⟨fun h => congrArg UScalar.val h, UScalar.eq_of_val_eq⟩
      have hdispatch {W : Type} (hooks : code.OpVisitor W) (w : W) :
          code.step hooks st data env ctx opcode w = code.step_memory hooks st data env opcode w := by
        unfold code.step
        split <;> simp_all [global_simps, U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]
      rw [hdispatch visitor v] at h
      rw [hdispatch replacement w]
      rw [Visitor.Dispatch.memory_fallback visitor st data env opcode v hm h_memory_size h_memory_grow,
        code.step_numeric.unrecognized visitor st opcode v hn] at h
      rw [Visitor.Dispatch.memory_fallback replacement st data env opcode w hm h_memory_size h_memory_grow,
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

namespace Itasca.Visitor.Trace

/-- Converts a callback reply to a validator result: a rejection becomes `OpError.Visitor`. -/
def outcome : VisitResult → BodyResult
  | .Ok () => .Ok ()
  | .Err e => .Err (.Visitor e)

theorem AllAccepted.append {xs ys} (hx : AllAccepted xs) (hy : AllAccepted ys) :
    AllAccepted (xs ++ ys) := by
  intro o ho
  exact (List.mem_append.mp ho).elim (hx o) (hy o)

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

end Itasca.Visitor.Trace

end
