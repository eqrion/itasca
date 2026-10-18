import Exec.Generated.Funs
import Itasca.Wasm1.Trace.Body
import Itasca.Wasm2.Trace.Correspondence
namespace Exec.Code
open Aeneas Aeneas.Std
open Itasca Itasca.VisitorTrace

/-- One actual callback, retaining both compiler states and the canonical
event (including the validator stack, control stack, and byte position). -/
structure CallbackRecord (V : Type) where
  before : V
  observation : Observation
  after : V

/-- Exact sequential callback equations, without an assumed compiler invariant. -/
inductive CallbackRun {V : Type} (visitor : code.OpVisitor V) :
    V → List (CallbackRecord V) → V → Prop where
  | nil (state) : CallbackRun visitor state [] state
  | snoc {initial before records event reply after}
      (prior : CallbackRun visitor initial records before)
      (called : invoke visitor before event = .ok (reply, after)) :
      CallbackRun visitor initial (records ++ [⟨before, ⟨event, reply⟩, after⟩]) after

def callbackObservations {V : Type} (state : V × List (CallbackRecord V)) : List Observation :=
  state.2.map CallbackRecord.observation

/-- Proof-only instrumentation preserves the actual visitor and records state
transitions; the extracted compiler itself is unchanged. -/
def recordCallbacks {V : Type} (visitor : code.OpVisitor V) :
    code.OpVisitor (V × List (CallbackRecord V)) :=
  ofHandler fun state event => do
    let (reply, after) ← invoke visitor state.1 event
    .ok (reply, (after, state.2 ++ [⟨state.1, ⟨event, reply⟩, after⟩]))

theorem recordCallbacks_refines {V : Type} (visitor : code.OpVisitor V) (initial : V) :
    Refines visitor (recordCallbacks visitor)
      (fun before recorded => before = recorded.1 ∧ CallbackRun visitor initial recorded.2 before) := by
  rintro before ⟨current, records⟩ event reply after ⟨rfl, prior⟩ called
  exact ⟨(after, records ++ [⟨before, ⟨event, reply⟩, after⟩]),
    by simp [recordCallbacks, called], rfl, .snoc prior called⟩

theorem recordCallbacks_records {V : Type} (visitor : code.OpVisitor V) :
    Records (recordCallbacks visitor) callbackObservations := by
  rintro ⟨before, records⟩ event reply ⟨after, output⟩ called
  simp only [recordCallbacks, invoke_ofHandler] at called
  obtain ⟨⟨actualReply, actualAfter⟩, actual, returned⟩ := ResultFacts.bind_ok_inv _ _ _ called
  simp at returned
  obtain ⟨rfl, rfl, rfl⟩ := returned
  simp [callbackObservations]

/-- The Wasm 1.0 accepted body trace and exact compiler callback states arise
from the same actual body-validation run. -/
theorem callback_body_wasm1 {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (results : ctx.results.val = Control.results bt) (before after : V)
    (accepted : code.validate_body_with visitor data env ctx before = .ok (.Ok (), after)) :
    ∃ records, CallbackRun visitor before records after ∧
      VisitorTrace.AcceptedBody data env ctx bt (records.map CallbackRecord.observation) := by
  obtain ⟨⟨final, records⟩, run, same, callbacks⟩ := code.validate_body_with.refines visitor
    (recordCallbacks visitor) _ (recordCallbacks_refines visitor before)
    data env ctx before (before, []) ⟨rfl, .nil before⟩ (.Ok ()) after accepted
  dsimp only at same
  subst final
  obtain ⟨observations, log, trace⟩ := code.validate_body_with.trace_sound (recordCallbacks visitor)
    callbackObservations (recordCallbacks_records visitor) data env ctx bt results
    (before, []) (after, records) run
  simp only [callbackObservations, List.map_nil, List.nil_append] at log
  exact ⟨records, callbacks, log ▸ trace⟩

/-- Wasm 2.0 retains the same callback states with indexed block signatures and
declared-reference evidence from the canonical accepted body trace. -/
theorem callback_body_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (before after : V)
    (accepted : code.validate_multi_value_body_with visitor data env ctx index before = .ok (.Ok (), after)) :
    ∃ records, CallbackRun visitor before records after ∧
      Wasm2.CallbackTrace.AcceptedBody data env ctx index (records.map CallbackRecord.observation) := by
  obtain ⟨⟨final, records⟩, run, same, callbacks⟩ := code.validate_multi_value_body_with.refines visitor
    (recordCallbacks visitor) _ (recordCallbacks_refines visitor before)
    data env ctx index before (before, []) ⟨rfl, .nil before⟩ (.Ok ()) after accepted
  dsimp only at same
  subst final
  obtain ⟨observations, log, trace⟩ := code.validate_multi_value_body_with.trace_sound (recordCallbacks visitor)
    callbackObservations (recordCallbacks_records visitor) data env ctx index
    (before, []) (after, records) run
  simp only [callbackObservations, List.map_nil, List.nil_append] at log
  exact ⟨records, callbacks, log ▸ trace⟩
end Exec.Code
