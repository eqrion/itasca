import Itasca.Binary.Wasm2.EncodingUnique
import Itasca.Visitor.TraceBytes
import Itasca.Visitor.RunTrace

/-!
# Callback byte provenance for Wasm 2.0

Defines the relations that tie a visitor's callback observations to the independent encoding of a
body: `Chunk` (the callbacks of one decoded instruction), `StepTrace` (one step, including failure),
`Completed` (a sequence of chunks) and `BodyTrace` (a whole run). Block tokens keep their indexed
signatures. This file gives the relations and their composition laws; `Wasm2/Trace/Correspondence`
shows that the extracted validator satisfies them.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.CallbackTrace

open VisitorTrace

/-- The Wasm 2.0 token of an operator callback. Block, loop and if tokens keep their indexed
parameter and result signatures. -/
def actionToken (action : Action) (pending : List U32) : Option Token :=
  match action with
  | .block bt => some (.block bt)
  | .loop bt => some (.loop bt)
  | .if_ bt => some (.if_ bt)
  | _ => action.token pending

/-- Exactly the callbacks for one fully decoded instruction. The table case
separates vector entries from its default target, which has no label callback.
Computed metadata and state snapshots remain in the observations. -/
inductive Chunk (data : Slice U8) (start : Usize) :
    List Observation → Token → Usize → Prop where
  | single (st : code.OpIterState) (action : Action) (reply : VisitResult) (token : Token) :
      actionToken action [] = some token → action.opcode ≠ some 0x0E#u8 →
      At data start token st.pos →
      Chunk data start [⟨.op st action, reply⟩] token st.pos
  | table {pos count first labels depths last fallback st bt reply} :
      Wasm1.BytesAt data start [0x0E#u8] pos →
      Leb128.Decoded data pos count first →
      LabelsAt data first labels depths last → depths.length = count.val →
      Leb128.Decoded data last fallback st.pos →
      At data start
        (.plain (.BR_TABLE (depths.map (fun i => .mk_uN i.val)) (.mk_uN fallback.val))) st.pos →
      Chunk data start (labels ++ [⟨.op st (.br_table fallback bt), reply⟩])
        (.plain (.BR_TABLE (depths.map (fun i => .mk_uN i.val)) (.mk_uN fallback.val))) st.pos

theorem Chunk.encoded {data start observations token next}
    (h : Chunk data start observations token next) : At data start token next := by
  cases h <;> assumption

/-- One actual step's callback trace, including ordinary failure. -/
inductive StepTrace (data : Slice U8) (start : Usize) :
    List Observation → BodyResult → code.OpIterState → Prop where
  | silent (e : error.OpError) (st : code.OpIterState) : Outcomes [] (.Err e) →
      StepTrace data start [] (.Err e) st
  | complete {observations token st result} : Chunk data start observations token st.pos →
      Outcomes observations result → StepTrace data start observations result st
  | unfinished {observations st} (e : error.OpError) : PartialTable data start observations →
      Outcomes observations (.Err e) → StepTrace data start observations (.Err e) st

theorem StepTrace.outcomes {data start observations result st}
    (h : StepTrace data start observations result st) : Outcomes observations result := by
  cases h <;> assumption

theorem StepTrace.accepted {data start observations st}
    (h : StepTrace data start observations (.Ok ()) st) :
    ∃ token, Chunk data start observations token st.pos := by
  cases h with
  | complete hc _ => exact ⟨_, hc⟩

/-- Concatenation of complete instruction chunks, independently of execution. -/
inductive Completed (data : Slice U8) :
    Usize → List Observation → List Token → Usize → Prop where
  | nil (pos : Usize) (bound : pos.val ≤ data.length) : Completed data pos [] [] pos
  | cons {start first token middle rest tokens next} :
      Chunk data start first token middle → Completed data middle rest tokens next →
      Completed data start (first ++ rest) (token :: tokens) next

theorem Completed.encoded {data start observations tokens next}
    (h : Completed data start observations tokens next) : Consumed data start tokens next := by
  induction h with
  | nil pos hb => exact .nil pos hb
  | cons hc _ ih =>
      simpa using (Consumed.snoc (.nil _ (by have := hc.encoded.span; omega)) hc.encoded).append ih

/-- Whole-run byte provenance. Only the final rejected table can be partial. -/
def BodyTrace (data : Slice U8) (start : Usize) (observations : List Observation)
    (result : BodyResult) : Prop :=
  Outcomes observations result ∧ ∃ complete tokens cursor tail,
    observations = complete ++ tail ∧ Completed data start complete tokens cursor ∧
    (tail = [] ∨ PartialTable data cursor tail) ∧
    (result = .Ok () → tail = [] ∧ cursor.val = data.length)

theorem BodyTrace.accepted {data start observations}
    (h : BodyTrace data start observations (.Ok ())) :
    AllAccepted observations ∧ ∃ tokens cursor,
      Completed data start observations tokens cursor ∧ cursor.val = data.length := by
  obtain ⟨ho, complete, tokens, cursor, tail, heq, hc, _, hend⟩ := h
  obtain ⟨rfl, hp⟩ := hend rfl
  simp only [List.append_nil] at heq
  exact ⟨ho, tokens, cursor, heq ▸ hc, hp⟩


/-- Lifts independent success-byte provenance through a single recorded callback.
Failure before the callback is silent; the callback's own rejection is recorded. -/
theorem run_step_trace {A V : Type} (data : Slice U8) (start : Usize)
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (action : A → Action)
    (hbytes : ∀ s a, read = .ok (.Ok a, s) → ∃ token,
      actionToken (action a) [] = some token ∧ (action a).opcode ≠ some 0x0E#u8 ∧
      At data start token s.pos)
    (v : V) (result : BodyResult) (final : code.OpIterState) (v' : V)
    (h : CoreVisitor.run read (fun v s a => invoke visitor v (.op s (action a))) v =
      .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      StepTrace data start observations result final := by
  rcases CoreVisitor.run.recorded read visitor observe hrecords (fun s a => .op s (action a))
      v result final v' h with ⟨err, _, rfl, hlog⟩ | ⟨a, reply, hr, rfl, hlog⟩
  · exact ⟨[], by simpa using hlog, .silent err final (Outcomes.empty _)⟩
  · obtain ⟨token, ht, hn, hb⟩ := hbytes final a hr
    refine ⟨[⟨.op final (action a), reply⟩], hlog,
      .complete (.single final (action a) reply token ht hn hb) ?_⟩
    exact Outcomes.single (.op final (action a)) reply


end Itasca.Wasm2.CallbackTrace
