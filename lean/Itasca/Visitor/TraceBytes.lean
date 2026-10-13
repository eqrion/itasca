import Itasca.Visitor.EventMeaning
import Itasca.Binary.Wasm1.Encoding

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

abbrev BodyResult := core.result.Result Unit error.OpError

/-- Ordinary callback results are converted without changing their error. -/
def outcome : VisitResult → BodyResult
  | .Ok () => .Ok ()
  | .Err e => .Err (.Visitor e)

def AllAccepted (observations : List Observation) : Prop :=
  ∀ observation ∈ observations, observation.outcome = .Ok ()

theorem AllAccepted.append {xs ys} (hx : AllAccepted xs) (hy : AllAccepted ys) :
    AllAccepted (xs ++ ys) := by
  intro o ho
  exact (List.mem_append.mp ho).elim (hx o) (hy o)

/-- A rejecting callback is the last observation and matches the returned
visitor error. Successful calls contain only accepting callbacks. -/
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

/-- Raw vector depths, in callback order, with each callback's precise cursor.
No reader or implementation dispatcher appears in this relation. -/
inductive LabelsAt (data : Slice U8) : Usize → List Observation → List U32 → Usize → Prop where
  | nil (pos : Usize) : LabelsAt data pos [] [] pos
  | cons {pos depth st reply observations depths last} :
      Leb128.Decoded data pos depth st.pos →
      LabelsAt data st.pos observations depths last →
      LabelsAt data pos (⟨.op st (.br_table_label depth), reply⟩ :: observations)
        (depth :: depths) last

/-- Exactly the callbacks for one fully decoded instruction. The table case
separates vector entries from its default target, which has no label callback.
Computed metadata and state snapshots remain in the observations. -/
inductive Chunk (data : Slice U8) (start : Usize) :
    List Observation → Wasm.Token → Usize → Prop where
  | single (st : code.OpIterState) (action : Action) (reply : VisitResult) (token : Wasm.Token) :
      action.token [] = some token → action.opcode ≠ some 0x0E#u8 →
      Wasm.At data start token st.pos →
      Chunk data start [⟨.op st action, reply⟩] token st.pos
  | table {pos count first labels depths last fallback st bt reply} :
      Wasm.BytesAt data start [0x0E#u8] pos →
      Leb128.Decoded data pos count first →
      LabelsAt data first labels depths last → depths.length = count.val →
      Leb128.Decoded data last fallback st.pos →
      Wasm.At data start
        (.plain (.BR_TABLE (depths.map (fun i => .mk_uN i.val)) (.mk_uN fallback.val))) st.pos →
      Chunk data start (labels ++ [⟨.op st (.br_table fallback bt), reply⟩])
        (.plain (.BR_TABLE (depths.map (fun i => .mk_uN i.val)) (.mk_uN fallback.val))) st.pos

theorem Chunk.encoded {data start observations token next}
    (h : Chunk data start observations token next) : Wasm.At data start token next := by
  cases h <;> assumption

/-- A rejected table can have observed some or all of its vector entries,
without a closing table callback. Even a label that fails target merging is
part of this prefix, since its callback has already run. -/
def PartialTable (data : Slice U8) (start : Usize) (observations : List Observation) : Prop :=
  ∃ pos count first depths last,
    Wasm.BytesAt data start [0x0E#u8] pos ∧
    Leb128.Decoded data pos count first ∧
    LabelsAt data first observations depths last ∧ depths.length ≤ count.val

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
    Usize → List Observation → List Wasm.Token → Usize → Prop where
  | nil (pos : Usize) (bound : pos.val ≤ data.length) : Completed data pos [] [] pos
  | cons {start first token middle rest tokens next} :
      Chunk data start first token middle → Completed data middle rest tokens next →
      Completed data start (first ++ rest) (token :: tokens) next

theorem Completed.encoded {data start observations tokens next}
    (h : Completed data start observations tokens next) : Wasm.Consumed data start tokens next := by
  induction h with
  | nil pos hb => exact .nil pos hb
  | cons hc _ ih =>
      simpa using (Wasm.Consumed.snoc (.nil _ (by have := hc.encoded.span; omega)) hc.encoded).append ih

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

end Itasca.VisitorTrace
