import Itasca.Visitor.EventMeaning
import Itasca.Binary.Wasm1.Encoding

/-!
# Callback traces and byte provenance

Describes callback traces without mentioning the extracted code. `Chunk` is the callbacks of one
decoded instruction, `Completed` a run of chunks, `PartialTable` an unfinished `br_table`, and
`BodyTrace` a whole body. Each relates the observations to `Wasm1.Token` lists and the bytes they
encode, and `Outcomes` relates them to the validator result. `BodyTrace.accepted` states that an
accepted body consumes all its input. Covers the Wasm 1.0 body.
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

/-- The callbacks of one fully decoded instruction with its token. A `br_table` has one label
callback per vector entry and a closing callback, and none for its default target. -/
inductive Chunk (data : Slice U8) (start : Usize) :
    List Observation → Wasm1.Token → Usize → Prop where
  | single (st : code.OpIterState) (action : Action) (reply : VisitResult) (token : Wasm1.Token) :
      action.token [] = some token → action.opcode ≠ some 0x0E#u8 →
      Wasm1.At data start token st.pos →
      Chunk data start [⟨.op st action, reply⟩] token st.pos
  | table {pos count first labels depths last fallback st bt reply} :
      Wasm1.BytesAt data start [0x0E#u8] pos →
      Leb128.Decoded data pos count first →
      LabelsAt data first labels depths last → depths.length = count.val →
      Leb128.Decoded data last fallback st.pos →
      Wasm1.At data start
        (.plain (.BR_TABLE (depths.map (fun i => .mk_uN i.val)) (.mk_uN fallback.val))) st.pos →
      Chunk data start (labels ++ [⟨.op st (.br_table fallback bt), reply⟩])
        (.plain (.BR_TABLE (depths.map (fun i => .mk_uN i.val)) (.mk_uN fallback.val))) st.pos

/-- A chunk's bytes encode its token. -/
theorem Chunk.encoded {data start observations token next}
    (h : Chunk data start observations token next) : Wasm1.At data start token next := by
  cases h <;> assumption

/-- The callbacks of a `br_table` that stopped before its closing callback. They cover some or all
of the vector entries, including an entry whose target merge failed after its callback ran. -/
def PartialTable (data : Slice U8) (start : Usize) (observations : List Observation) : Prop :=
  ∃ pos count first depths last,
    Wasm1.BytesAt data start [0x0E#u8] pos ∧
    Leb128.Decoded data pos count first ∧
    LabelsAt data first observations depths last ∧ depths.length ≤ count.val

/-- The callbacks of one step that returns normally. The step either failed silently, completed an
instruction, or stopped inside a `br_table`. -/
inductive StepTrace (data : Slice U8) (start : Usize) :
    List Observation → BodyResult → code.OpIterState → Prop where
  | silent (e : error.OpError) (st : code.OpIterState) : Outcomes [] (.Err e) →
      StepTrace data start [] (.Err e) st
  | complete {observations token st result} : Chunk data start observations token st.pos →
      Outcomes observations result → StepTrace data start observations result st
  | unfinished {observations st} (e : error.OpError) : PartialTable data start observations →
      Outcomes observations (.Err e) → StepTrace data start observations (.Err e) st

/-- The callbacks of a step match its result. -/
theorem StepTrace.outcomes {data start observations result st}
    (h : StepTrace data start observations result st) : Outcomes observations result := by
  cases h <;> assumption

/-- An accepted step completed an instruction. -/
theorem StepTrace.accepted {data start observations st}
    (h : StepTrace data start observations (.Ok ()) st) :
    ∃ token, Chunk data start observations token st.pos := by
  cases h with
  | complete hc _ => exact ⟨_, hc⟩

/-- Consecutive complete instruction chunks with their tokens. -/
inductive Completed (data : Slice U8) :
    Usize → List Observation → List Wasm1.Token → Usize → Prop where
  | nil (pos : Usize) (bound : pos.val ≤ data.length) : Completed data pos [] [] pos
  | cons {start first token middle rest tokens next} :
      Chunk data start first token middle → Completed data middle rest tokens next →
      Completed data start (first ++ rest) (token :: tokens) next

/-- Completed chunks encode their token list. -/
theorem Completed.encoded {data start observations tokens next}
    (h : Completed data start observations tokens next) : Wasm1.Consumed data start tokens next := by
  induction h with
  | nil pos hb => exact .nil pos hb
  | cons hc _ ih =>
      simpa using (Wasm1.Consumed.snoc (.nil _ (by have := hc.encoded.span; omega)) hc.encoded).append ih

/-- The callbacks of a whole body run: completed chunks, then possibly one partial `br_table`. An
accepted run consumes all of the input and has no partial table. -/
def BodyTrace (data : Slice U8) (start : Usize) (observations : List Observation)
    (result : BodyResult) : Prop :=
  Outcomes observations result ∧ ∃ complete tokens cursor tail,
    observations = complete ++ tail ∧ Completed data start complete tokens cursor ∧
    (tail = [] ∨ PartialTable data cursor tail) ∧
    (result = .Ok () → tail = [] ∧ cursor.val = data.length)

/-- An accepted body run has only accepted callbacks and consumes the entire input. -/
theorem BodyTrace.accepted {data start observations}
    (h : BodyTrace data start observations (.Ok ())) :
    AllAccepted observations ∧ ∃ tokens cursor,
      Completed data start observations tokens cursor ∧ cursor.val = data.length := by
  obtain ⟨ho, complete, tokens, cursor, tail, heq, hc, _, hend⟩ := h
  obtain ⟨rfl, hp⟩ := hend rfl
  simp only [List.append_nil] at heq
  exact ⟨ho, tokens, cursor, heq ▸ hc, hp⟩

end Itasca.VisitorTrace
