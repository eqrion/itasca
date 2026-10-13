import Itasca.Visitor.TraceBytes

/-!
# Properties of callback traces

Shows that the traces of `Visitor/TraceBytes` contain only instruction callbacks, so they never
include `functionStart`, and that `VisitorTrace.project` recovers their `Wasm1.Token` list from
the observations. `BodyTrace.project` states that a body trace projects to the tokens of the
consumed bytes, with no pending `br_table` labels when the run is accepted. Covers the Wasm 1.0
body.
-/

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

private theorem rejection_position {before after accepted : List Observation}
    {event last : Event} {e other : error.VisitError}
    (heq : before ++ [⟨event, .Err e⟩] ++ after = accepted ++ [⟨last, .Err other⟩])
    (hok : AllAccepted accepted) :
    after = [] ∧ e = other ∧ AllAccepted before := by
  induction before generalizing accepted with
  | nil =>
    cases accepted with
    | nil =>
      simp only [List.nil_append, List.singleton_append, List.cons.injEq] at heq
      refine ⟨heq.2, ?_, by simp [AllAccepted]⟩
      have he := congrArg Observation.outcome heq.1
      exact core.result.Result.Err.inj he
    | cons first rest =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
      have hh := hok first (by simp)
      rw [← heq.1] at hh
      contradiction
  | cons first rest ih =>
    cases accepted with
    | nil =>
      have hl := congrArg List.length heq
      simp at hl
    | cons head tail =>
      simp only [List.cons_append, List.cons.injEq] at heq
      have ht : AllAccepted tail := fun o ho => hok o (List.mem_cons_of_mem _ ho)
      obtain ⟨ha, he, hb⟩ := ih heq.2 ht
      refine ⟨ha, he, ?_⟩
      intro o ho
      rcases List.mem_cons.mp ho with rfl | ho
      · rw [heq.1]
        exact hok head (by simp)
      · exact hb o ho

/-- An observed rejecting callback is last and determines the returned visitor error. -/
theorem Outcomes.rejecting {before after : List Observation} {event : Event}
    {e : error.VisitError} {result : BodyResult}
    (h : Outcomes (before ++ [⟨event, .Err e⟩] ++ after) result) :
    after = [] ∧ result = .Err (.Visitor e) ∧ AllAccepted before := by
  have hnot : ¬ AllAccepted (before ++ [⟨event, .Err e⟩] ++ after) := by
    intro hall
    have hh := hall ⟨event, .Err e⟩ (by simp)
    contradiction
  cases result with
  | Ok u => exact False.elim (hnot h)
  | Err err =>
    cases err <;> try exact False.elim (hnot h)
    case Visitor other =>
      rcases h with hall | ⟨accepted, last, heq, hok⟩
      · exact False.elim (hnot hall)
      obtain ⟨ha, rfl, hb⟩ := rejection_position heq hok
      exact ⟨ha, rfl, hb⟩

/-- Every observation is an instruction callback with its validator state, not a function start. -/
def OnlyOps (observations : List Observation) : Prop :=
  ∀ o ∈ observations, ∃ st action, o.event = .op st action

theorem OnlyOps.append {first rest : List Observation}
    (hf : OnlyOps first) (hr : OnlyOps rest) : OnlyOps (first ++ rest) := by
  intro o ho
  exact (List.mem_append.mp ho).elim (hf o) (hr o)

theorem OnlyOps.single (st : code.OpIterState) (action : Action) (reply : VisitResult) :
    OnlyOps [⟨.op st action, reply⟩] := by
  intro o ho
  have he : o = ⟨.op st action, reply⟩ := by simpa using ho
  subst o
  exact ⟨st, action, rfl⟩

/-- A trace of only instruction callbacks contains no `functionStart` event. -/
theorem OnlyOps.no_function_start {observations : List Observation} (h : OnlyOps observations)
    (ctx : code.Context) (idx : U32) (first last : Usize) :
    Event.functionStart ctx idx first last ∉ observations.map Observation.event := by
  intro hm
  obtain ⟨o, ho, he⟩ := List.mem_map.mp hm
  obtain ⟨st, action, hop⟩ := h o ho
  rw [hop] at he
  contradiction

theorem LabelsAt.only_ops {data pos observations depths last}
    (h : LabelsAt data pos observations depths last) : OnlyOps observations := by
  induction h with
  | nil => simp [OnlyOps]
  | cons hd ht ih =>
    simpa using (OnlyOps.single _ (.br_table_label _) _).append ih

theorem Chunk.only_ops {data start observations token next}
    (h : Chunk data start observations token next) : OnlyOps observations := by
  cases h with
  | single st action reply token _ _ _ => exact .single st action reply
  | table _ _ hl _ _ _ => exact hl.only_ops.append (.single _ (.br_table _ _) _)

theorem Completed.only_ops {data start observations tokens next}
    (h : Completed data start observations tokens next) : OnlyOps observations := by
  induction h with
  | nil => simp [OnlyOps]
  | cons hc _ ih => exact hc.only_ops.append ih

theorem PartialTable.only_ops {data start observations}
    (h : PartialTable data start observations) : OnlyOps observations := by
  obtain ⟨_, _, _, _, _, _, _, hl, _⟩ := h
  exact hl.only_ops

/-- A body trace contains only instruction callbacks. -/
theorem BodyTrace.only_ops {data start observations result}
    (h : BodyTrace data start observations result) : OnlyOps observations := by
  obtain ⟨_, complete, _, _, tail, rfl, hc, ht, _⟩ := h
  apply hc.only_ops.append
  rcases ht with rfl | ht
  · simp [OnlyOps]
  · exact ht.only_ops

theorem LabelsAt.no_function_start {data pos observations depths last}
    (h : LabelsAt data pos observations depths last)
    (ctx : code.Context) (idx : U32) (first finish : Usize) :
    Event.functionStart ctx idx first finish ∉ observations.map Observation.event :=
  h.only_ops.no_function_start ctx idx first finish

theorem Chunk.no_function_start {data start observations token next}
    (h : Chunk data start observations token next)
    (ctx : code.Context) (idx : U32) (first finish : Usize) :
    Event.functionStart ctx idx first finish ∉ observations.map Observation.event :=
  h.only_ops.no_function_start ctx idx first finish

theorem Completed.no_function_start {data start observations tokens next}
    (h : Completed data start observations tokens next)
    (ctx : code.Context) (idx : U32) (first finish : Usize) :
    Event.functionStart ctx idx first finish ∉ observations.map Observation.event :=
  h.only_ops.no_function_start ctx idx first finish

theorem PartialTable.no_function_start {data start observations}
    (h : PartialTable data start observations)
    (ctx : code.Context) (idx : U32) (first finish : Usize) :
    Event.functionStart ctx idx first finish ∉ observations.map Observation.event :=
  h.only_ops.no_function_start ctx idx first finish

/-- A body trace has no `functionStart` event. -/
theorem BodyTrace.no_function_start {data start observations result}
    (h : BodyTrace data start observations result)
    (ctx : code.Context) (idx : U32) (first finish : Usize) :
    Event.functionStart ctx idx first finish ∉ observations.map Observation.event :=
  h.only_ops.no_function_start ctx idx first finish

/-- The pending `br_table` labels after a callback: a label callback adds one, the closing table
callback clears them. -/
def Action.nextPending (action : Action) (pending : List U32) : List U32 :=
  match action with
  | .br_table_label depth => pending ++ [depth]
  | .br_table _ _ => []
  | _ => pending

/-- Reconstructs the flat token list and the pending `br_table` labels from a trace. Replies do not
affect the result. -/
def project : List Observation → List U32 → List Wasm1.Token × List U32
  | [], pending => ([], pending)
  | observation :: rest, pending =>
    match observation.event with
    | .functionStart _ _ _ _ => project rest pending
    | .op _ action =>
      let next := project rest (action.nextPending pending)
      ((action.token pending).toList ++ next.1, next.2)

/-- `project` of a concatenation threads the pending labels through. -/
theorem project_append (first rest : List Observation) (pending : List U32) :
    project (first ++ rest) pending =
      ((project first pending).1 ++ (project rest (project first pending).2).1,
        (project rest (project first pending).2).2) := by
  induction first generalizing pending with
  | nil => simp [project]
  | cons observation first ih =>
    cases he : observation.event with
    | functionStart ctx idx first last => simp [project, he, ih]
    | op st action => simp [project, he, ih, List.append_assoc]

/-- A label sequence projects to no tokens and appends its depths to the pending labels. -/
theorem LabelsAt.project {data pos observations depths last}
    (h : LabelsAt data pos observations depths last) (pending : List U32) :
    project observations pending = ([], pending ++ depths) := by
  induction h generalizing pending with
  | nil => simp [VisitorTrace.project]
  | cons hd ht ih =>
    simp [VisitorTrace.project, Action.token, Action.nextPending, ih, List.append_assoc]

private theorem Action.nextPending_nil_of_token {action : Action} {token : Wasm1.Token}
    (h : action.token [] = some token) : action.nextPending [] = [] := by
  cases action <;> try rfl
  simp [Action.token] at h

/-- A chunk projects to its token and leaves no pending labels. -/
theorem Chunk.project {data start observations token next}
    (h : Chunk data start observations token next) : project observations [] = ([token], []) := by
  cases h with
  | single st action reply token ht _ _ =>
    simp [VisitorTrace.project, Action.nextPending_nil_of_token ht, ht]
  | table _ _ hl _ _ _ =>
    rw [project_append, hl.project]
    simp [VisitorTrace.project, Action.token, Action.nextPending]

/-- Completed chunks project to their token list and leave no pending labels. -/
theorem Completed.project {data start observations tokens next}
    (h : Completed data start observations tokens next) : project observations [] = (tokens, []) := by
  induction h with
  | nil => rfl
  | cons hc ht ih =>
    rw [project_append, hc.project]
    simp [ih]

/-- An unfinished `br_table` projects to no tokens and its pending label depths. -/
theorem PartialTable.project {data start observations}
    (h : PartialTable data start observations) :
    ∃ depths, project observations [] = ([], depths) := by
  obtain ⟨_, _, _, depths, _, _, _, hl, _⟩ := h
  exact ⟨depths, by simpa using hl.project []⟩

/-- A body trace projects to the tokens of a consumed byte prefix plus any pending labels. An
accepted body consumes the whole input and has no pending labels. -/
theorem BodyTrace.project {data start observations result}
    (h : BodyTrace data start observations result) :
    ∃ tokens cursor pending, project observations [] = (tokens, pending) ∧
      Wasm1.Consumed data start tokens cursor ∧
      (result = .Ok () → pending = [] ∧ cursor.val = data.length) := by
  obtain ⟨_, complete, tokens, cursor, tail, heq, hc, ht, hend⟩ := h
  have hp : ∃ pending, VisitorTrace.project tail [] = ([], pending) := by
    rcases ht with rfl | ht
    · exact ⟨[], rfl⟩
    · exact ht.project
  obtain ⟨pending, hp⟩ := hp
  refine ⟨tokens, cursor, pending, ?_, hc.encoded, ?_⟩
  · rw [heq, project_append, hc.project]
    simp [hp]
  · intro hr
    obtain ⟨rfl, hpos⟩ := hend hr
    exact ⟨(congrArg Prod.snd hp).symm, hpos⟩

end Itasca.VisitorTrace
