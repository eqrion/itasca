import Exec.Abs.SliceInversion
import Exec.Abs.Bound
import Exec.Abs.ReferenceBounds
import Exec.Interp.Control.StructuredPoint

namespace Exec.Interp

/-- Syntactic closure is retained independently of value typing. -/
def SyntaxClosure (before after : Abs.AFrame) : Prop := Abs.FrameSlice before → Abs.FrameSlice after

theorem SyntaxClosure.refl (f : Abs.AFrame) : SyntaxClosure f f := fun h => h

theorem SyntaxClosure.trans {before middle after} (first : SyntaxClosure before middle)
    (second : SyntaxClosure middle after) : SyntaxClosure before after := fun h => second (first h)

theorem SyntaxClosure.tail (f : Abs.AFrame) (op : instr) (after : List instr)
    (locals values : List val) :
    SyntaxClosure { f with code := op :: after } { f with code := after, locals := locals, vals := values } := by
  rintro ⟨code, labels⟩
  exact ⟨fun i hi => code i (List.mem_cons_of_mem _ hi), labels⟩

theorem SyntaxClosure.replace (f : Abs.AFrame) (op next : instr) (after : List instr)
    (locals values : List val) (allowed : Abs.SliceInstr next) :
    SyntaxClosure { f with code := op :: after } { f with code := next :: after, locals := locals, vals := values } := by
  rintro ⟨code, labels⟩
  refine ⟨?_, labels⟩
  intro i hi
  rcases List.mem_cons.mp hi with rfl | member
  · exact allowed
  · exact code i (List.mem_cons_of_mem _ member)

theorem SyntaxClosure.branch (f : Abs.AFrame) (depth : Nat) (label : Abs.Label)
    (lookup : f.labels[depth]? = some label) (values : List val) :
    SyntaxClosure f { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := values } := by
  rintro ⟨code, labels⟩
  have retained := labels label (List.mem_of_getElem? lookup)
  constructor
  · intro i hi
    rcases List.mem_append.mp hi with member | member
    · exact retained.1 i member
    · exact retained.2 i member
  · intro next member
    exact labels next (List.mem_of_mem_drop member)

theorem SyntaxClosure.ifChoice (f : Abs.AFrame) (bt : blocktype) (yes no after : List instr)
    (condition : Bool) (values : List val) :
    SyntaxClosure { f with code := .IFELSE bt yes no :: after }
      { f with code := .BLOCK bt (if condition then yes else no) :: after, vals := values } := by
  rintro ⟨code, labels⟩
  have head := code (.IFELSE bt yes no) (List.mem_cons_self ..)
  obtain ⟨yesAllowed, noAllowed⟩ := head.if_inv
  refine ⟨?_, labels⟩
  intro i hi
  rcases List.mem_cons.mp hi with rfl | member
  · apply Abs.SliceInstr.block
    cases condition <;> assumption
  · exact code i (List.mem_cons_of_mem _ member)

theorem SyntaxClosure.loop (f : Abs.AFrame) (bt : blocktype) (body after : List instr)
    (params results : List valtype) (height : Nat) :
    SyntaxClosure { f with code := .LOOP bt body :: after }
      { f with code := body, labels := ⟨params, results, [.LOOP bt body], height, after⟩ :: f.labels } := by
  rintro ⟨code, labels⟩
  have head := code (.LOOP bt body) (List.mem_cons_self ..)
  have bodyAllowed : Forall Abs.SliceInstr body := head.loop_inv
  refine ⟨bodyAllowed, ?_⟩
  intro label member
  rcases List.mem_cons.mp member with rfl | member
  · constructor
    · intro i hi
      have same : i = .LOOP bt body := by simpa using hi
      subst i
      exact head
    · exact fun i hi => code i (List.mem_cons_of_mem _ hi)
  · exact labels label member

theorem SyntaxClosure.block (f : Abs.AFrame) (bt : blocktype) (body after : List instr)
    (results : List valtype) (height : Nat) :
    SyntaxClosure { f with code := .BLOCK bt body :: after }
      { f with code := body, labels := ⟨results, results, [], height, after⟩ :: f.labels } := by
  rintro ⟨code, labels⟩
  have head := code (.BLOCK bt body) (List.mem_cons_self ..)
  have bodyAllowed : Forall Abs.SliceInstr body := head.block_inv
  refine ⟨bodyAllowed, ?_⟩
  intro label member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨by intro i hi; simp at hi, fun i hi => code i (List.mem_cons_of_mem _ hi)⟩
  · exact labels label member

theorem SyntaxClosure.label (f : Abs.AFrame) (label : Abs.Label) (labels : List Abs.Label) :
    SyntaxClosure { f with code := [], labels := label :: labels }
      { f with code := label.after, labels := labels } := by
  rintro ⟨code, saved⟩
  exact ⟨(saved label (List.mem_cons_self ..)).2,
    fun next member => saved next (List.mem_cons_of_mem _ member)⟩

theorem SyntaxClosure.slice {before after} (closure : SyntaxClosure before after)
    {s : store} {ambient : frame} {rest : List Abs.AFrame}
    (slice : Abs.SliceState ⟨s, ambient, before :: rest, []⟩) :
    Abs.SliceState ⟨s, ambient, after :: rest, []⟩ :=
  Abs.slice_replace_frame slice (closure (slice.active _ (List.mem_cons_self ..)))


/-- Every ordinary source rearrangement preserves both the allowed syntax and
an arbitrary pre-existing finite bound on source continuations. -/
structure SourceClosure (before after : Abs.AFrame) : Prop where
  allowed : SyntaxClosure before after
  bounded : ∀ bound, Abs.FrameCodeBound bound before → Abs.FrameCodeBound bound after
  references : ∀ bound, Abs.FrameReferencesBound bound before → Abs.FrameReferencesBound bound after

theorem SourceClosure.refl (f : Abs.AFrame) : SourceClosure f f := ⟨.refl f, fun _ h => h, fun _ h => h⟩

theorem SourceClosure.trans {before middle after} (first : SourceClosure before middle)
    (second : SourceClosure middle after) : SourceClosure before after :=
  ⟨first.allowed.trans second.allowed, fun bound h => second.bounded bound (first.bounded bound h),
    fun bound h => second.references bound (first.references bound h)⟩

theorem SourceClosure.tail (f : Abs.AFrame) (op : instr) (after : List instr)
    (locals values : List val)
    (references : ∀ bound, Abs.FrameReferencesBound bound f → Abs.ValuesBound bound locals ∧ Abs.ValuesBound bound values) :
    SourceClosure { f with code := op :: after } { f with code := after, locals := locals, vals := values } := by
  refine ⟨SyntaxClosure.tail f op after locals values, ?_, references⟩
  rintro bound ⟨size, labels⟩
  refine ⟨?_, labels⟩
  change sizeOf after ≤ bound
  simp only [List.cons.sizeOf_spec] at size
  omega

theorem SourceClosure.replace (f : Abs.AFrame) (op next : instr) (after : List instr)
    (locals values : List val) (allowed : Abs.SliceInstr next) (smaller : sizeOf next ≤ sizeOf op)
    (references : ∀ bound, Abs.FrameReferencesBound bound f → Abs.ValuesBound bound locals ∧ Abs.ValuesBound bound values) :
    SourceClosure { f with code := op :: after } { f with code := next :: after, locals := locals, vals := values } := by
  refine ⟨SyntaxClosure.replace f op next after locals values allowed, ?_, references⟩
  rintro bound ⟨size, labels⟩
  refine ⟨?_, labels⟩
  simp only [List.cons.sizeOf_spec] at size ⊢
  omega

theorem SourceClosure.branch (f : Abs.AFrame) (depth : Nat) (label : Abs.Label)
    (lookup : f.labels[depth]? = some label) (values : List val)
    (references : ∀ bound, Abs.ValuesBound bound f.vals → Abs.ValuesBound bound values) :
    SourceClosure f { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := values } := by
  refine ⟨SyntaxClosure.branch f depth label lookup values, ?_, fun bound h => ⟨h.1, references bound h.2⟩⟩
  rintro bound ⟨size, labels⟩
  exact ⟨labels label (List.mem_of_getElem? lookup), fun next member => labels next (List.mem_of_mem_drop member)⟩

theorem SourceClosure.ifChoice (f : Abs.AFrame) (bt : blocktype) (yes no after : List instr)
    (condition : Bool) (values : List val)
    (references : ∀ bound, Abs.ValuesBound bound f.vals → Abs.ValuesBound bound values) :
    SourceClosure { f with code := .IFELSE bt yes no :: after }
      { f with code := .BLOCK bt (if condition then yes else no) :: after, vals := values } := by
  refine ⟨SyntaxClosure.ifChoice f bt yes no after condition values, ?_, fun bound h => ⟨h.1, references bound h.2⟩⟩
  rintro bound ⟨size, labels⟩
  refine ⟨?_, labels⟩
  cases condition <;> simp at size ⊢ <;> omega

theorem SourceClosure.loop (f : Abs.AFrame) (bt : blocktype) (body after : List instr)
    (params results : List valtype) (height : Nat) :
    SourceClosure { f with code := .LOOP bt body :: after }
      { f with code := body, labels := ⟨params, results, [.LOOP bt body], height, after⟩ :: f.labels } := by
  refine ⟨SyntaxClosure.loop f bt body after params results height, ?_, fun _ h => h⟩
  rintro bound ⟨size, labels⟩
  constructor
  · simp at size ⊢
    omega
  · intro label member
    rcases List.mem_cons.mp member with rfl | member
    · simpa using size
    · exact labels label member

theorem SourceClosure.block (f : Abs.AFrame) (bt : blocktype) (body after : List instr)
    (results : List valtype) (height : Nat) :
    SourceClosure { f with code := .BLOCK bt body :: after }
      { f with code := body, labels := ⟨results, results, [], height, after⟩ :: f.labels } := by
  refine ⟨SyntaxClosure.block f bt body after results height, ?_, fun _ h => h⟩
  rintro bound ⟨size, labels⟩
  constructor
  · simp at size ⊢
    omega
  · intro label member
    rcases List.mem_cons.mp member with rfl | member
    · simp at size ⊢
      omega
    · exact labels label member

theorem SourceClosure.label (f : Abs.AFrame) (label : Abs.Label) (labels : List Abs.Label) :
    SourceClosure { f with code := [], labels := label :: labels }
      { f with code := label.after, labels := labels } := by
  refine ⟨SyntaxClosure.label f label labels, ?_, fun _ h => h⟩
  rintro bound ⟨size, saved⟩
  have full := saved label (List.mem_cons_self ..)
  have appended := Abs.list_size_append label.cont label.after
  have positive : 1 ≤ sizeOf label.cont := by cases label.cont <;> simp <;> omega
  exact ⟨by change sizeOf label.after ≤ bound; omega, fun next member => saved next (List.mem_cons_of_mem _ member)⟩

theorem SourceClosure.slice {before after} (closure : SourceClosure before after)
    {s : store} {ambient : frame} {rest : List Abs.AFrame}
    (slice : Abs.SliceState ⟨s, ambient, before :: rest, []⟩) :
    Abs.SliceState ⟨s, ambient, after :: rest, []⟩ := closure.allowed.slice slice

theorem SourceClosure.codeBound {before after} (closure : SourceClosure before after)
    {s : store} {ambient : frame} {rest : List Abs.AFrame} {bound : Nat}
    (bounded : Abs.CodeBound bound ⟨s, ambient, before :: rest, []⟩) :
    Abs.CodeBound bound ⟨s, ambient, after :: rest, []⟩ :=
  Abs.bound_replace_frame bounded (closure.bounded bound (bounded.frames before (List.mem_cons_self ..)))

theorem SourceClosure.referenceBound {before after} (closure : SourceClosure before after)
    {s : store} {ambient : frame} {rest : List Abs.AFrame} {bound : Nat}
    (bounded : Abs.StateReferencesBound bound ⟨s, ambient, before :: rest, []⟩) :
    Abs.StateReferencesBound bound ⟨s, ambient, after :: rest, []⟩ := by
  refine ⟨bounded.1, ?_⟩
  intro item member
  rcases List.mem_cons.mp member with rfl | member
  · exact closure.references bound (bounded.2 before (List.mem_cons_self ..))
  · exact bounded.2 item (List.mem_cons_of_mem _ member)

end Exec.Interp
