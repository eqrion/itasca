import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.SourceMachine.ReferenceBounds
import Itasca.Runtime.Interp.Control.StructuredPoint

namespace Itasca.Runtime.Interp

/-- Every ordinary source rearrangement preserves an arbitrary pre-existing finite bound on source continuations. -/
structure SourceClosure (before after : SourceMachine.AFrame) : Prop where
  bounded : ∀ bound, SourceMachine.FrameCodeBound bound before → SourceMachine.FrameCodeBound bound after
  references : ∀ bound, SourceMachine.FrameReferencesBound bound before → SourceMachine.FrameReferencesBound bound after

theorem SourceClosure.refl (f : SourceMachine.AFrame) : SourceClosure f f := ⟨fun _ h => h, fun _ h => h⟩

theorem SourceClosure.trans {before middle after} (first : SourceClosure before middle)
    (second : SourceClosure middle after) : SourceClosure before after :=
  ⟨fun bound h => second.bounded bound (first.bounded bound h),
    fun bound h => second.references bound (first.references bound h)⟩

theorem SourceClosure.tail (f : SourceMachine.AFrame) (op : instr) (after : List instr)
    (locals values : List val)
    (references : ∀ bound, SourceMachine.FrameReferencesBound bound f → SourceMachine.ValuesBound bound locals ∧ SourceMachine.ValuesBound bound values) :
    SourceClosure { f with code := op :: after } { f with code := after, locals := locals, vals := values } := by
  refine ⟨?_, references⟩
  rintro bound ⟨size, labels⟩
  refine ⟨?_, labels⟩
  change sizeOf after ≤ bound
  simp only [List.cons.sizeOf_spec] at size
  omega

theorem SourceClosure.if_choice (f : SourceMachine.AFrame) (bt : blocktype) (yes no after : List instr)
    (condition : Bool) (values : List val)
    (references : ∀ bound, SourceMachine.ValuesBound bound f.vals → SourceMachine.ValuesBound bound values) :
    SourceClosure { f with code := .IFELSE bt yes no :: after }
      { f with code := .BLOCK bt (if condition then yes else no) :: after, vals := values } := by
  refine ⟨?_, fun bound h => ⟨h.1, references bound h.2⟩⟩
  rintro bound ⟨size, labels⟩
  refine ⟨?_, labels⟩
  cases condition <;> simp at size ⊢ <;> omega

theorem SourceClosure.loop (f : SourceMachine.AFrame) (bt : blocktype) (body after : List instr)
    (params results : List valtype) (height : Nat) :
    SourceClosure { f with code := .LOOP bt body :: after }
      { f with code := body, labels := ⟨params, results, [.LOOP bt body], height, after⟩ :: f.labels } := by
  refine ⟨?_, fun _ h => h⟩
  rintro bound ⟨size, labels⟩
  constructor
  · simp at size ⊢
    omega
  · intro label member
    rcases List.mem_cons.mp member with rfl | member
    · simpa using size
    · exact labels label member

theorem SourceClosure.block (f : SourceMachine.AFrame) (bt : blocktype) (body after : List instr)
    (results : List valtype) (height : Nat) :
    SourceClosure { f with code := .BLOCK bt body :: after }
      { f with code := body, labels := ⟨results, results, [], height, after⟩ :: f.labels } := by
  refine ⟨?_, fun _ h => h⟩
  rintro bound ⟨size, labels⟩
  constructor
  · simp at size ⊢
    omega
  · intro label member
    rcases List.mem_cons.mp member with rfl | member
    · simp at size ⊢
      omega
    · exact labels label member

theorem SourceClosure.label (f : SourceMachine.AFrame) (label : SourceMachine.Label) (labels : List SourceMachine.Label) :
    SourceClosure { f with code := [], labels := label :: labels }
      { f with code := label.after, labels := labels } := by
  refine ⟨?_, fun _ h => h⟩
  rintro bound ⟨size, saved⟩
  have full := saved label (List.mem_cons_self ..)
  have appended := SourceMachine.list_size_append label.cont label.after
  have positive : 1 ≤ sizeOf label.cont := by cases label.cont <;> simp <;> omega
  exact ⟨by change sizeOf label.after ≤ bound; omega, fun next member => saved next (List.mem_cons_of_mem _ member)⟩

theorem SourceClosure.code_bound {before after} (closure : SourceClosure before after)
    {s : store} {ambient : frame} {rest : List SourceMachine.AFrame} {bound : Nat}
    (bounded : SourceMachine.CodeBound bound ⟨s, ambient, before :: rest, []⟩) :
    SourceMachine.CodeBound bound ⟨s, ambient, after :: rest, []⟩ :=
  SourceMachine.bound_replace_frame bounded (closure.bounded bound (bounded.frames before (List.mem_cons_self ..)))

end Itasca.Runtime.Interp
