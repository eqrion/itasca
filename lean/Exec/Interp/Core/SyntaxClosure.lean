import Exec.Interp.Core.StoreTransport
import Exec.Interp.Control.StructuredPoint
namespace Exec.Interp
/-- Syntactic closure is retained independently of value typing. -/
def CoreSyntaxClosure (before after : Abs.AFrame) : Prop := Abs.FrameCore before → Abs.FrameCore after

theorem CoreSyntaxClosure.refl (f : Abs.AFrame) : CoreSyntaxClosure f f := fun h => h

theorem CoreSyntaxClosure.trans {before middle after} (first : CoreSyntaxClosure before middle)
    (second : CoreSyntaxClosure middle after) : CoreSyntaxClosure before after := fun h => second (first h)

theorem CoreSyntaxClosure.tail (f : Abs.AFrame) (op : instr) (after : List instr)
    (locals values : List val) :
    CoreSyntaxClosure { f with code := op :: after } { f with code := after, locals := locals, vals := values } := by
  rintro ⟨code, labels⟩
  exact ⟨fun i hi => code i (List.mem_cons_of_mem _ hi), labels⟩

theorem CoreSyntaxClosure.replace (f : Abs.AFrame) (op next : instr) (after : List instr)
    (locals values : List val) (allowed : Abs.CoreInstr next) :
    CoreSyntaxClosure { f with code := op :: after } { f with code := next :: after, locals := locals, vals := values } := by
  rintro ⟨code, labels⟩
  refine ⟨?_, labels⟩
  intro i hi
  rcases List.mem_cons.mp hi with rfl | member
  · exact allowed
  · exact code i (List.mem_cons_of_mem _ member)

theorem CoreSyntaxClosure.branch (f : Abs.AFrame) (depth : Nat) (label : Abs.Label)
    (lookup : f.labels[depth]? = some label) (values : List val) :
    CoreSyntaxClosure f { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := values } := by
  rintro ⟨code, labels⟩
  have retained := labels label (List.mem_of_getElem? lookup)
  constructor
  · intro i hi
    rcases List.mem_append.mp hi with member | member
    · exact retained.1 i member
    · exact retained.2 i member
  · intro next member
    exact labels next (List.mem_of_mem_drop member)

theorem CoreSyntaxClosure.ifChoice (f : Abs.AFrame) (bt : blocktype) (yes no after : List instr)
    (condition : Bool) (values : List val) :
    CoreSyntaxClosure { f with code := .IFELSE bt yes no :: after }
      { f with code := .BLOCK bt (if condition then yes else no) :: after, vals := values } := by
  rintro ⟨code, labels⟩
  have head := code (.IFELSE bt yes no) (List.mem_cons_self ..)
  obtain ⟨yesAllowed, noAllowed⟩ := head.if_bodies
  refine ⟨?_, labels⟩
  intro i hi
  rcases List.mem_cons.mp hi with rfl | member
  · apply Abs.CoreInstr.block
    cases condition <;> assumption
  · exact code i (List.mem_cons_of_mem _ member)

theorem CoreSyntaxClosure.loop (f : Abs.AFrame) (bt : blocktype) (body after : List instr)
    (params results : List valtype) (height : Nat) :
    CoreSyntaxClosure { f with code := .LOOP bt body :: after }
      { f with code := body, labels := ⟨params, results, [.LOOP bt body], height, after⟩ :: f.labels } := by
  rintro ⟨code, labels⟩
  have head := code (.LOOP bt body) (List.mem_cons_self ..)
  have bodyAllowed : Forall Abs.CoreInstr body := head.loop_body
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

theorem CoreSyntaxClosure.block (f : Abs.AFrame) (bt : blocktype) (body after : List instr)
    (results : List valtype) (height : Nat) :
    CoreSyntaxClosure { f with code := .BLOCK bt body :: after }
      { f with code := body, labels := ⟨results, results, [], height, after⟩ :: f.labels } := by
  rintro ⟨code, labels⟩
  have head := code (.BLOCK bt body) (List.mem_cons_self ..)
  have bodyAllowed : Forall Abs.CoreInstr body := head.block_body
  refine ⟨bodyAllowed, ?_⟩
  intro label member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨by intro i hi; simp at hi, fun i hi => code i (List.mem_cons_of_mem _ hi)⟩
  · exact labels label member

theorem CoreSyntaxClosure.label (f : Abs.AFrame) (label : Abs.Label) (labels : List Abs.Label) :
    CoreSyntaxClosure { f with code := [], labels := label :: labels }
      { f with code := label.after, labels := labels } := by
  rintro ⟨code, saved⟩
  exact ⟨(saved label (List.mem_cons_self ..)).2,
    fun next member => saved next (List.mem_cons_of_mem _ member)⟩

theorem CoreSyntaxClosure.state {before after} (closure : CoreSyntaxClosure before after)
    {s : store} {ambient : frame} {rest : List Abs.AFrame}
    (slice : Abs.CoreState ⟨s, ambient, before :: rest, []⟩) :
    Abs.CoreState ⟨s, ambient, after :: rest, []⟩ :=
  Abs.core_replace_frame slice (closure (slice.active _ (List.mem_cons_self ..)))



end Exec.Interp
