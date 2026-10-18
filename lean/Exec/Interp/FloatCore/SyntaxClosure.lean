import Exec.Abs.FloatCoreState
import Exec.Interp.Control.StructuredPoint
namespace Exec.Abs

theorem float_core_replace_frame {s : store} {ambient : frame} {f f' : AFrame}
    {rest : List AFrame} (covered : FloatCoreState ⟨s,ambient,f::rest,[]⟩)
    (fresh : FrameFloatCore f') : FloatCoreState ⟨s,ambient,f'::rest,[]⟩ := by
  refine ⟨?_,covered.functions⟩
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · exact fresh
  · exact covered.active frame (List.mem_cons_of_mem _ member)

theorem FloatCoreState.instruction_tail {s nextStore : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {op : instr} {after : List instr}
    (covered : FloatCoreState ⟨s,ambient,{f with code := op::after}::rest,[]⟩)
    (functions : nextStore.FUNCS = s.FUNCS) (locals values : List val) :
    FloatCoreState ⟨nextStore,ambient,{f with code := after,locals := locals,vals := values}::rest,[]⟩ := by
  have frame := covered.active _ (List.mem_cons_self ..)
  have old : FloatCoreState ⟨s,ambient,{f with code := after,locals := locals,vals := values}::rest,[]⟩ :=
    float_core_replace_frame covered ⟨fun instruction member => frame.1 instruction (List.mem_cons_of_mem _ member),frame.2⟩
  exact old.store_same functions

end Exec.Abs

namespace Exec.Interp
/-- Syntactic closure is retained independently of value typing. -/
def FloatCoreSyntaxClosure (before after : Abs.AFrame) : Prop := Abs.FrameFloatCore before → Abs.FrameFloatCore after

theorem FloatCoreSyntaxClosure.refl (f : Abs.AFrame) : FloatCoreSyntaxClosure f f := fun h => h

theorem FloatCoreSyntaxClosure.trans {before middle after} (first : FloatCoreSyntaxClosure before middle)
    (second : FloatCoreSyntaxClosure middle after) : FloatCoreSyntaxClosure before after := fun h => second (first h)

theorem FloatCoreSyntaxClosure.tail (f : Abs.AFrame) (op : instr) (after : List instr)
    (locals values : List val) :
    FloatCoreSyntaxClosure { f with code := op :: after } { f with code := after, locals := locals, vals := values } := by
  rintro ⟨code, labels⟩
  exact ⟨fun i hi => code i (List.mem_cons_of_mem _ hi), labels⟩

theorem FloatCoreSyntaxClosure.replace (f : Abs.AFrame) (op next : instr) (after : List instr)
    (locals values : List val) (allowed : Abs.FloatCoreInstr next) :
    FloatCoreSyntaxClosure { f with code := op :: after } { f with code := next :: after, locals := locals, vals := values } := by
  rintro ⟨code, labels⟩
  refine ⟨?_, labels⟩
  intro i hi
  rcases List.mem_cons.mp hi with rfl | member
  · exact allowed
  · exact code i (List.mem_cons_of_mem _ member)

theorem FloatCoreSyntaxClosure.branch (f : Abs.AFrame) (depth : Nat) (label : Abs.Label)
    (lookup : f.labels[depth]? = some label) (values : List val) :
    FloatCoreSyntaxClosure f { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := values } := by
  rintro ⟨code, labels⟩
  have retained := labels label (List.mem_of_getElem? lookup)
  constructor
  · intro i hi
    rcases List.mem_append.mp hi with member | member
    · exact retained.1 i member
    · exact retained.2 i member
  · intro next member
    exact labels next (List.mem_of_mem_drop member)

theorem FloatCoreSyntaxClosure.ifChoice (f : Abs.AFrame) (bt : blocktype) (yes no after : List instr)
    (condition : Bool) (values : List val) :
    FloatCoreSyntaxClosure { f with code := .IFELSE bt yes no :: after }
      { f with code := .BLOCK bt (if condition then yes else no) :: after, vals := values } := by
  rintro ⟨code, labels⟩
  have head := code (.IFELSE bt yes no) (List.mem_cons_self ..)
  obtain ⟨yesAllowed, noAllowed⟩ := head.if_bodies
  refine ⟨?_, labels⟩
  intro i hi
  rcases List.mem_cons.mp hi with rfl | member
  · apply Abs.FloatCoreInstr.block
    cases condition <;> assumption
  · exact code i (List.mem_cons_of_mem _ member)

theorem FloatCoreSyntaxClosure.loop (f : Abs.AFrame) (bt : blocktype) (body after : List instr)
    (params results : List valtype) (height : Nat) :
    FloatCoreSyntaxClosure { f with code := .LOOP bt body :: after }
      { f with code := body, labels := ⟨params, results, [.LOOP bt body], height, after⟩ :: f.labels } := by
  rintro ⟨code, labels⟩
  have head := code (.LOOP bt body) (List.mem_cons_self ..)
  have bodyAllowed : Forall Abs.FloatCoreInstr body := head.loop_body
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

theorem FloatCoreSyntaxClosure.block (f : Abs.AFrame) (bt : blocktype) (body after : List instr)
    (results : List valtype) (height : Nat) :
    FloatCoreSyntaxClosure { f with code := .BLOCK bt body :: after }
      { f with code := body, labels := ⟨results, results, [], height, after⟩ :: f.labels } := by
  rintro ⟨code, labels⟩
  have head := code (.BLOCK bt body) (List.mem_cons_self ..)
  have bodyAllowed : Forall Abs.FloatCoreInstr body := head.block_body
  refine ⟨bodyAllowed, ?_⟩
  intro label member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨by intro i hi; simp at hi, fun i hi => code i (List.mem_cons_of_mem _ hi)⟩
  · exact labels label member

theorem FloatCoreSyntaxClosure.label (f : Abs.AFrame) (label : Abs.Label) (labels : List Abs.Label) :
    FloatCoreSyntaxClosure { f with code := [], labels := label :: labels }
      { f with code := label.after, labels := labels } := by
  rintro ⟨code, saved⟩
  exact ⟨(saved label (List.mem_cons_self ..)).2,
    fun next member => saved next (List.mem_cons_of_mem _ member)⟩

theorem FloatCoreSyntaxClosure.state {before after} (closure : FloatCoreSyntaxClosure before after)
    {s : store} {ambient : frame} {rest : List Abs.AFrame}
    (slice : Abs.FloatCoreState ⟨s, ambient, before :: rest, []⟩) :
    Abs.FloatCoreState ⟨s, ambient, after :: rest, []⟩ :=
  ⟨fun f member => by
    rcases List.mem_cons.mp member with rfl | member
    · exact closure (slice.active _ (List.mem_cons_self ..))
    · exact slice.active f (List.mem_cons_of_mem _ member), slice.functions⟩



end Exec.Interp
