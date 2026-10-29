import Itasca.Runtime.SourceMachine.Ownership.Bounds

namespace Itasca.Runtime.Abs.Ownership

/-- Publication may enlarge either reference namespace. Existing references
remain owned only when both address bounds are retained. -/
structure Bounds.Extends (before after : Bounds) : Prop where
  functions : before.functions ≤ after.functions
  externs : before.externs ≤ after.externs

theorem ValueOwned.extend {before after value} (extension : before.Extends after)
    (owned : ValueOwned before value) : ValueOwned after value := by
  cases value <;> try trivial
  · exact owned.trans_le extension.functions
  · exact owned.trans_le extension.externs

theorem ValuesOwned.extend {before after values} (extension : before.Extends after)
    (owned : ValuesOwned before values) : ValuesOwned after values :=
  fun value member => (owned value member).extend extension

theorem FrameOwned.extend {before after frame} (extension : before.Extends after)
    (owned : FrameOwned before frame) : FrameOwned after frame :=
  ⟨owned.1.extend extension,owned.2.extend extension⟩

theorem StateOwned.extend {before after source} (extension : before.Extends after)
    (owned : StateOwned before source) : StateOwned after source :=
  ⟨owned.1.extend extension,fun frame member => (owned.2 frame member).extend extension⟩

/-- A resumed caller retains its locals and prefix operands; only the checked
host result values are added. Older suspended callers retain their ownership. -/
theorem StateOwned.host_return {before after : Bounds} {s target : store} {ambient : frame}
    {caller : AFrame} {rest : List AFrame} {front args returned : List val} {code : List instr}
    (extension : before.Extends after)
    (owned : StateOwned before ⟨s,ambient,caller::rest,[]⟩)
    (split : caller.vals=front++args) (results : ValuesOwned after returned) :
    StateOwned after ⟨target,ambient,{caller with code:=code,vals:=front++returned}::rest,[]⟩ := by
  have previous := owned.extend extension
  have current := previous.2 caller (List.mem_cons_self ..)
  refine ⟨valuesOwned_nil _,?_⟩
  intro item member
  rcases List.mem_cons.mp member with rfl | member
  · refine ⟨current.1,valuesOwned_append.mpr ⟨?_,results⟩⟩
    have operands := current.2
    rw [split] at operands
    exact (valuesOwned_append.mp operands).1
  · exact previous.2 item (List.mem_cons_of_mem _ member)
end Itasca.Runtime.Abs.Ownership
