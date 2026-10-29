import Itasca.Runtime.SourceMachine.State
import Itasca.Runtime.SourceMachine.BinaryInstr

/-!
Source instruction-support certificates for active frames and stored functions. This grammar restriction is independent of runtime bytecode and concrete values.
-/

namespace Itasca.Runtime.SourceMachine

/-- Source support is independent of values and concrete bytecode emission. -/
def FrameSupported (f : AFrame) : Prop :=
  Forall BinaryInstr f.code ∧ Forall (fun label => Forall BinaryInstr label.cont ∧ Forall BinaryInstr label.after) f.labels

def FunctionsSupported (s : store) : Prop :=
  ∀ function ∈ s.FUNCS, match function.CODE with
    | .HOST _ => True
    | .FUNC _ _ body => Forall BinaryInstr body

structure SupportedState (s : AState) : Prop where
  active : Forall (FrameSupported) s.frames
  functions : FunctionsSupported s.store

theorem FunctionsSupported.same {before after : store}
    (functions : FunctionsSupported before) (same : after.FUNCS = before.FUNCS) :
    FunctionsSupported after := by simpa only [FunctionsSupported,same] using functions

theorem SupportedState.tail {before afterStore : store}
    {ambient : frame} {f : AFrame} {rest : List AFrame} {op : instr} {after : List instr}
    (covered : SupportedState ⟨before,ambient,{f with code := op::after}::rest,[]⟩)
    (same : afterStore.FUNCS = before.FUNCS) (values : List val) :
    SupportedState ⟨afterStore,ambient,{f with code := after, vals := values}::rest,[]⟩ := by
  refine ⟨?_,covered.functions.same same⟩
  intro item member
  rcases List.mem_cons.mp member with rfl | member
  · have old := covered.active _ (List.mem_cons_self ..)
    exact ⟨fun instruction member => old.1 instruction (List.mem_cons_of_mem _ member),old.2⟩
  · exact covered.active item (List.mem_cons_of_mem _ member)

end Itasca.Runtime.SourceMachine
