import Exec.Abs.State

namespace Exec.Abs

/-- Source support is independent of values and concrete bytecode emission. -/
def FrameSupported (allowed : instr → Prop) (f : AFrame) : Prop :=
  Forall allowed f.code ∧ Forall (fun label => Forall allowed label.cont ∧ Forall allowed label.after) f.labels

def FunctionsSupported (allowed : instr → Prop) (s : store) : Prop :=
  ∀ function ∈ s.FUNCS, match function.CODE with
    | .HOST _ => True
    | .FUNC _ _ body => Forall allowed body

structure SupportedState (allowed : instr → Prop) (s : AState) : Prop where
  active : Forall (FrameSupported allowed) s.frames
  functions : FunctionsSupported allowed s.store

theorem FunctionsSupported.same {allowed : instr → Prop} {before after : store}
    (functions : FunctionsSupported allowed before) (same : after.FUNCS = before.FUNCS) :
    FunctionsSupported allowed after := by simpa only [FunctionsSupported,same] using functions

theorem SupportedState.tail {allowed : instr → Prop} {before afterStore : store}
    {ambient : frame} {f : AFrame} {rest : List AFrame} {op : instr} {after : List instr}
    (covered : SupportedState allowed ⟨before,ambient,{f with code := op::after}::rest,[]⟩)
    (same : afterStore.FUNCS = before.FUNCS) (values : List val) :
    SupportedState allowed ⟨afterStore,ambient,{f with code := after, vals := values}::rest,[]⟩ := by
  refine ⟨?_,covered.functions.same same⟩
  intro item member
  rcases List.mem_cons.mp member with rfl | member
  · have old := covered.active _ (List.mem_cons_self ..)
    exact ⟨fun instruction member => old.1 instruction (List.mem_cons_of_mem _ member),old.2⟩
  · exact covered.active item (List.mem_cons_of_mem _ member)

theorem SupportedState.map {allowed other : instr → Prop} {s : AState}
    (covered : SupportedState allowed s) (embed : ∀ source, allowed source → other source) :
    SupportedState other s := by
  refine ⟨?_,?_⟩
  · intro f member
    obtain ⟨code,labels⟩ := covered.active f member
    exact ⟨fun i hi => embed i (code i hi),fun l hl =>
      ⟨fun i hi => embed i ((labels l hl).1 i hi),fun i hi => embed i ((labels l hl).2 i hi)⟩⟩
  · intro fn member
    have old := covered.functions fn member
    cases h : fn.CODE with
    | HOST id => trivial
    | FUNC index locals body =>
      simp only [FunctionsSupported,h] at old ⊢
      exact fun i hi => embed i (old i hi)

end Exec.Abs
