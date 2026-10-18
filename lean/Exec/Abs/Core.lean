import Exec.Abs.SliceInversion
import Exec.Abs.Memory.Descriptor

namespace Exec.Abs

/-- Source syntax for the mutable scalar extension. This grammar records the
intended coverage; its constructors do not assert execution or compilation
correctness. The established immutable slice remains a separate specialization. -/
inductive CoreInstr : instr → Prop where
  | slice {instruction} : SliceInstr instruction → CoreInstr instruction
  | constant (ty : numtype) (value : num_) : CoreInstr (.CONST ty value)
  | select : CoreInstr (.SELECT none)
  | global_get (index : idx) : CoreInstr (.GLOBAL_GET index)
  | global_set (index : idx) : CoreInstr (.GLOBAL_SET index)
  | load (op : Memory.Load) (argument : memarg) : CoreInstr (op.source argument)
  | store (op : Memory.Store) (argument : memarg) : CoreInstr (op.source argument)
  | block (ty : blocktype) (body : List instr) :
      Forall CoreInstr body → CoreInstr (.BLOCK ty body)
  | loop (ty : blocktype) (body : List instr) :
      Forall CoreInstr body → CoreInstr (.LOOP ty body)
  | ifelse (ty : blocktype) (yes no : List instr) :
      Forall CoreInstr yes → Forall CoreInstr no → CoreInstr (.IFELSE ty yes no)

def FrameCore (f : AFrame) : Prop :=
  Forall CoreInstr f.code ∧ Forall (fun label =>
    Forall CoreInstr label.cont ∧ Forall CoreInstr label.after) f.labels

/-- Defined bodies use the scalar grammar. Host entries are admitted as syntax;
executing them requires separate host laws and yields an explicit host boundary. -/
def CoreFunctions (s : store) : Prop :=
  ∀ function ∈ s.FUNCS, match function.CODE with
    | .HOST _ => True
    | .FUNC _ _ body => Forall CoreInstr body

structure CoreState (s : AState) : Prop where
  active : Forall FrameCore s.frames
  functions : CoreFunctions s.store

theorem CoreFunctions.same {before after : store}
    (same : after.FUNCS = before.FUNCS) (functions : CoreFunctions before) : CoreFunctions after := by
  simpa only [CoreFunctions, same] using functions

theorem CoreState.store_same {state : AState} {after : store}
    (same : after.FUNCS = state.store.FUNCS) (covered : CoreState state) :
    CoreState {state with store := after} := ⟨covered.active, covered.functions.same same⟩

theorem SliceState.core {s : AState} (covered : SliceState s) : CoreState s := by
  refine ⟨?_, ?_⟩
  · intro f member
    have frame := covered.active f member
    exact ⟨fun i found => .slice (frame.1 i found), fun label found =>
      ⟨fun i found' => .slice ((frame.2 label found).1 i found'),
       fun i found' => .slice ((frame.2 label found).2 i found')⟩⟩
  · intro function member
    have body := covered.functions function member
    cases code : function.CODE with
    | HOST host => trivial
    | FUNC signature locals source =>
      rw [code] at body
      exact fun i found => .slice (body i found)

theorem CoreInstr.block_body {ty body} (covered : CoreInstr (.BLOCK ty body)) :
    Forall CoreInstr body := by
  cases covered with
  | slice pure =>
    have inner := SliceInstr.block_inv pure
    exact fun i found => .slice (inner i found)
  | block _ _ body => exact body

theorem CoreInstr.loop_body {ty body} (covered : CoreInstr (.LOOP ty body)) :
    Forall CoreInstr body := by
  cases covered with
  | slice pure =>
    have inner := SliceInstr.loop_inv pure
    exact fun i found => .slice (inner i found)
  | loop _ _ body => exact body

theorem CoreInstr.if_bodies {ty yes no} (covered : CoreInstr (.IFELSE ty yes no)) :
    Forall CoreInstr yes ∧ Forall CoreInstr no := by
  cases covered with
  | slice pure =>
    have inner := SliceInstr.if_inv pure
    exact ⟨fun i found => .slice (inner.1 i found), fun i found => .slice (inner.2 i found)⟩
  | ifelse _ _ _ yes no => exact ⟨yes,no⟩

end Exec.Abs
