import Exec.Spec.Wf

namespace Exec.Spec

/-- Only the directly reduced numeric operator consumes a pure choice. Dead
continuations after a branch, return, or trap are not evaluated. -/
def pureRedexUsesChoice : List admininstr → Bool
  | [.CONST _ _,.UNOP _ _] => true
  | [.CONST _ _,.CONST _ _,.BINOP _ _] => true
  | [.CONST _ _,.CVTOP _ _ _] => true
  | [.VCONST _ _,.VUNOP _ _] => true
  | [.VCONST _ _,.VCONST _ _,.VBINOP _ _] => true
  | [.VCONST _ _,.VCVTOP _ _ _] => true
  | _ => false

def ChoiceFreePureRedex (body : List admininstr) : Prop :=
  pureRedexUsesChoice body = false

/-- Atomic store-changing redexes whose source rules do not consume a numeric,
growth, or host choice. Constants contain no suspended computation. -/
inductive ChoiceFreeWriteRedex : List admininstr → Prop where
  | local (value : val) (index : idx) : ChoiceFreeWriteRedex [admininstr_val value,.LOCAL_SET index]
  | global (value : val) (index : idx) : ChoiceFreeWriteRedex [admininstr_val value,.GLOBAL_SET index]
  | table (position : num_) (value : ref) (index : idx) :
      ChoiceFreeWriteRedex [.CONST .I32 position,admininstr_ref value,.TABLE_SET index]
  | elementDrop (index : idx) : ChoiceFreeWriteRedex [.ELEM_DROP index]
  | store (position value : num_) (type : numtype) (packed : Option sz) (argument : memarg) :
      ChoiceFreeWriteRedex [.CONST .I32 position,.CONST type value,.STORE type packed argument]
  | vectorStore (position : num_) (value : vec_) (argument : memarg) :
      ChoiceFreeWriteRedex [.CONST .I32 position,.VCONST .V128 value,.VSTORE .V128 argument]
  | laneStore (position : num_) (value : vec_) (width : sz) (argument : memarg) (lane : laneidx) :
      ChoiceFreeWriteRedex [.CONST .I32 position,.VCONST .V128 value,.VSTORE_LANE .V128 width argument lane]
  | dataDrop (index : idx) : ChoiceFreeWriteRedex [.DATA_DROP index]

/-- Control-rule classification inspects only the actual reduced pure redex,
so inactive numeric instructions after a branch do not require choices. -/
theorem label_redex_choice_free (arity : Nat) (continuation : List instr) (body : List admininstr) :
    ChoiceFreePureRedex [.LABEL_ arity continuation body] := by
  simp [ChoiceFreePureRedex,pureRedexUsesChoice]

theorem frame_redex_choice_free (arity : Nat) (frame : _root_.frame) (body : List admininstr) :
    ChoiceFreePureRedex [.FRAME_ arity frame body] := by
  simp [ChoiceFreePureRedex,pureRedexUsesChoice]

/-- A choosing pure redex contains only its operands and numeric operator. -/
theorem choosing_pure_has_no_trap {body : List admininstr} (choosing : pureRedexUsesChoice body = true) :
    admininstr.TRAP ∉ body := by
  unfold pureRedexUsesChoice at choosing
  split at choosing <;> simp_all

/-- Trap propagation discards arbitrary following instructions, including
choosing operators, without executing those operators. -/
theorem trap_redex_choice_free (front : List val) (tail : List admininstr) :
    ChoiceFreePureRedex (SpecExt.vals front++[.TRAP]++tail) := by
  have present : admininstr.TRAP ∈ SpecExt.vals front++[.TRAP]++tail := by simp
  cases selected : pureRedexUsesChoice (SpecExt.vals front++[.TRAP]++tail) with
  | false => exact selected
  | true => exact False.elim (choosing_pure_has_no_trap selected present)

end Exec.Spec
