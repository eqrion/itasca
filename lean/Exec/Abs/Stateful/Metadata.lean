import Exec.Abs.Stateful.Transition
namespace Itasca.Runtime.Abs.Stateful
open SpecExt Itasca.Runtime.Spec

theorem evaluate_frame (choice : Selection) (op : Instruction) (s : AState) (f : AFrame)
    (rest : List AFrame) (after : List instr) (next : AState)
    (result : evaluate choice op s f rest after = .next next) :
    ∃ values, next.frames = {f with code := after, vals := values}::rest ∧
      next.ambient = s.ambient ∧ next.results = s.results := by
  cases op <;> simp only [evaluate,refNull,refFunc,refIsNull,tableGet,tableSet,tableSize,tableGrow,
    tableFill,tableCopy,tableInit,elementDrop,memorySize,memoryGrow,memoryFill,memoryCopy,memoryInit,dataDrop] at result
  all_goals repeat first | split at result | contradiction
  all_goals cases result <;> exact ⟨_,rfl,rfl,rfl⟩

theorem transition_frame (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (op : Instruction) (next : AState) (step : Transition s f rest after op (.next next)) :
    ∃ values, next.frames = {f with code := after,vals := values}::rest ∧
      next.ambient = s.ambient ∧ next.results = s.results := by
  obtain ⟨choice,_,result⟩ := step
  exact evaluate_frame choice op s f rest after next result
theorem tableFill_functions (s : store) (f : frame) (index destination : Nat) (value : ref) (count : Nat) :
    (Segment.tableFill s f index destination value count).FUNCS = s.FUNCS := by
  induction count generalizing s destination with
  | zero => rfl
  | succ count ih => exact ih (Segment.tableWrite s f index destination value) (destination+1)

theorem memoryFill_functions (s : store) (f : frame) (destination value count : Nat) :
    (Segment.memoryFill s f destination value count).FUNCS = s.FUNCS := by
  induction count generalizing s destination with
  | zero => rfl
  | succ count ih => exact ih (Segment.memoryWrite s f destination (Segment.fillByte value)) (Segment.next32 destination)

theorem memoryInit_functions (s : store) (f : frame) (index destination source count : Nat) :
    (Segment.memoryInit s f index destination source count).FUNCS = s.FUNCS := by
  induction count generalizing s destination source with
  | zero => rfl
  | succ count ih => exact ih _ _ _

theorem tableInit_functions (s : store) (f : frame) (index sourceIndex destination source count : Nat) :
    (Segment.tableInit s f index sourceIndex destination source count).FUNCS = s.FUNCS := by
  rw [Segment.tableInit_eq]

theorem evaluate_functions (choice : Selection) (op : Instruction) (s : AState) (f : AFrame)
    (rest : List AFrame) (after : List instr) (next : AState)
    (result : evaluate choice op s f rest after = .next next) : next.store.FUNCS = s.store.FUNCS := by
  cases op <;> simp only [evaluate,refNull,refFunc,refIsNull,tableGet,tableSet,tableSize,tableGrow,
    tableFill,tableCopy,tableInit,elementDrop,memorySize,memoryGrow,memoryFill,memoryCopy,memoryInit,dataDrop,advance] at result
  all_goals repeat' first | split at result | contradiction
  all_goals cases result
  all_goals first | rfl | apply tableFill_functions | apply memoryFill_functions | apply tableInit_functions | apply memoryInit_functions

theorem transition_functions (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (op : Instruction) (next : AState) (step : Transition s f rest after op (.next next)) :
    next.store.FUNCS = s.store.FUNCS := by
  obtain ⟨choice,_,result⟩ := step
  exact evaluate_functions choice op s f rest after next result
end Itasca.Runtime.Abs.Stateful
