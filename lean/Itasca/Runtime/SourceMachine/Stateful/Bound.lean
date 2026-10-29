import Itasca.Runtime.SourceMachine.Stateful.Transition
import Itasca.Runtime.SourceMachine.Bound

/-!
Stateful transition metadata and code-bound preservation, consumed by cumulative execution.
-/

/-! ## Metadata -/

section

namespace Itasca.Runtime.SourceMachine.Stateful
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
theorem table_fill_functions (s : store) (f : frame) (index destination : Nat) (value : ref) (count : Nat) :
    (Segment.tableFill s f index destination value count).FUNCS = s.FUNCS := by
  induction count generalizing s destination with
  | zero => rfl
  | succ count ih => exact ih (Segment.tableWrite s f index destination value) (destination+1)

theorem memory_fill_functions (s : store) (f : frame) (destination value count : Nat) :
    (Segment.memoryFill s f destination value count).FUNCS = s.FUNCS := by
  induction count generalizing s destination with
  | zero => rfl
  | succ count ih => exact ih (Segment.memoryWrite s f destination (Segment.fillByte value)) (Segment.next32 destination)

theorem memory_init_functions (s : store) (f : frame) (index destination source count : Nat) :
    (Segment.memoryInit s f index destination source count).FUNCS = s.FUNCS := by
  induction count generalizing s destination source with
  | zero => rfl
  | succ count ih => exact ih _ _ _

theorem table_init_functions (s : store) (f : frame) (index sourceIndex destination source count : Nat) :
    (Segment.tableInit s f index sourceIndex destination source count).FUNCS = s.FUNCS := by
  rw [Segment.table_init_eq]

theorem evaluate_functions (choice : Selection) (op : Instruction) (s : AState) (f : AFrame)
    (rest : List AFrame) (after : List instr) (next : AState)
    (result : evaluate choice op s f rest after = .next next) : next.store.FUNCS = s.store.FUNCS := by
  cases op <;> simp only [evaluate,refNull,refFunc,refIsNull,tableGet,tableSet,tableSize,tableGrow,
    tableFill,tableCopy,tableInit,elementDrop,memorySize,memoryGrow,memoryFill,memoryCopy,memoryInit,dataDrop,advance] at result
  all_goals repeat' first | split at result | contradiction
  all_goals cases result
  all_goals first | rfl | apply table_fill_functions | apply memory_fill_functions | apply table_init_functions | apply memory_init_functions

theorem transition_functions (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (op : Instruction) (next : AState) (step : Transition s f rest after op (.next next)) :
    next.store.FUNCS = s.store.FUNCS := by
  obtain ⟨choice,_,result⟩ := step
  exact evaluate_functions choice op s f rest after next result
end Itasca.Runtime.SourceMachine.Stateful

end

/-! ## Bound -/

section

namespace Itasca.Runtime.SourceMachine.Stateful

theorem transition_bound (bound : Nat) (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr) (next : AState)
    (bounded : CodeBound bound ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op (.next next)) :
    CodeBound bound next := by
  obtain ⟨values,frames,_,_⟩ := transition_frame _ _ _ _ _ _ step
  have functions := transition_functions _ _ _ _ _ _ step
  have active := bounded.frames {f with code := op.source::after} (List.mem_cons_self ..)
  refine ⟨bounded.positive,?_,?_⟩
  · rw [frames]
    intro frame member
    rcases List.mem_cons.mp member with rfl | member
    · refine ⟨?_,active.2⟩
      have headBound : sizeOf (op.source::after) ≤ bound := active.1
      simp only [List.cons.sizeOf_spec] at headBound
      change sizeOf after ≤ bound
      omega
    · exact bounded.frames frame (List.mem_cons_of_mem _ member)
  · simpa only [functions] using bounded.functions
end Itasca.Runtime.SourceMachine.Stateful

end
