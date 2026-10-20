import Exec.Abs.Stateful.Transition
import Exec.Abs.Stateful.ChosenReference
import Exec.Abs.Stateful.ChosenTableRead
import Exec.Abs.Stateful.ChosenTableSet
import Exec.Abs.Stateful.ChosenMemorySize
import Exec.Abs.Stateful.ChosenDrops
import Exec.Abs.Stateful.ChosenMemoryFill
import Exec.Abs.Stateful.ChosenMemoryCopy
import Exec.Abs.Stateful.ChosenMemoryInit
import Exec.Abs.Stateful.ChosenTableFill
import Exec.Abs.Stateful.ChosenTableCopy
import Exec.Abs.Stateful.ChosenTableInit
import Exec.Abs.Stateful.ChosenMemoryGrow
import Exec.Abs.Stateful.ChosenTableGrow
namespace Exec.Abs.Stateful
open SpecExt Exec.Spec

def Selection.Matches (choice : Selection) (choices : SourceChoices) (occurrence : Nat) (op : Instruction) (s : store) (f : AFrame) : Prop :=
  match op with
  | .memoryGrow => ∀ front delta address object,
      f.vals = front ++ [integerVal .I32 delta] → f.module.MEMS[0]? = some address →
      s.MEMS[address]? = some object → choices.memory occurrence object delta = choice.memory
  | .tableGrow index => ∀ front reference delta address object,
      f.vals = front ++ [val_ref reference,integerVal .I32 delta] →
      f.module.TABLES[index]? = some address → s.TABLES[address]? = some object →
      choices.table occurrence object delta reference = choice.table
  | _ => True

/-- Growth replies match the independently specified policy at this source occurrence. -/
def ChosenTransition (choices : SourceChoices) (occurrence : Nat)
    (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (op : Instruction) (result : AResult) : Prop :=
  ∃ choice, choice.Allowed op s.store f ∧ choice.Matches choices occurrence op s.store f ∧
    evaluate choice op s f rest after = result

theorem ChosenTransition.erases {choices occurrence s f rest after op result}
    (step : ChosenTransition choices occurrence s f rest after op result) :
    Transition s f rest after op result := by
  obtain ⟨choice,allowed,_,result⟩ := step
  exact ⟨choice,allowed,result⟩
def ChosenResultSafe (choices : SourceChoices) (occurrence : Nat) (initial : AState) : AResult → Prop
  | .next next => CoreTyped next ∧ Extend_store initial.store next.store ∧ ChosenNextSim choices occurrence initial next
  | .trap => ∃ count, 0 < count ∧ ChosenStepsN choices occurrence count (decode initial) [] ⟨⟨initial.store,initial.ambient⟩,[.TRAP]⟩
  | _ => False

theorem evaluate_chosen_safe {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (choice : Selection) (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (allowed : choice.Allowed op s f) (matched : choice.Matches choices occurrence op s f) :
    ChosenResultSafe choices occurrence ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩
      (evaluate choice op ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after) := by
  cases op with
  | refNull type =>
    obtain ⟨next,result,fresh,simulation⟩ := refNull_chosen_progress admissible vector occurrence s ambient f rest type after typed
    have same := evaluate_read_store choice (.refNull type) ⟨s,ambient,{f with code := (.refNull type : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ChosenResultSafe choices occurrence _ (refNull _ f rest type after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | refFunc index =>
    obtain ⟨next,result,fresh,simulation⟩ := refFunc_chosen_progress admissible vector occurrence s ambient f rest index after typed
    have same := evaluate_read_store choice (.refFunc index) ⟨s,ambient,{f with code := (.refFunc index : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ChosenResultSafe choices occurrence _ (refFunc _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | refIsNull =>
    obtain ⟨next,result,fresh,simulation⟩ := refIsNull_chosen_progress admissible vector occurrence s ambient f rest after typed
    have same := evaluate_read_store choice (.refIsNull) ⟨s,ambient,{f with code := (.refIsNull : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ChosenResultSafe choices occurrence _ (refIsNull _ f rest after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | tableSize index =>
    obtain ⟨next,result,fresh,simulation⟩ := tableSize_chosen_progress admissible vector occurrence s ambient f rest index after typed
    have same := evaluate_read_store choice (.tableSize index) ⟨s,ambient,{f with code := (.tableSize index : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ChosenResultSafe choices occurrence _ (tableSize _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | memorySize =>
    obtain ⟨next,result,fresh,simulation⟩ := memorySize_chosen_progress admissible vector occurrence s ambient f rest after typed
    have same := evaluate_read_store choice (.memorySize) ⟨s,ambient,{f with code := (.memorySize : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ChosenResultSafe choices occurrence _ (memorySize _ f rest after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | tableGet index =>
    rcases tableGet_chosen_progress admissible vector occurrence s ambient f rest index after typed with ⟨next,result,fresh,simulation⟩ | ⟨result,trap⟩
    · have same := evaluate_read_store choice (.tableGet index) ⟨s,ambient,{f with code := (.tableGet index : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
      change ChosenResultSafe choices occurrence _ (tableGet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
    · change ChosenResultSafe choices occurrence _ (tableGet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableSet index =>
    rcases tableSet_chosen_progress admissible vector occurrence s ambient f rest index after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ChosenResultSafe choices occurrence _ (tableSet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ChosenResultSafe choices occurrence _ (tableSet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableFill index =>
    rcases tableFill_chosen_progress admissible vector occurrence s ambient f rest index after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ChosenResultSafe choices occurrence _ (tableFill _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ChosenResultSafe choices occurrence _ (tableFill _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableCopy index source =>
    rcases tableCopy_chosen_progress admissible vector occurrence s ambient f rest index source after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ChosenResultSafe choices occurrence _ (tableCopy _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ChosenResultSafe choices occurrence _ (tableCopy _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableInit index source =>
    rcases tableInit_chosen_progress admissible vector occurrence s ambient f rest index source after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ChosenResultSafe choices occurrence _ (tableInit _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ChosenResultSafe choices occurrence _ (tableInit _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | memoryFill =>
    rcases memoryFill_chosen_progress admissible vector occurrence s ambient f rest  after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ChosenResultSafe choices occurrence _ (memoryFill _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ChosenResultSafe choices occurrence _ (memoryFill _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | memoryCopy =>
    rcases memoryCopy_chosen_progress admissible vector occurrence s ambient f rest  after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ChosenResultSafe choices occurrence _ (memoryCopy _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ChosenResultSafe choices occurrence _ (memoryCopy _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | memoryInit index =>
    rcases memoryInit_chosen_progress admissible vector occurrence s ambient f rest index after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ChosenResultSafe choices occurrence _ (memoryInit _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ChosenResultSafe choices occurrence _ (memoryInit _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | elemDrop index =>
    obtain ⟨next,result,fresh,extended,simulation⟩ := elementDrop_chosen_progress admissible vector occurrence s ambient f rest index after typed
    change ChosenResultSafe choices occurrence _ (elementDrop _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩
  | dataDrop index =>
    obtain ⟨next,result,fresh,extended,simulation⟩ := dataDrop_chosen_progress admissible vector occurrence s ambient f rest index after typed
    change ChosenResultSafe choices occurrence _ (dataDrop _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩
  | memoryGrow =>
    obtain ⟨front,delta,address,object,values,mapped,found,alternatives⟩ := memoryGrow_chosen_choices admissible occurrence s ambient f rest after typed
    obtain ⟨next,result,fresh,extended,simulation⟩ := alternatives choice.memory (allowed front delta address object values mapped found) (matched front delta address object values mapped found)
    change ChosenResultSafe choices occurrence _ (memoryGrow _ _ f rest after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩
  | tableGrow index =>
    obtain ⟨front,reference,delta,address,object,values,mapped,found,alternatives⟩ := tableGrow_chosen_choices admissible occurrence s ambient f rest index after typed
    obtain ⟨next,result,fresh,extended,simulation⟩ := alternatives choice.table (allowed front reference delta address object values mapped found) (matched front reference delta address object values mapped found)
    change ChosenResultSafe choices occurrence _ (tableGrow _ _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩

theorem transition_chosen_safe {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr) (result : AResult)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : ChosenTransition choices occurrence ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op result) :
    ChosenResultSafe choices occurrence ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ result := by
  obtain ⟨choice,allowed,matched,rfl⟩ := step
  exact evaluate_chosen_safe admissible vector occurrence choice op s ambient f rest after typed allowed matched

end Exec.Abs.Stateful
