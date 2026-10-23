import Exec.Abs.Stateful.Reference
import Exec.Abs.Stateful.TableRead
import Exec.Abs.Stateful.MemorySize
import Exec.Abs.Stateful.TableSet
import Exec.Abs.Stateful.Drops
import Exec.Abs.Stateful.TableFill
import Exec.Abs.Stateful.MemoryFill
import Exec.Abs.Stateful.MemoryCopy
import Exec.Abs.Stateful.TableCopy
import Exec.Abs.Stateful.MemoryInit
import Exec.Abs.Stateful.TableInit
import Exec.Abs.Stateful.MemoryGrow
import Exec.Abs.Stateful.TableGrow
import Exec.Abs.Stateful.Descriptor
namespace Exec.Abs.Stateful
open SpecExt Exec.Spec

/-- The only nondeterministic choices are successful growth or permitted refusal. -/
structure Selection where
  memory : Option meminst := none
  table : Option tableinst := none

/-- Growth choices refer to the actual operands and selected source object. -/
def Selection.Allowed (choice : Selection) (op : Instruction) (s : store) (f : AFrame) : Prop :=
  match op with
  | .memoryGrow => ∀ front delta address object,
      f.vals = front ++ [integerVal .I32 delta] → f.module.MEMS[0]? = some address →
      s.MEMS[address]? = some object → MemoryGrowthChoice object delta choice.memory
  | .tableGrow index => ∀ front reference delta address object,
      f.vals = front ++ [val_ref reference,integerVal .I32 delta] →
      f.module.TABLES[index]? = some address → s.TABLES[address]? = some object →
      TableGrowthChoice object delta reference choice.table
  | _ => True

theorem Selection.refusal_allowed (op : Instruction) (s : store) (f : AFrame) :
    Selection.Allowed {} op s f := by
  cases op <;> simp only [Selection.Allowed]
  all_goals first | trivial | intros; constructor

def evaluate (choice : Selection) (op : Instruction) (s : AState) (f : AFrame)
    (rest : List AFrame) (after : List instr) : AResult :=
  match op with
  | .refNull type => refNull s f rest type after
  | .refFunc index => refFunc s f rest index after
  | .refIsNull => refIsNull s f rest after
  | .tableGet index => tableGet s f rest index after
  | .tableSet index => tableSet s f rest index after
  | .tableSize index => tableSize s f rest index after
  | .tableGrow index => tableGrow choice.table s f rest index after
  | .tableFill index => tableFill s f rest index after
  | .tableCopy index source => tableCopy s f rest index source after
  | .tableInit index source => tableInit s f rest index source after
  | .elemDrop index => elementDrop s f rest index after
  | .memorySize => memorySize s f rest after
  | .memoryGrow => memoryGrow choice.memory s f rest after
  | .memoryFill => memoryFill s f rest after
  | .memoryCopy => memoryCopy s f rest after
  | .memoryInit index => memoryInit s f rest index after
  | .dataDrop index => dataDrop s f rest index after

/-- This relation selects a runtime result without choosing successful allocation in advance. -/
def Transition (s : AState) (f : AFrame) (rest : List AFrame) (after : List instr)
    (op : Instruction) (result : AResult) : Prop :=
  ∃ choice, choice.Allowed op s.store f ∧ evaluate choice op s f rest after = result

def ResultSafe (initial : AState) : AResult → Prop
  | .next next => CoreTyped next ∧ Extend_store initial.store next.store ∧ NextSim initial next
  | .trap => ∃ count, 0 < count ∧ StepsHN count (decode initial) [] ⟨⟨initial.store,initial.ambient⟩,[.TRAP]⟩
  | _ => False

def Instruction.readOnly : Instruction → Bool
  | .refNull _ | .refFunc _ | .refIsNull | .tableGet _ | .tableSize _ | .memorySize => true
  | _ => false

theorem evaluate_read_store (choice : Selection) (op : Instruction) (s : AState) (f : AFrame)
    (rest : List AFrame) (after : List instr) (next : AState) (readOnly : op.readOnly = true)
    (result : evaluate choice op s f rest after = .next next) : next.store = s.store := by
  cases op <;> simp only [Instruction.readOnly, Bool.false_eq_true] at readOnly
  all_goals simp only [evaluate,refNull,refFunc,refIsNull,tableGet,tableSize,memorySize,advance] at result
  all_goals repeat first | split at result | (cases result; rfl) | contradiction

theorem evaluate_safe (choice : Selection) (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (allowed : choice.Allowed op s f) :
    ResultSafe ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩
      (evaluate choice op ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after) := by
  cases op with
  | refNull type =>
    obtain ⟨next,result,fresh,simulation⟩ := refNull_progress s ambient f rest type after typed
    have same := evaluate_read_store choice (.refNull type) ⟨s,ambient,{f with code := (.refNull type : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ResultSafe _ (refNull _ f rest type after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | refFunc index =>
    obtain ⟨next,result,fresh,simulation⟩ := refFunc_progress s ambient f rest index after typed
    have same := evaluate_read_store choice (.refFunc index) ⟨s,ambient,{f with code := (.refFunc index : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ResultSafe _ (refFunc _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | refIsNull =>
    obtain ⟨next,result,fresh,simulation⟩ := refIsNull_progress s ambient f rest after typed
    have same := evaluate_read_store choice (.refIsNull) ⟨s,ambient,{f with code := (.refIsNull : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ResultSafe _ (refIsNull _ f rest after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | tableSize index =>
    obtain ⟨next,result,fresh,simulation⟩ := tableSize_progress s ambient f rest index after typed
    have same := evaluate_read_store choice (.tableSize index) ⟨s,ambient,{f with code := (.tableSize index : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ResultSafe _ (tableSize _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | memorySize =>
    obtain ⟨next,result,fresh,simulation⟩ := memorySize_progress s ambient f rest after typed
    have same := evaluate_read_store choice (.memorySize) ⟨s,ambient,{f with code := (.memorySize : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
    change ResultSafe _ (memorySize _ f rest after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
  | tableGet index =>
    rcases tableGet_progress s ambient f rest index after typed with ⟨next,result,fresh,simulation⟩ | ⟨result,trap⟩
    · have same := evaluate_read_store choice (.tableGet index) ⟨s,ambient,{f with code := (.tableGet index : Instruction).source::after}::rest,[]⟩ f rest after next rfl result
      change ResultSafe _ (tableGet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh, by rw [same]; exact extend_store_refl _ typed.typed.store, simulation⟩
    · change ResultSafe _ (tableGet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableSet index =>
    rcases tableSet_progress s ambient f rest index after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (tableSet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (tableSet _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableFill index =>
    rcases tableFill_progress s ambient f rest index after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (tableFill _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (tableFill _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableCopy index source =>
    rcases tableCopy_progress s ambient f rest index source after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (tableCopy _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (tableCopy _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | tableInit index source =>
    rcases tableInit_progress s ambient f rest index source after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (tableInit _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (tableInit _ f rest index source after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | memoryFill =>
    rcases memoryFill_progress s ambient f rest  after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (memoryFill _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (memoryFill _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | memoryCopy =>
    rcases memoryCopy_progress s ambient f rest  after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (memoryCopy _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (memoryCopy _ f rest  after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | memoryInit index =>
    rcases memoryInit_progress s ambient f rest index after typed with ⟨next,result,fresh,extended,simulation⟩ | ⟨result,trap⟩
    · change ResultSafe _ (memoryInit _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact ⟨fresh,extended,simulation⟩
    · change ResultSafe _ (memoryInit _ f rest index after)
      simp only [Instruction.source]
      rw [result]
      exact trap
  | elemDrop index =>
    obtain ⟨next,result,fresh,extended,simulation⟩ := elementDrop_progress s ambient f rest index after typed
    change ResultSafe _ (elementDrop _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩
  | dataDrop index =>
    obtain ⟨next,result,fresh,extended,simulation⟩ := dataDrop_progress s ambient f rest index after typed
    change ResultSafe _ (dataDrop _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩
  | memoryGrow =>
    obtain ⟨front,delta,address,object,values,mapped,found,choices⟩ := memoryGrow_choices s ambient f rest after typed
    obtain ⟨next,result,fresh,extended,simulation⟩ := choices choice.memory (allowed front delta address object values mapped found)
    change ResultSafe _ (memoryGrow _ _ f rest after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩
  | tableGrow index =>
    obtain ⟨front,reference,delta,address,object,values,mapped,found,choices⟩ := tableGrow_choices s ambient f rest index after typed
    obtain ⟨next,result,fresh,extended,simulation⟩ := choices choice.table (allowed front reference delta address object values mapped found)
    change ResultSafe _ (tableGrow _ _ f rest index after)
    simp only [Instruction.source]
    rw [result]
    exact ⟨fresh,extended,simulation⟩

theorem transition_safe (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr) (result : AResult)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op result) :
    ResultSafe ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ result := by
  obtain ⟨choice,allowed,rfl⟩ := step
  exact evaluate_safe choice op s ambient f rest after typed allowed

theorem transition_next (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr) (next : AState)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op (.next next)) :
    CoreTyped next ∧ Extend_store s next.store ∧
      NextSim ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ next :=
  transition_safe op s ambient f rest after (.next next) typed step

theorem transition_trap (op : Instruction) (s : store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (after : List instr)
    (typed : CoreTyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Transition ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ f rest after op .trap) :
    ∃ count,0<count ∧ StepsHN count (decode ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩) []
      ⟨⟨s,ambient⟩,[.TRAP]⟩ :=
  transition_safe op s ambient f rest after .trap typed step

end Exec.Abs.Stateful
