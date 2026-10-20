import Exec.Theorems.Host.Callbacks.ReadCallbacks
import Exec.Theorems.Api.ExecutableInvGrowth
import Exec.Store.Api.GrowthEffects

/-! Finite checked callback programs with memory and null-filled table growth.
Independent effects retain refusal and committed buffer changes. Native memory
and allocation laws remain explicit; callback normality is proved. -/

namespace Exec.Theorems.GrowthCallbacks
open Aeneas Aeneas.Std

def nullValue : Itasca.types.ElemType → runtime.Value
  | .FuncRef => .FuncRef none
  | .ExternRef => .ExternRef none

private theorem null_owned {M : Type} (store : runtime.store.Store M) (type : Itasca.types.ElemType) :
    Store.ValueInStore store (nullValue type) := by cases type <;> exact ⟨trivial,trivial⟩

private theorem null_typed (type : Itasca.types.ElemType) :
    Store.elementValueType type = Interp.rawType (nullValue type) := by cases type <;> rfl

private theorem null_encoded (type : Itasca.types.ElemType) :
    runtime.value.encode (nullValue type) = .ok (0#u64,0#u64) := by cases type <;> rfl

private theorem memory_effect {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (index : Usize) (delta : U32)
    (inside : index.val < store.memories.length) :
    runtime.store.Store.grow_memory_with memory store ⟨store.id,index⟩ delta ⦃ answer =>
      ∃ pages, answer.1 = .Ok pages ∧ Store.MemoryGrowth view code store index delta (pages,answer.2) ⦄ := by
  unfold runtime.store.Store.grow_memory_with
  simp [runtime.store.Store.check,core.result.Result.Insts.CoreOpsTry.branch]
  step with Store.memory_grow_effect memory view laws code store index delta inside
    (fun m member => (held.shape.memories m member).length_bound)
    (fun m member => (held.shape.memories m member).1) as ⟨pages,after,effect⟩
  exact ⟨pages,rfl,effect⟩

private theorem table_effect {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (index : Usize) (delta : U32)
    (inside : index.val < store.tables.length) :
    runtime.store.Store.grow_table_with memory allocator store ⟨store.id,index⟩ delta
      (nullValue (store.tables.val[index.val]).ty) ⦃ answer =>
      ∃ size, answer.1 = .Ok size ∧ Store.TableGrowth store index delta 0#u64 (size,answer.2) ⦄ := by
  unfold runtime.store.Store.grow_table_with
  simp [runtime.store.Store.check,core.result.Result.Insts.CoreOpsTry.branch]
  rw [Store.check_value_owned memory store _ (null_owned store _).1]
  simp
  step with Interp.vec_index_given store.tables index store.tables.val[index.val]
    (List.getElem?_eq_getElem inside) as ⟨table,found⟩
  subst table
  simp [null_typed,core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default]
  rw [null_encoded,bind_ok]
  step with Store.table_grow_effect memory allocator allocation store index delta 0#u64 inside
    (fun table member => (held.shape.tables table member).1) as ⟨size,after,effect⟩
  exact ⟨size,rfl,effect⟩

inductive Program where
  | base (segment : ReadCallbacks.Program)
  | sequence (segment : ReadCallbacks.Program) (next : Program)
  | growMemory (index : Usize) (delta : U32) (next : Program)
  | growTableNull (index : Usize) (delta : U32) (next : Program)
  | branch (condition : Bool) (yes no : Program)

abbrev Reply (M : Type) := StoreCallbacks.Reply M
abbrev Effect := @OpenHostControl.Effect

/-- Growth refusal retains its specified sentinel behavior. A completed growth
operation continues; invalid issued-object indices become host traps. -/
def Program.run {M A : Type} (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A) :
    Program → runtime.store.Store M → Result (Reply M)
  | .base segment,store => segment.run memory allocator store
  | .branch condition yes no,store => if condition then yes.run memory allocator store else no.run memory allocator store
  | .sequence segment next,store => do
    let answer ← segment.run memory allocator store
    match answer.1 with
    | .Ok () => next.run memory allocator answer.2.1
    | .Err error => .ok (.Err error,answer.2.1,Slice.new _)
  | .growMemory index delta next,store =>
    if index.val < store.memories.length then do
      let answer ← runtime.store.Store.grow_memory_with memory store ⟨store.id,index⟩ delta
      match answer.1 with
      | .Ok _ => next.run memory allocator answer.2
      | .Err _ => .ok (.Err .Trap,answer.2,Slice.new _)
    else .ok (.Err .Trap,store,Slice.new _)
  | .growTableNull index delta next,store =>
    if inside : index.val < store.tables.length then do
      let answer ← runtime.store.Store.grow_table_with memory allocator store ⟨store.id,index⟩ delta
        (nullValue (store.tables.val[index.val]'inside).ty)
      match answer.1 with
      | .Ok _ => next.run memory allocator answer.2
      | .Err _ => .ok (.Err .Trap,answer.2,Slice.new _)
    else .ok (.Err .Trap,store,Slice.new _)

/-- Independent growth effects distinguish refusal, exact zero-filled/nullable
extension and committed representation changes without an implementation run. -/
inductive Returns {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation) : Program → runtime.store.Store M →
    core.result.Result Unit runtime.platform.HostError → runtime.store.Store M → List runtime.Value → Prop
  | base {segment before status after values} (source : ReadCallbacks.Returns segment before status after values) :
      Returns view code (.base segment) before status after values
  | sequence {segment next before middle status after values ignored}
      (first : ReadCallbacks.Returns segment before (.Ok ()) middle ignored)
      (tail : Returns view code next middle status after values) :
      Returns view code (.sequence segment next) before status after values
  | rejected {segment next before after error ignored}
      (first : ReadCallbacks.Returns segment before (.Err error) after ignored) :
      Returns view code (.sequence segment next) before (.Err error) after []
  | memory {index delta next before middle status after values pages}
      (inside : index.val < before.memories.length)
      (effect : Store.MemoryGrowth view code before index delta (pages,middle))
      (tail : Returns view code next middle status after values) :
      Returns view code (.growMemory index delta next) before status after values
  | memory_invalid {index delta next before} (outside : ¬ index.val < before.memories.length) :
      Returns view code (.growMemory index delta next) before (.Err .Trap) before []
  | table {index delta next before middle status after values size}
      (inside : index.val < before.tables.length)
      (effect : Store.TableGrowth before index delta 0#u64 (size,middle))
      (tail : Returns view code next middle status after values) :
      Returns view code (.growTableNull index delta next) before status after values
  | table_invalid {index delta next before} (outside : ¬ index.val < before.tables.length) :
      Returns view code (.growTableNull index delta next) before (.Err .Trap) before []
  | yes {yes no before status after values} (source : Returns view code yes before status after values) :
      Returns view code (.branch true yes no) before status after values
  | no {yes no before status after values} (source : Returns view code no before status after values) :
      Returns view code (.branch false yes no) before status after values

theorem Program.correct_owned {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (program : Program) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) :
    program.run memory allocator store ⦃ answer =>
      Returns view code program store answer.1 answer.2.1 answer.2.2.val ∧
      Effect view code store answer.2.1 ∧
      ∀ value ∈ answer.2.2.val, Store.ValueInStore answer.2.1 value ⦄ := by
  induction program generalizing store with
  | base segment =>
    exact WP.spec_mono (segment.correct_owned memory allocator allocation view code store held)
      (fun _ post => ⟨.base post.1,post.2⟩)
  | branch condition yes no hy hn =>
    cases condition with
    | false => exact WP.spec_mono (hn store held) (fun _ post => ⟨.no post.1,post.2⟩)
    | true => exact WP.spec_mono (hy store held) (fun _ post => ⟨.yes post.1,post.2⟩)
  | sequence segment next ih =>
    obtain ⟨⟨status,after,values⟩,actual,source,effect,issued⟩ := WP.spec_imp_exists
      (segment.correct_owned memory allocator allocation view code store held)
    unfold Program.run
    rw [actual,bind_ok]
    cases status with
    | Ok result =>
      cases result
      exact WP.spec_mono (ih after effect.invariant) (fun _ post => ⟨.sequence source post.1,effect.trans post.2.1,post.2.2⟩)
    | Err error => exact WP.spec.ret ⟨.rejected source,effect,by simp⟩
  | growMemory index delta next ih =>
    unfold Program.run
    split
    · rename_i inside
      obtain ⟨answer,actual,fresh,_,extension⟩ := WP.spec_imp_exists
        (ExecutableInv.memory_grow_certified memory view laws code store held index delta inside)
      have source := memory_effect memory view laws code store held index delta inside
      rw [actual,WP.spec_ok] at source
      obtain ⟨pages,status,growth⟩ := source
      have metadata := growth.metadata
      have effect : Effect view code store answer.2 := ⟨fresh,metadata.1.prefix,extension,metadata.2.1⟩
      rw [actual,bind_ok,status]
      exact WP.spec_mono (ih answer.2 fresh) (fun _ post => ⟨.memory inside growth post.1,effect.trans post.2.1,post.2.2⟩)
    · exact WP.spec.ret ⟨.memory_invalid (by assumption),.refl held,by simp⟩
  | growTableNull index delta next ih =>
    unfold Program.run
    split
    · rename_i inside
      obtain ⟨answer,actual,fresh,_,extension⟩ := WP.spec_imp_exists
        (ExecutableInv.table_grow_certified memory allocator allocation view code store held index delta
          (nullValue (store.tables.val[index.val]).ty) inside (null_typed _) (null_owned store _))
      have source := table_effect memory allocator allocation view code store held index delta inside
      rw [actual,WP.spec_ok] at source
      obtain ⟨size,status,growth⟩ := source
      have metadata := growth.metadata
      have effect : Effect view code store answer.2 := ⟨fresh,metadata.1.prefix,extension,metadata.2.1⟩
      rw [actual,bind_ok,status]
      exact WP.spec_mono (ih answer.2 fresh) (fun _ post => ⟨.table inside growth post.1,effect.trans post.2.1,post.2.2⟩)
    · exact WP.spec.ret ⟨.table_invalid (by assumption),.refl held,by simp⟩

/-- The issued-result contract follows from the stronger owned-result package. -/
theorem Program.correct {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (program : Program) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) :
    program.run memory allocator store ⦃ answer =>
      Returns view code program store answer.1 answer.2.1 answer.2.2.val ∧
      Effect view code store answer.2.1 ∧
      ∀ value ∈ answer.2.2.val, Store.IssuedValue answer.2.1 value ⦄ := by
  apply WP.spec_mono (program.correct_owned memory allocator allocation view laws code store held)
  rintro answer ⟨source,effect,owned⟩
  exact ⟨source,effect,fun value member=>(owned value member).issued⟩

def platform {M A : Type} (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (select : U64 → Slice runtime.Value → Program) : runtime.platform.Platform Unit M where
  MemoryBufferInst := memory
  interrupt token := .ok (.Continue,token)
  call_host token store identity args _ := do
    let answer ← (select identity args).run memory allocator store
    .ok (answer.1,token,answer.2.1,answer.2.2)

theorem sound {M A : Type} (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (select : U64 → Slice runtime.Value → Program)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation) :
    Platform.HostSound (platform memory allocator select) (ExecutableInv view code) (Store.decodeStore view code) := by
  apply Platform.HostSound.of_invariant (fun _ held => held.source_typed)
  intro token store identity args results held
  unfold platform
  step with (select identity args).correct memory allocator allocation view laws code store held
    as ⟨answer,_,effect,_⟩
  exact ⟨effect.invariant,effect.extension⟩

theorem world_sound {M A : Type} (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (select : U64 → Slice runtime.Value → Program)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) :
    HostWorldSound (platform memory allocator select) view (ExecutableInv view) :=
  HostWorldSound.of_fixed (sound memory allocator allocation select view laws)

theorem callback_package {M A : Type} (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (select : U64 → Slice runtime.Value → Program)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation) (token : Unit)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (identity : U64) (args results : Slice runtime.Value) :
    (platform memory allocator select).call_host token store identity args results ⦃ answer =>
      Returns view code (select identity args) store answer.1 answer.2.2.1 answer.2.2.2.val ∧
      Effect view code store answer.2.2.1 ∧
      Store_ok (Store.decodeStore view code answer.2.2.1) ∧
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value ⦄ := by
  unfold platform
  step with (select identity args).correct memory allocator allocation view laws code store held
    as ⟨answer,source,effect,issued⟩
  exact ⟨source,effect,effect.invariant.source_typed,issued⟩

end Exec.Theorems.GrowthCallbacks

