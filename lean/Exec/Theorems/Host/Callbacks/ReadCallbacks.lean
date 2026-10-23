import Exec.Theorems.Host.Callbacks.AllocationCallbacks
import Exec.Theorems.Host.Callbacks.HostControl
import Exec.Store.Invariant.SemanticRead
import Exec.Store.Api.ReadOwnership
import Exec.Store.Invariant.IssuedArguments

/-! Finite callbacks with checked global/table reads and sequencing after
writes or host definitions. Independent observations describe decoded values;
normal return, ownership, metadata and source typing follow from the actual
accessors and certified action implementations. -/

namespace Exec.Theorems.ReadCallbacks
open Aeneas Aeneas.Std

inductive Program where
  | base (program : AllocationCallbacks.Program)
  | global (index : Usize)
  | table (table : Usize) (index : U32)
  | sequence (segment : AllocationCallbacks.Program) (next : Program)
  | branch (condition : Bool) (yes no : Program)

abbrev Reply (M : Type) := StoreCallbacks.Reply M
abbrev Effect := @OpenHostControl.Effect

def singleton (value : runtime.Value) : Slice runtime.Value :=
  Slice.from [value] (by simp; scalar_tac)

def Program.run {M A : Type} (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A) :
    Program → runtime.store.Store M → Result (Reply M)
  | .base program,store => program.run memory allocator store
  | .branch condition yes no,store => if condition then yes.run memory allocator store else no.run memory allocator store
  | .sequence segment next,store => do
    let answer ← segment.run memory allocator store
    match answer.1 with
    | .Ok () => next.run memory allocator answer.2.1
    | .Err error => .ok (.Err error,answer.2.1,Slice.new _)
  | .global index,store =>
    if index.val < store.globals.length then do
      let answer ← runtime.store.Store.global memory store ⟨store.id,index⟩
      match answer with
      | .Ok value => .ok (.Ok (),store,singleton value)
      | .Err _ => .ok (.Err .Trap,store,Slice.new _)
    else .ok (.Err .Trap,store,Slice.new _)
  | .table tableIndex index,store =>
    if inside : tableIndex.val < store.tables.length then
      if index.val < (store.tables.val[tableIndex.val]'inside).elements.length then do
        let answer ← runtime.store.Store.table_get memory store ⟨store.id,tableIndex⟩ index
        match answer with
        | .Ok value => .ok (.Ok (),store,singleton value)
        | .Err _ => .ok (.Err .Trap,store,Slice.new _)
      else .ok (.Err .Trap,store,Slice.new _)
    else .ok (.Err .Trap,store,Slice.new _)

inductive Returns {M : Type} : Program → runtime.store.Store M →
    core.result.Result Unit runtime.platform.HostError → runtime.store.Store M → List runtime.Value → Prop
  | base {program before status after values}
      (source : AllocationCallbacks.Returns program before status after values) :
      Returns (.base program) before status after values
  | global {store index value} (inside : index.val < store.globals.length)
      (observed : Interp.sourceValue value = (Store.decodeGlobal (store.globals.val[index.val])).VALUE) :
      Returns (.global index) store (.Ok ()) store [value]
  | global_invalid {store index} (outside : ¬ index.val < store.globals.length) :
      Returns (.global index) store (.Err .Trap) store []
  | table {store tableIndex index value} (inside : tableIndex.val < store.tables.length)
      (element : index.val < (store.tables.val[tableIndex.val]).elements.length)
      (observed : Interp.sourceValue value = Store.refVal
        (Store.decodeRef (store.tables.val[tableIndex.val]).ty
          ((store.tables.val[tableIndex.val]).elements.val[index.val]))) :
      Returns (.table tableIndex index) store (.Ok ()) store [value]
  | table_invalid {store tableIndex index} (outside : ¬ tableIndex.val < store.tables.length) :
      Returns (.table tableIndex index) store (.Err .Trap) store []
  | table_bounds {store tableIndex index} (inside : tableIndex.val < store.tables.length)
      (outside : ¬ index.val < (store.tables.val[tableIndex.val]).elements.length) :
      Returns (.table tableIndex index) store (.Err .Trap) store []
  | sequence {segment next before middle status after values ignored}
      (first : AllocationCallbacks.Returns segment before (.Ok ()) middle ignored)
      (tail : Returns next middle status after values) :
      Returns (.sequence segment next) before status after values
  | rejected {segment next before after error ignored}
      (first : AllocationCallbacks.Returns segment before (.Err error) after ignored) :
      Returns (.sequence segment next) before (.Err error) after []
  | yes {yes no before status after values} (source : Returns yes before status after values) :
      Returns (.branch true yes no) before status after values
  | no {yes no before status after values} (source : Returns no before status after values) :
      Returns (.branch false yes no) before status after values

theorem Program.correct_owned {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (program : Program) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) :
    program.run memory allocator store ⦃ answer =>
      Returns program store answer.1 answer.2.1 answer.2.2.val ∧
      Effect view code store answer.2.1 ∧
      ∀ value ∈ answer.2.2.val, Store.ValueInStore answer.2.1 value ⦄ := by
  induction program generalizing store with
  | base program =>
    apply WP.spec_mono (program.correct_owned memory allocator allocation view code store held)
    rintro answer ⟨source,valid,metadata,extension,externs,issued⟩
    exact ⟨.base source,⟨valid,metadata,extension,externs⟩,issued⟩
  | branch condition yes no hy hn =>
    cases condition with
    | false => exact WP.spec_mono (hn store held) (fun _ result => ⟨.no result.1,result.2⟩)
    | true => exact WP.spec_mono (hy store held) (fun _ result => ⟨.yes result.1,result.2⟩)
  | sequence segment next ih =>
    obtain ⟨⟨status,after,values⟩,actual,source,valid,metadata,extension,externs,issued⟩ := WP.spec_imp_exists
      (segment.correct_owned memory allocator allocation view code store held)
    have effect : Effect view code store after := ⟨valid,metadata,extension,externs⟩
    unfold Program.run
    rw [actual,bind_ok]
    cases status with
    | Ok result =>
      cases result
      exact WP.spec_mono (ih after valid) (fun _ post => ⟨.sequence source post.1,effect.trans post.2.1,post.2.2⟩)
    | Err error => exact WP.spec.ret ⟨.rejected source,effect,by simp⟩
  | global index =>
    unfold Program.run
    split
    · rename_i inside
      obtain ⟨answer,actual,value,same,_,observed⟩ := WP.spec_imp_exists
        (Store.global_read_boundary memory view store held.shape index inside)
      have owned := Store.global_read_owned memory view store held.shape index inside
      rw [actual,WP.spec_ok] at owned
      obtain ⟨other,otherSame,owned⟩ := owned
      rw [same] at otherSame
      cases otherSame
      rw [actual,same,bind_ok]
      exact WP.spec.ret ⟨.global inside observed,.refl held,by
        intro result member
        simp only [singleton,Slice.from_val,List.mem_singleton] at member
        subst result
        exact owned⟩
    · exact WP.spec.ret ⟨.global_invalid (by assumption),.refl held,by simp⟩
  | table tableIndex index =>
    unfold Program.run
    split
    · rename_i inside
      split
      · rename_i element
        obtain ⟨answer,actual,value,same,observed⟩ := WP.spec_imp_exists
          (Store.table_read_boundary memory view store held.shape tableIndex index inside element)
        have owned := Store.table_read_owned memory view store held.shape tableIndex index inside
        rw [actual,WP.spec_ok] at owned
        rcases owned with wrong | ⟨other,otherSame,owned⟩
        · rw [same] at wrong
          cases wrong
        · rw [same] at otherSame
          cases otherSame
          rw [actual,same,bind_ok]
          exact WP.spec.ret ⟨.table inside element observed,.refl held,by
            intro result member
            simp only [singleton,Slice.from_val,List.mem_singleton] at member
            subst result
            exact owned⟩
      · exact WP.spec.ret ⟨.table_bounds inside (by assumption),.refl held,by simp⟩
    · exact WP.spec.ret ⟨.table_invalid (by assumption),.refl held,by simp⟩

end Exec.Theorems.ReadCallbacks

