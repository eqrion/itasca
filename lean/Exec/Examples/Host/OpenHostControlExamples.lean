import Exec.Theorems.Host.Callbacks.HostControl

namespace Exec.Theorems.OpenHostControl
open Aeneas Aeneas.Std

/-- An implementation of the actual modeled callback interface can diverge
inside host control while retaining a pending call in its tick semantics. -/
theorem looping_platform_diverges {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (token : Unit) (store : runtime.store.Store M) (identity : U64) (args results : Slice runtime.Value) :
    (platform memory (fun _ _ => [.jump 0])).call_host token store identity args results = .div := by
  simp only [platform]
  rw [host_loop_diverges memory ⟨0,store,identity,args⟩ rfl]
  simp only [bind_div]

def mutatingLoop (index : Usize) (value : U32) : Code :=
  [.action (.writeI32 index value (.terminal (.returned (Slice.new _)))) 1,.jump 1]

def writtenStore {M : Type} (store : runtime.store.Store M) (index : Usize) (value : U32)
    (inside : index.val < store.globals.length) : runtime.store.Store M :=
  {store with globals := (store.globals.set index
    {store.globals.val[index.val] with lo := UScalar.cast .U64 value,hi := 0#u64})}

/-- This example commits the exact allowed global update in its first tick,
then diverges at the next program counter. The pending call remains in `next`. -/
theorem mutation_then_divergence {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (state : State M) (atStart : state.pc = 0) (index : Usize) (value : U32)
    (inside : index.val < state.store.globals.length)
    (mutable : (state.store.globals.val[index.val]).ty.mutability = .Var)
    (typed : (state.store.globals.val[index.val]).ty.valtype = .I32) :
    let next := {state with pc := 1,store := writtenStore state.store index value inside}
    tick memory (mutatingLoop index value) state = .ok (.cont next) ∧
      run memory (mutatingLoop index value) state = .div := by
  let next := {state with pc := 1,store := writtenStore state.store index value inside}
  have semantics : StoreCallbacks.Returns
      (.writeI32 index value (.terminal (.returned (Slice.new _)))) state.store (.Ok ())
      (writtenStore state.store index value inside) [] :=
    .write (.accepted inside mutable typed) (.terminal (.returned _) _)
  obtain ⟨values,actual,empty⟩ := semantics.actual memory
  have valuesEq : values = Slice.new _ := Slice.ext _ _ empty
  rw [valuesEq] at actual
  have first : tick memory (mutatingLoop index value) state = .ok (.cont next) := by
    simp [tick,mutatingLoop,atStart,actual,next]
  have forever : run memory (mutatingLoop index value) next = .div := by
    apply Interp.loop_diverges_of_stream (tick memory (mutatingLoop index value)) (fun _ => next)
    intro n
    simp [tick,mutatingLoop,next]
  refine ⟨first,?_⟩
  unfold run
  rw [loop.eq_def,first,bind_ok]
  exact forever

/-- Effects committed before divergence remain semantically source-typed. -/
theorem mutation_before_divergence_typed {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (state : State M)
    (held : ExecutableInv view code state.store) (index : Usize) (value : U32)
    (inside : index.val < state.store.globals.length)
    (mutable : (state.store.globals.val[index.val]).ty.mutability = .Var)
    (typed : (state.store.globals.val[index.val]).ty.valtype = .I32) :
    Store_ok (Store.decodeStore view code (writtenStore state.store index value inside)) := by
  have semantics : StoreCallbacks.Returns
      (.writeI32 index value (.terminal (.returned (Slice.new _)))) state.store (.Ok ())
      (writtenStore state.store index value inside) [] :=
    .write (.accepted inside mutable typed) (.terminal (.returned _) _)
  obtain ⟨values,actual,_⟩ := semantics.actual memory
  have safe := (StoreCallbacks.Program.writeI32 index value (.terminal (.returned (Slice.new _)))).correct
    memory view code state.store held
  rw [actual,WP.spec_ok] at safe
  exact safe.1.source_typed

end Exec.Theorems.OpenHostControl
