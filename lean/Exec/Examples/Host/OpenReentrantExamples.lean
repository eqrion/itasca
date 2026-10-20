import Exec.Theorems.Host.Open.Driver.ReentrantControl
import Exec.Examples.Host.OpenHostControlExamples
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std

def mutatingLoop (index : Usize) (value : U32) : Code :=
  [.action (.allocation (.base (.writeI32 index value (.terminal (.returned (Slice.new _)))))) 1,.jump 1]

/-- The first actual tick commits a checked global write. Every later tick
loops in host control, keeping the same pending call and committed store. -/
theorem mutation_then_divergence {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (identity : U64) (args : Slice runtime.Value)
    (index : Usize) (value : U32) (inside : index.val<store.globals.length)
    (mutable : (store.globals.val[index.val]).ty.mutability=.Var)
    (typed : (store.globals.val[index.val]).ty.valtype=.I32) :
    let select : Selector := fun _ _=>mutatingLoop index value
    let initial := initialHost select store identity args
    let next : State M := {initial with store:=OpenHostControl.writtenStore store index value inside,
                                          mode:=.host ⟨1,mutatingLoop index value,identity,args⟩}
    tick memory floats allocator select initial=.ok (.cont next) ∧
      run memory floats allocator select next=.div ∧ run memory floats allocator select initial=.div := by
  let select : Selector := fun _ _=>mutatingLoop index value
  let initial := initialHost select store identity args
  let next : State M := {initial with store:=OpenHostControl.writtenStore store index value inside,
                                        mode:=.host ⟨1,mutatingLoop index value,identity,args⟩}
  have source : StoreCallbacks.Returns (.writeI32 index value (.terminal (.returned (Slice.new _)))) store (.Ok ())
      (OpenHostControl.writtenStore store index value inside) [] :=
    .write (.accepted inside mutable typed) (.terminal (.returned _) _)
  obtain ⟨values,actual,empty⟩ := source.actual memory
  have valuesEq : values=Slice.new _ := Slice.ext _ _ empty
  rw [valuesEq] at actual
  have first : tick memory floats allocator select initial=.ok (.cont next) := by
    simp [tick,initialHost,mutatingLoop,CallbackActions.Program.run,AllocationCallbacks.Program.run,actual,initial,select,next]
  have forever : run memory floats allocator select next=.div := by
    apply Interp.loop_diverges_of_stream (tick memory floats allocator select) (fun _=>next)
    intro n
    simp [tick,next,initial,initialHost,select,mutatingLoop]
  refine ⟨first,forever,?_⟩
  unfold run
  rw [loop.eq_def,first,bind_ok]
  exact forever

/-- Source typing of the committed prefix comes from the checked write API,
independently of whether the enclosing host interaction ever completes. -/
theorem mutation_prefix_typed {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (held : ExecutableInv view code store) (index : Usize) (value : U32)
    (inside : index.val<store.globals.length) (mutable : (store.globals.val[index.val]).ty.mutability=.Var)
    (typed : (store.globals.val[index.val]).ty.valtype=.I32) :
    Store_ok (Store.decodeStore view code (OpenHostControl.writtenStore store index value inside)) :=
  OpenHostControl.mutation_before_divergence_typed memory view code ⟨0,store,0#u64,Slice.new _⟩ held index value inside mutable typed
end Exec.Theorems.OpenReentrantControl
