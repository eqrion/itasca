import Exec.Theorems.Host.Open.Native.NativeInvocationReturn
import Exec.Theorems.Host.Open.Native.NativeInvocationPartial
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

theorem invoke_erases {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (owner : address.store=store.id)
    (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature)
    (args : Slice runtime.Value) (issued : ∀value∈args.val,Store.IssuedValue store value)
    (results : alloc.vec.Vec runtime.Value) :
    (do let out←invoke memory floats allocator select exec store address args results
        .ok out.1)=runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator exec store () address args results := by
  have driverSafe:=invoke_safe memory floats allocator correct allocation view laws select code store held exec address owner function signature functionAt signatureAt args issued results
  have nativeSafe:=native_invoke_partial memory floats allocator correct allocation view laws select code store held exec address owner function signature functionAt signatureAt args issued results
  generalize driverEq : invoke memory floats allocator select exec store address args results=driver at driverSafe ⊢
  cases driverSafe with
  | ret post=>
    rename_i out
    rcases out with ⟨answer,history⟩
    simp only [bind_ok]
    exact (invoke_return_erases memory floats allocator correct allocation view laws select code store held exec address owner function signature functionAt signatureAt
      args issued results answer history driverEq).symm
  | div=>
    simp only [bind_div]
    generalize nativeEq : runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator exec store () address args results=native at nativeSafe ⊢
    cases nativeSafe with
    | div=>rfl
    | ret post=>
      rename_i answer
      obtain ⟨history,lifted⟩ := native_invoke_return_lifts memory floats allocator correct allocation view laws select code store held exec address owner function signature functionAt signatureAt
        args issued results answer nativeEq
      rw [driverEq] at lifted
      exact False.elim (div_not_ok lifted)

theorem invoke_diverges_iff_native {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (owner : address.store=store.id)
    (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature)
    (args : Slice runtime.Value) (issued : ∀value∈args.val,Store.IssuedValue store value)
    (results : alloc.vec.Vec runtime.Value) :
    invoke memory floats allocator select exec store address args results=.div ↔
      runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator exec store () address args results=.div := by
  have erased:=invoke_erases memory floats allocator correct allocation view laws select code store held exec address owner function signature functionAt signatureAt args issued results
  constructor
  · intro divergent
    rw [divergent,bind_div] at erased
    exact erased.symm
  · intro divergent
    have safe:=invoke_safe memory floats allocator correct allocation view laws select code store held exec address owner function signature functionAt signatureAt args issued results
    generalize actual : invoke memory floats allocator select exec store address args results=result at safe ⊢
    cases safe with
    | div=>rfl
    | ret post=>
      rename_i out
      rw [actual,bind_ok,divergent] at erased
      exact False.elim (ok_not_div erased)
end Exec.Theorems.OpenReentrantControl
