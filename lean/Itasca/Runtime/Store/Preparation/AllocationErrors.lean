import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Invariant.NormalResult
import Itasca.Runtime.Store.Api.Define
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Tactic.Rename
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Error classification only: an ordinary return from the object-count gate
cannot manufacture a link, trap, or argument failure. -/
theorem room_errors {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (out : core.result.Result Unit runtime.ExecError)
    (run : runtime.store.Store.room memory store = .ok out) : ErrorAllowed ResourceError out := by
  unfold runtime.store.Store.room at run
  repeat' first
    | (obtain ⟨value, called, rest⟩ := normal_bind_exists _ _ _ run; clear run; rename' rest => run)
    | split at run
    | (simp only [Result.ok.injEq] at run; subst out; trivial)

theorem reserve_errors {A T : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (values : alloc.vec.Vec T) (extra : Usize)
    (out : core.result.Result Unit runtime.ExecError × alloc.vec.Vec T)
    (run : runtime.reserve allocator values extra = .ok out) : ErrorAllowed ResourceError out.1 := by
  obtain ⟨answer, called⟩ := reserve_wrapper_eq allocator law values extra
  rw [called] at run
  simp only [Result.ok.injEq] at run
  rw [← run]
  cases answer <;> trivial

open Lean Meta Elab Tactic in
elab "allocation_error_effect " h:ident " using " allocator:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.reserve => `(tactic| have cause := reserve_errors $allocator $law _ _ _ $h)
    | ``runtime.store.Store.room => `(tactic| have cause := room_errors _ _ _ $h)
    | ``runtime.copy_type => do
      let theoremName :=    mkIdent `Itasca.Runtime.Store.copy_type_errors
      `(tactic| have cause := $theoremName $allocator $law _ _ $h)
    | ``runtime.store.Store.intern_type => do
      let theoremName :=    mkIdent `Itasca.Runtime.Store.intern_type_errors
      `(tactic| have cause := $theoremName _ $allocator $law _ _ _ $h)
    | ``runtime.store.copy_bytes => do
      let theoremName :=    mkIdent `Itasca.Runtime.Store.copy_bytes_errors
      `(tactic| have cause := $theoremName $allocator $law _ _ $h)
    | _ => throwError "not an allocation helper"
  evalTactic tac

macro "allocation_error_step " h:ident " using " allocator:term ", " law:term : tactic => `(tactic|
  first
  | solve | (simp only [Result.ok.injEq] at $h:ident; cases $h:ident; simp_all [ErrorAllowed, ResourceError])
  | solve | simp_all only [Result.ok.injEq, Prod.mk.injEq, ErrorAllowed, ResourceError,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.option.Option.ok_or, bind_ok, bind_tc_ok]
  | (fail_if_no_progress simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.option.Option.ok_or, bind_ok, bind_tc_ok, uncurry_apply_pair] at $h:ident)
  | split at $h:ident
  | (obtain ⟨value, called, rest⟩ := normal_bind_exists _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩
        repeat' (guard_hyp secondValue : Prod _ _; rcases secondValue with ⟨firstValue, secondValue⟩))
     | skip
     try allocation_error_effect called using $allocator, $law
     try simp only [uncurry_apply_pair] at $h:ident)
  | split at $h:ident)

theorem copy_type_errors {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (ty : Itasca.wasm_types.FuncType)
    (out : core.result.Result Itasca.wasm_types.FuncType runtime.ExecError)
    (run : runtime.copy_type allocator ty = .ok out) : ErrorAllowed ResourceError out := by
  unfold runtime.copy_type at run
  repeat' allocation_error_step run using allocator, law

theorem intern_type_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (ty : Itasca.wasm_types.FuncType)
    (out : core.result.Result Usize runtime.ExecError × runtime.store.Store M)
    (run : runtime.store.Store.intern_type memory allocator store ty = .ok out) : ErrorAllowed ResourceError out.1 := by
  unfold runtime.store.Store.intern_type at run
  repeat' allocation_error_step run using allocator, law

theorem copy_bytes_errors {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (bytes : Slice U8)
    (out : core.result.Result (alloc.vec.Vec U8) runtime.ExecError)
    (run : runtime.store.copy_bytes allocator bytes = .ok out) : ErrorAllowed ResourceError out := by
  unfold runtime.store.copy_bytes at run
  repeat' allocation_error_step run using allocator, law

theorem add_type_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_type memory allocator store inst index = .ok out) : ErrorAllowed ResourceError out.1 := by
  unfold runtime.store.instantiate.Store.add_instance_type at run
  repeat' allocation_error_step run using allocator, law

theorem add_function_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (instanceIndex index : Usize)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × runtime.store.ModuleInst)
    (run : runtime.store.instantiate.Store.add_instance_function memory allocator store inst instanceIndex index = .ok out) : ErrorAllowed ResourceError out.1 := by
  unfold runtime.store.instantiate.Store.add_instance_function at run
  repeat' allocation_error_step run using allocator, law

theorem add_data_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (instanceIndex index : Usize)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M)
    (run : runtime.store.instantiate.Store.add_instance_data memory allocator store instanceIndex index = .ok out) : ErrorAllowed ResourceError out.1 := by
  unfold runtime.store.instantiate.Store.add_instance_data at run
  repeat' allocation_error_step run using allocator, law
end Itasca.Runtime.Store
