import Exec.Theorems.Host.Open.Completeness.ChosenQuietWorld
import Exec.Theorems.Composition.World.ChosenWorldResourceBounds
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Source call capacities, allocator availability and the inert dispatch
hooks rule out every nontrap Wasm failure before open host suspension. -/
theorem chosen_completed_only_trap {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vectorChoice : choices.vector=Spec.firstVectorChoice)
    (occurrence : Nat) {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    {expected : List valtype} (world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view expected)
    (held : ExecutableInv view world.code world.machine.store) (active : 0<world.machine.exec.frames.length)
    (typed : Config_ok (Abs.decode world.machine.source) (.mk_list expected))
    (resources : SourceWorldResources world.machine.store.limits.max_values.val world.machine.store.limits.max_frames.val world.machine.source)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (out : Answer M Unit) (error : runtime.ExecError)
    (prepared : prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform=.ok (.done out))
    (failed : out.1=.Err error) : ∃trap,error=.Trap trap := by
  have post:=chosen_quiet_world admissible numericChoice vectorChoice occurrence memory floats allocator correct allocation view laws compatible
    world held active typed out prepared
  simp only [ChosenQuietWorldResult,failed] at post
  obtain ⟨afterCode,effect,path,cause⟩:=post
  have excluded (kind : error=.Terminated ∨ error=.Exhausted .CallStack ∨ error=.Exhausted .Values ∨
      error=.Exhausted .Allocation ∨ error=.Exhausted .Objects) : False :=
    (cause.source_resources held.capacities).excludes_boundary resources (by omega) (by omega) available
      (by intro before after impossible
          simp only [inert,PureCallbacks.platform,Result.ok.injEq,Prod.mk.injEq] at impossible
          cases impossible.1)
      (by intro p identity args defaults nextPlatform after returned impossible
          simp only [inert,PureCallbacks.platform,PureCallbacks.Program.evaluate,Result.ok.injEq,Prod.mk.injEq] at impossible
          cases impossible.1) kind
  cases error with
  | Trap trap => exact ⟨trap,rfl⟩
  | Terminated => exact False.elim (excluded (Or.inl rfl))
  | Exhausted limit =>
    cases limit with
    | CallStack => exact False.elim (excluded (Or.inr (Or.inl rfl)))
    | Values => exact False.elim (excluded (Or.inr (Or.inr (Or.inl rfl))))
    | Allocation => exact False.elim (excluded (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | Objects => exact False.elim (excluded (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  | BadArguments | WrongStore | Internal | Link reason => cases path
end Exec.Theorems.OpenReentrantControl
