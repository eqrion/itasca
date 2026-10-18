import Exec.Abs.SimdSupported

namespace Exec.Abs

/-- Source syntax combining the scalar, stateful and SIMD families with
explicit select and branch tables, allowing arbitrary mixed nested bodies. -/
inductive ExecutableInstr : instr → Prop where
  | base {source} : SimdCumulativeInstr source → ExecutableInstr source
  | typedSelect (ty : valtype) : ExecutableInstr (.SELECT (some [ty]))
  | branchTable (labels : List labelidx) (fallback : labelidx) : ExecutableInstr (.BR_TABLE labels fallback)
  | block (ty : blocktype) (body : List instr) : Forall ExecutableInstr body → ExecutableInstr (.BLOCK ty body)
  | loop (ty : blocktype) (body : List instr) : Forall ExecutableInstr body → ExecutableInstr (.LOOP ty body)
  | ifelse (ty : blocktype) (yes no : List instr) :
      Forall ExecutableInstr yes → Forall ExecutableInstr no → ExecutableInstr (.IFELSE ty yes no)

theorem ExecutableInstr.block_body {ty body} (allowed : ExecutableInstr (.BLOCK ty body)) :
    Forall ExecutableInstr body := by
  cases allowed with
  | base old => exact fun i member => .base (old.block_body i member)
  | block _ _ body => exact body

theorem ExecutableInstr.loop_body {ty body} (allowed : ExecutableInstr (.LOOP ty body)) :
    Forall ExecutableInstr body := by
  cases allowed with
  | base old => exact fun i member => .base (old.loop_body i member)
  | loop _ _ body => exact body

theorem ExecutableInstr.if_bodies {ty yes no} (allowed : ExecutableInstr (.IFELSE ty yes no)) :
    Forall ExecutableInstr yes ∧ Forall ExecutableInstr no := by
  cases allowed with
  | base old => exact ⟨fun i member => .base (old.if_bodies.1 i member),fun i member => .base (old.if_bodies.2 i member)⟩
  | ifelse _ _ _ yes no => exact ⟨yes,no⟩

theorem executable_language : Supported.Language ExecutableInstr where
  cumulative old := .base (.cumulative old)
  block := .block
  loop := .loop
  block_body := ExecutableInstr.block_body
  loop_body := ExecutableInstr.loop_body
  if_bodies := ExecutableInstr.if_bodies
  head allowed := by
    cases allowed with
    | base old => exact simd_cumulative_language.head old
    | typedSelect ty => exact .external (by intros; rfl)
    | branchTable labels fallback => exact .external (by intros; rfl)
    | block ty body _ => exact .block ty body
    | loop ty body _ => exact .loop ty body
    | ifelse ty yes no _ _ => exact .ifelse ty yes no

abbrev ExecutableState := SupportedState ExecutableInstr

theorem SimdCumulativeState.executable {s : AState} (supported : SimdCumulativeState s) : ExecutableState s :=
  supported.map (fun _ old => .base old)

end Exec.Abs
