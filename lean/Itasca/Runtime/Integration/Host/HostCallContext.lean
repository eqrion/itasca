import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Host.HostReturnFrames
import Itasca.Runtime.Store.Invariant.HostSignature
import Itasca.Runtime.Spec.ModuleMembership
import Itasca.Generated.Types
import Itasca.Runtime.Spec.Integer
import Itasca.Runtime.SourceMachine.Sim.Host

/-!
Sections, each formerly its own module: HostCallSource, HostCallRecording, HostCallContext.
-/

/-! ## HostCallSource -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- Observable behavior after an actual host callback. Preparation rejections
are separated by the calling theorem because they perform no host event. -/
def HostCallSourceOutcome {M P : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before : runtime.store.Store M) (ambient : frame) (address : runtime.FuncAddr)
    (args : List val) (base : Usize) (exec : runtime.interp.Execution)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  out.2.1.host_args.val.map sourceValue = args ∧ out.2.1.frames = exec.frames ∧ out.2.1.store = exec.store ∧
  exec.slots.length ≤ out.2.1.slots.length ∧
  ((out.1 = .Ok () ∧
    ValuesAt out.2.1.slots.val base.val (out.2.1.host_results.val.map sourceValue) ∧
    StepH ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
      [.call address.index.val args (some (out.2.1.host_results.val.map sourceValue))]
      ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.1.host_results.val.map sourceValue)⟩ ∧
    (∀ j, j < exec.slots.length →
      j < base.val ∨ base.val + Compiler.slots (out.2.1.host_results.val.map (Compiler.valueType ∘ sourceValue)) ≤ j →
      out.2.1.slots.val[j]? = exec.slots.val[j]?)) ∨
   ((out.1 = .Err (.Trap .Host) ∨ out.1 = .Err (.Exhausted .CallStack)) ∧
    StepH ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
      [.call address.index.val args none]
      ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,[.TRAP]⟩ ∧
    (∀ j, j < exec.slots.length → out.2.1.slots.val[j]? = exec.slots.val[j]?)))

/-- Actual resource causes for a host call, including a callback's explicit
stack-overflow reply. The checked callback equation retains its returned store. -/
def HostCallCauses {A M P : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (signature : Itasca.wasm_types.FuncType)
    (base : Usize) (identity : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  match out.1 with
  | .Ok _ | .Err (.Trap _) => True
  | .Err (.Exhausted .CallStack) =>
      ∃ p args defaults returned, hooks.call_host p store identity args defaults =
        .ok (.Err .StackOverflow,out.2.2.2,out.2.2.1,returned)
  | .Err error => HostPreparationCause allocator hooks exec store platform signature base error

theorem HostCallCauses.of_preparation {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {signature : Itasca.wasm_types.FuncType}
    {base : Usize} {identity : U64}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    {error : runtime.ExecError} (status : out.1 = .Err error)
    (cause : HostPreparationCause allocator hooks exec store platform signature base error) :
    HostCallCauses allocator hooks exec store platform signature base identity out := by
  simp only [HostCallCauses,status]
  cases error <;> simp_all [HostPreparationCause]
  rename_i limit
  cases limit <;> simp_all [HostPreparationCause]

end Itasca.Runtime.Integration

end

/-! ## HostCallRecording -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- The observable source endpoint for an isolated host call. A preparation
rejection has not consumed the call redex. -/
def hostCallResultConfig {M P : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (ambient : frame) (address : runtime.FuncAddr) (args : List val)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : config :=
  ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,
    match out.1 with
    | .Ok _ => vals (out.2.1.host_results.val.map sourceValue)
    | .Err (.Trap .Host) | .Err (.Exhausted .CallStack) => [.TRAP]
    | _ => vals args ++ [.CALL_ADDR address.index.val]⟩

theorem HostCallSourceOutcome.events {M P : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before : runtime.store.Store M) (ambient : frame)
    (address : runtime.FuncAddr) (args : List val) (base : Usize)
    (exec : runtime.interp.Execution)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P)
    (observed : HostCallSourceOutcome view code before ambient address args base exec out) :
    StepsH ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
      (hostCallEvents address out) (hostCallResultConfig view code ambient address args out) := by
  obtain ⟨arguments,_,_,_,outcome⟩ := observed
  rcases outcome with ⟨success,_,source,_⟩ | ⟨error,source,_⟩
  · simpa only [hostCallEvents,hostCallResultConfig,success,arguments] using Spec.steps_h_single source
  · rcases error with trap | exhausted
    · simpa only [hostCallEvents,hostCallResultConfig,trap,arguments] using Spec.steps_h_single source
    · simpa only [hostCallEvents,hostCallResultConfig,exhausted,arguments] using Spec.steps_h_single source

end Itasca.Runtime.Integration

end

/-! ## HostCallContext -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- Source endpoint after a host call in an active Wasm frame. Traps unwind
all callers; successful calls resume the source continuation with actual results. -/
def hostCallFrameResult {M P : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (front : List val)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : config :=
  match out.1 with
  | .Ok _ => SourceMachine.decode ⟨Store.decodeStore view code out.2.2.1,ambient,
      {f with code := after,vals := front ++ out.2.1.host_results.val.map sourceValue} :: rest,[]⟩
  | _ => ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,[.TRAP]⟩

/-- The checked atomic host event composes with source call resolution and
all surrounding contexts. This retains a positive source step count. -/
theorem HostCallSourceOutcome.frame_events {M P : Type}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before : runtime.store.Store M) (ambient : frame) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr) (index : Nat)
    (address : runtime.FuncAddr) (front args : List val) (base : Usize)
    (exec : runtime.interp.Execution)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P)
    (observed : HostCallSourceOutcome view code before f.toFrame address args base exec out)
    (storeWf : wf_store (Store.decodeStore view code before))
    (freshWf : wf_store (Store.decodeStore view code out.2.2.1))
    (ambientWf : wf_frame ambient) (frameWf : wf_frame f.toFrame)
    (labels : SourceMachine.LabelsWf f.labels) (values : Forall wf_val front)
    (tail : Forall wf_instr after) (callers : Forall SourceMachine.FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (resolve : f.module.FUNCS[index]? = some address.index.val) (indexBound : index < 2^32)
    (argsWf : Forall wf_val args) :
    ∃ n, 2 ≤ n ∧ Spec.StepsHN n
      (SourceMachine.decode ⟨Store.decodeStore view code before,ambient,
        {f with code := .CALL (.mk_uN index) :: after,vals := front ++ args} :: rest,[]⟩)
      (hostCallEvents address out) (hostCallFrameResult view code ambient f rest after front out) := by
  obtain ⟨arguments,_,_,_,outcome⟩ := observed
  rcases outcome with ⟨success,_,source,_⟩ | ⟨failure,source,_⟩
  · refine ⟨2,by omega,?_⟩
    simpa only [hostCallEvents,hostCallFrameResult,success,arguments] using
      SourceMachine.host_return_simulation _ _ ambient f rest after index address.index.val front args
        (out.2.1.host_results.val.map sourceValue) _ storeWf ambientWf frameWf labels values tail callers
        heights resolve indexBound argsWf source
  · obtain ⟨n,bound,trace⟩ := SourceMachine.host_trap_simulation _ _ ambient f rest after index address.index.val
      front args _ storeWf freshWf ambientWf frameWf labels values tail callers heights resolve indexBound argsWf source
    refine ⟨n,bound,?_⟩
    rcases failure with trapped | exhausted
    · simpa only [hostCallEvents,hostCallFrameResult,trapped,arguments] using trace
    · simpa only [hostCallEvents,hostCallFrameResult,exhausted,arguments] using trace
end Itasca.Runtime.Integration

end
