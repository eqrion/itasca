import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Equations.Interp
import Itasca.Generated.Funs
import Itasca.Results.Definitions.Host
import Itasca.Runtime.Platform.Observation
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Runtime.SourceMachine.Simulation
import Itasca.Runtime.Interp.Definitions

/-!
Proofs for Runtime / Interp.

This module collects Recording, Simulation.
Each section documents its contracts and consumers.
-/

/-! ## Recording -/

section

/-!
Proofs for Runtime / Interp.

This module collects ValueSlots, Recording, Observation.
Each section documents its contracts and consumers.
-/

/-! ## ValueSlots -/

section

open Itasca.Representation

/-! Slot encoding and decoding for the extracted interpreter. -/

namespace Itasca.Interp
open Aeneas Aeneas.Std

/-- Exact list update performed by the extracted slot writer. -/
def written (words : List U64) (position : Nat) (ty : Itasca.wasm_types.ValueType)
    (lo hi : U64) : List U64 :=
  if Itasca.Translation.valueType ty = .V128 then (words.set position lo).set (position + 1) hi
  else words.set position lo

@[step] theorem encode_slot_spec (slots : Slice U64) (position : Usize)
    (ty : Itasca.wasm_types.ValueType) (value : runtime.Value) (lo hi : U64)
    (he : runtime.value.encode value = .ok (lo, hi))
    (hb : position.val + Representation.width (Itasca.Translation.valueType ty) ≤ slots.length) :
    runtime.interp.encode_slot slots position ty value ⦃ result =>
      result.val = written slots.val position.val ty lo hi ⦄ := by
  have hp : position.val < slots.length := by
    have := Representation.width_positive (Itasca.Translation.valueType ty)
    omega
  unfold runtime.interp.encode_slot
  rw [he]
  step as ⟨old, back, hold, hback⟩
  subst back
  cases ty <;> simp only [Representation.compiler_width_eq, Representation.initializerWidth, Itasca.Translation.valueType, Representation.width] at hb ⊢
  all_goals try simp [written, Itasca.Translation.valueType]
  step as ⟨next, hnext⟩
  step as ⟨after, hafter⟩
  subst after
  simp [hnext]

theorem index_eq (slots : Slice U64) (position : Usize) (word : U64)
    (hb : position.val < slots.length) (hv : slots.val[position.val]! = word) :
    Slice.index_usize slots position = .ok word := by
  obtain ⟨actual, hr, ha⟩ := WP.spec_imp_exists (Slice.index_usize_spec slots position hb)
  have he : actual = word := by simpa [ha, _root_.getElem!_pos slots.val position.val hb] using hv
  rw [he] at hr
  exact hr

/-- The extracted reader observes exactly the one or two words at its slot
boundary, then uses the extracted value decoder on those words. -/
@[step] theorem decode_slot_spec (slots : Slice U64) (position : Usize)
    (ty : Itasca.wasm_types.ValueType) (store : Usize) (lo hi : U64) (value : runtime.Value)
    (hb : position.val + Representation.width (Itasca.Translation.valueType ty) ≤ slots.length)
    (hlo : slots.val[position.val]! = lo)
    (hhi : if Itasca.Translation.valueType ty = .V128 then slots.val[position.val + 1]! = hi else hi = 0#u64)
    (hd : runtime.value.decode ty lo hi store = .ok value) :
    runtime.interp.decode_slot slots position ty store ⦃ result => result = value ⦄ := by
  have hp : position.val < slots.length := by
    have := Representation.width_positive (Itasca.Translation.valueType ty)
    omega
  have hread := index_eq slots position lo hp hlo
  cases ty <;> simp only [Itasca.Translation.valueType, reduceCtorEq, ↓reduceIte] at hhi
  all_goals first
    | solve | subst hi; simp [runtime.interp.decode_slot, Representation.compiler_width_eq, Representation.initializerWidth, hread, hd]
    | skip
  unfold runtime.interp.decode_slot
  simp [Representation.compiler_width_eq, Representation.initializerWidth]
  step as ⟨next, hnext⟩
  have hn : next.val < slots.length := by
    simp only [Itasca.Translation.valueType, Representation.width] at hb
    omega
  have hnword : slots.val[next.val]! = hi := by simpa [hnext] using hhi
  have hreadHi := index_eq slots next hi hn hnword
  simp [hreadHi, hread, hd]

theorem written_length (words : List U64) (position : Nat) (ty : Itasca.wasm_types.ValueType)
    (lo hi : U64) : (written words position ty lo hi).length = words.length := by
  simp [written]; split <;> simp

theorem written_low (words : List U64) (position : Nat) (ty : Itasca.wasm_types.ValueType)
    (lo hi : U64) (hp : position < words.length) :
    (written words position ty lo hi)[position]! = lo := by
  unfold written
  split <;> simp [hp]

theorem written_high (words : List U64) (position : Nat) (ty : Itasca.wasm_types.ValueType)
    (lo hi : U64) (hv : Itasca.Translation.valueType ty = .V128) (hp : position + 1 < words.length) :
    (written words position ty lo hi)[position + 1]! = hi := by
  simp [written, hv, hp]

end Itasca.Interp

end

/-! ## Recording -/

section

/-! Internal event selection and writer instrumentation. These definitions
organize the source simulation proof; the public contract is stated using the
actual extracted invocation and observations made at the callback boundary.
The observation correspondence proves that both histories match. -/

/-! ## Interp / HostEvents -/

section InterpHostEvents

open Itasca.Representation

/-!
### Direct host-call events

A known host call records its actual scratch arguments and checked results or trap.
Rejection before the callback contributes no event.
-/

namespace Itasca.Interp

open Aeneas Aeneas.Std SpecExt

/-- A known host call logs the actual scratch arguments and checked result.
A rejection before the callback contributes no event. -/
def hostCallEvents {M P : Type} (address : runtime.FuncAddr)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : List HostEvent :=
  match out.1 with
  | .Ok _ => [.call address.index.val (out.2.1.host_args.val.map sourceValue)
      (some (out.2.1.host_results.val.map sourceValue))]
  | .Err (.Trap .Host) | .Err (.Exhausted .CallStack) =>
      [.call address.index.val (out.2.1.host_args.val.map sourceValue) none]
  | _ => []

end Itasca.Interp

end InterpHostEvents

/-! ## Interp / CallRecording -/

section InterpCallRecording

/-!
### Recorded call computation

`recordedCall` retains the actual concrete call result together with the direct host
events described by `callHostEvents`.
-/

namespace Itasca.Interp

open Aeneas Aeneas.Std SpecExt

/-- Initial-call recording selects a host site from the actual pre-call store.
A Wasm call contributes no event; its subsequent dispatches have their own sites. -/
def callHostEvents {M P : Type} (store : runtime.store.Store M) (address : runtime.FuncAddr)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : List HostEvent :=
  match store.funcs.val[address.index.val]? with
  | some function => match function.code with
    | .Host _ => hostCallEvents address out
    | .Wasm .. => []
  | none => []

def recordedCall {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (base : Usize) (prior : List HostEvent) :=
  Platform.Recording.run (runtime.interp.call memory hooks floats allocator exec store platform address base)
    (callHostEvents store address) prior

end Itasca.Interp

end InterpCallRecording

/-! ## Interp / StepSimulation -/

section InterpStepSimulation

/-!
### Host-event extraction

Host-address and event extraction identify the actual call made by an interpreter
step. The proof that the step simulates source execution is internal.
-/

namespace Itasca.Interp

open Aeneas Aeneas.Std SpecExt

/-- The host target selected by the actual call bytecode. Failed lookups,
null references, and indirect signature mismatches select no host site. -/
def hostInstructionAddress {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) : Option runtime.FuncAddr := do
  let address ← match instruction with
    | .Call index _ => inst.funcs.val[index.val]?
    | .CallIndirect entry selector _ => do
      let (table,type) ← compiled.indirect.val[entry.val]?
      let tableAddress ← inst.tables.val[table.val]?
      let object ← store.tables.val[tableAddress.index.val]?
      let word ← exec.slots.val[raw.base.val+selector.val]?
      let reference ← object.elements.val[(UScalar.cast .U32 word).val]?
      if reference=0#u64 then none else do
        let index := UScalar.cast .Usize reference
        if index.val=0 then none else do
          let address : Usize := UScalar.ofNatCore (index.val-1) (by have := index.hBounds; omega)
          let function ← store.funcs.val[address.val]?
          let signature ← inst.types.val[type.val]?
          if function.signature=signature then some ⟨store.id,address⟩ else none
    | _ => none
  let function ← store.funcs.val[address.index.val]?
  match function.code with
  | .Host _ => some address
  | .Wasm .. => none

/-- Host-call selection uses only the pre-dispatch concrete frame, bytecode,
slots, tables and function metadata. It does not inspect a source trace. -/
def hostStepAddress {M : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) : Option runtime.FuncAddr := do
  let raw ← exec.frames.val[exec.frames.length-1]?
  let inst ← store.instances.val[raw.instance.val]?
  let compiled ← inst.module.functions.val[raw.function.val]?
  let instruction ← compiled.code.val[raw.pc.val]?
  hostInstructionAddress exec store raw inst compiled instruction

def stepHostEvents {M P : Type} (exec : runtime.interp.Execution)
    (store : runtime.store.Store M)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : List HostEvent :=
  match hostStepAddress exec store with
  | some address => hostCallEvents address out
  | none => []

end Itasca.Interp

end InterpStepSimulation

/-! ## Interp / InvocationRecording -/

section InterpInvocationRecording

open Itasca.Representation

/-!
### Recorded invocation computation

Loop states/results and transparent recorder functions retain the actual direct
host-event log through invocation and final readback.
-/

namespace Itasca.Interp

open Aeneas Aeneas.Std SpecExt

abbrev InvokeLoopState (M P : Type) := runtime.interp.Execution × runtime.store.Store M × P × core.result.Result Unit runtime.ExecError

abbrev InvokeLoopResult (M P : Type) := Usize × alloc.vec.Vec U64 × alloc.vec.Vec runtime.interp.Frame ×
  alloc.vec.Vec runtime.Value × alloc.vec.Vec runtime.Value × runtime.store.Store M × P × core.result.Result Unit runtime.ExecError

/-- Only continuing body results perform a dispatch. The stopping guard and
its status check contribute no host event. -/
def invokeLoopEvents {M P : Type} (before : InvokeLoopState M P)
    (out : ControlFlow (InvokeLoopState M P) (InvokeLoopResult M P)) : List HostEvent :=
  match out with
  | .cont (exec,store,platform,status) => stepHostEvents before.1 before.2.1 (status,exec,store,platform)
  | .done _ => []

def recordedInvokeLoop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError) (prior : List HostEvent) :
    Result (InvokeLoopResult M P × List HostEvent) :=
  Platform.Recording.loop
    (fun (exec,store,platform,status) => runtime.interp.invoke_with_loop1.body memory hooks floats allocator exec store platform status)
    invokeLoopEvents (exec,store,platform,status) prior

abbrev InvocationResult (M P : Type) := core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
  runtime.store.Store M × P × alloc.vec.Vec runtime.Value

/-- Transparent writer instrumentation of the extracted public invocation.
Only the initial call and dispatch loop append events. All argument checks,
preparation errors and result readback follow the original control flow. -/
def recordedInvokeWith {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (func : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (prior : List HostEvent) : Result (InvocationResult M P × List HostEvent) := do
  let r ← runtime.store.Store.func_type memory store func
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val.params
    let r1 ←
      runtime.interp.check_values memory store args s
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s1 := alloc.vec.Vec.deref val.params
      let r2 ← runtime.interp.type_slots s1
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s2 := alloc.vec.Vec.deref val.results
        let r3 ← runtime.interp.type_slots s2
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let needed ← lift (core.cmp.impls.OrdUsize.max val1 val2)
          let (r4, exec1) ←
            runtime.interp.Execution.ensure allocator exec needed
              store.limits.max_values
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let v ← runtime.clear exec1.frames
            let v1 ←
              runtime.interp.invoke_with_loop0 exec1.slots args val.params 0#usize
                0#usize
            let ((r5, exec2, store1, platform1),callTrace) ←
              recordedCall memory hooks
                floats allocator
                { exec1 with store := store.id, slots := v1, frames := v } store platform func 0#usize prior
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let ((i, v5, v6, v7, v8, store2, platform2, status),loopTrace) ←
                recordedInvokeLoop memory
                  hooks floats allocator
                  exec2 store1 platform1 (core.result.Result.Ok ()) callTrace
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch status
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r6 ←
                  runtime.store.Store.func_type memory store2
                    func
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let i1 := alloc.vec.Vec.len val3.results
                  let i2 := alloc.vec.Vec.len results
                  let i3 ← lift (core.num.Usize.saturating_sub i1 i2)
                  let (r7, results1) ←
                    runtime.reserve allocator results i3
                  let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r7
                  match cf8 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let results2 ← runtime.clear results1
                    let (store3, results3) ←
                      runtime.interp.invoke_with_loop2 v5 store2 results2
                        0#usize 0#usize val3.results
                    Result.ok ((core.result.Result.Ok (),
                      {
                        store := i,
                        slots := v5,
                        frames := v6,
                        host_args := v7,
                        host_results := v8
                      }, store3, platform2, results3),loopTrace)
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    let r8 ←
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        Unit (core.convert.FromSame
                        _root_.Itasca.runtime.ExecError) residual
                    Result.ok ((r8,
                      {
                        store := i,
                        slots := v5,
                        frames := v6,
                        host_args := v7,
                        host_results := v8
                      }, store2, platform2, results1),loopTrace)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  let r7 ←
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      Unit (core.convert.FromSame
                      _root_.Itasca.runtime.ExecError) residual
                  Result.ok ((r7,
                    {
                      store := i,
                      slots := v5,
                      frames := v6,
                      host_args := v7,
                      host_results := v8
                    }, store2, platform2, results),loopTrace)
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r6 ←
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    Unit (core.convert.FromSame _root_.Itasca.runtime.ExecError)
                    residual
                Result.ok ((r6,
                  {
                    store := i,
                    slots := v5,
                    frames := v6,
                    host_args := v7,
                    host_results := v8
                  }, store2, platform2, results),loopTrace)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r6 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame _root_.Itasca.runtime.ExecError)
                  residual
              Result.ok ((r6, exec2, store1, platform1, results),callTrace)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r5 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame _root_.Itasca.runtime.ExecError)
                residual
            Result.ok ((r5, exec1, store, platform, results),prior)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.runtime.ExecError)
              residual
          Result.ok ((r4, exec, store, platform, results),prior)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.runtime.ExecError) residual
        Result.ok ((r3, exec, store, platform, results),prior)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.runtime.ExecError) residual
      Result.ok ((r2, exec, store, platform, results),prior)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.runtime.ExecError) residual
    Result.ok ((r1, exec, store, platform, results),prior)

end Itasca.Interp

end InterpInvocationRecording

end

/-! ## Observation -/

section

/-! # Observation contracts used to compose interpreter proofs

These are internal proof interfaces. Each contract concerns the actual
extracted operation under the callback observer. The interpreter proofs supply
them; they are never additional premises of a public execution theorem.
-/
namespace Itasca.Platform
open Aeneas Aeneas.Std SpecExt

/-- The new observations account for exactly this segment of source events.
Keeping the old prefix explicit lets loop proofs concatenate segments without
requiring an empty log at each recursive call. -/
def ObservationExtension {M : Type} (before after : List (HostObservation M))
    (events : List HostEvent) : Prop :=
  ∃ fresh, after = before ++ fresh ∧ List.Forall₂ HostObservation.Matches fresh events

theorem ObservationExtension.refl {M : Type} (before : List (HostObservation M)) :
    ObservationExtension before before [] :=
  ⟨[], by simp only [List.append_nil], .nil⟩

/-- Sequential operations preserve both callback order and source-event order. -/
theorem ObservationExtension.append {M : Type}
    {before middle after : List (HostObservation M)} {first second : List HostEvent}
    (left : ObservationExtension before middle first)
    (right : ObservationExtension middle after second) :
    ObservationExtension before after (first ++ second) := by
  obtain ⟨a,rfl,ha⟩ := left
  obtain ⟨b,rfl,hb⟩ := right
  refine ⟨a ++ b, List.append_assoc _ _ _, ?_⟩
  induction ha with
  | nil => exact hb
  | cons related _ ih => exact .cons related ih

theorem ObservationExtension.empty {M : Type} {before after : List (HostObservation M)}
    (observed : ObservationExtension before after []) : after = before := by
  obtain ⟨fresh,rfl,matched⟩ := observed
  cases matched
  exact List.append_nil _

end Itasca.Platform

namespace Itasca.Interp.Observation
open Aeneas Aeneas.Std Itasca.Platform

/-- The call proof owns callback preparation and reply validation. Instruction
proofs use this contract to transport the selected callee's observations. -/
def Call {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) : Prop :=
  ∀ exec store platform address base prior out,
    runtime.interp.call memory (observing hooks) floats allocator exec store (platform, prior) address base = .ok out →
    ObservationExtension prior out.2.2.2.2 (callHostEvents store address out)

/-- A step extends the callback log by exactly its recorded source events.
The loop proof can compose this fact without inspecting dispatch or call sites. -/
def Step {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) : Prop :=
  ∀ exec store platform prior out,
    runtime.interp.step memory (observing hooks) floats allocator exec store (platform, prior) = .ok out →
    ObservationExtension prior out.2.2.2.2 (stepHostEvents exec store out)

end Itasca.Interp.Observation

end

end

/-! ## Simulation -/

section

/-!
# Internal interpreter simulation vocabulary

These witnesses relate concrete frames, slots and program counters to source
execution. They are construction tools for the public source behavior and
resource theorems, not assumptions in those theorem statements.
-/

open Aeneas Aeneas.Std

/-! ## Interp / ControlLabels -/

section InterpControlLabels

/-!
### Source label matching

Label-match relations and the dispatch measure connect source control structure to
concrete structured execution.
-/

namespace Itasca.Interp

open Aeneas.Std

/-- Each compiler label records the actual saved operand prefix and source
continuation of its abstract-machine counterpart. -/
structure LabelMatch (values : List val) (label : SourceMachine.Label) (target : Compiler.LabelTarget) : Prop where
  front : target.front = (values.take label.height).map Representation.valueType
  height : target.front.length = label.height
  branchTypes : target.branchTypes = label.branchTypes
  resultTypes : target.resultTypes = label.resultTypes
  cont : target.cont = label.cont
  after : target.after = label.after

/-- Labels use the same innermost-first indexing on both sides. -/
structure LabelsMatch (values : List val) (labels : List SourceMachine.Label) (targets : List Compiler.LabelTarget) : Prop where
  length : labels.length = targets.length
  atIndex : ∀ (depth : Nat) (label : SourceMachine.Label), labels[depth]? = some label →
    ∃ target, targets[depth]? = some target ∧ LabelMatch values label target

end Itasca.Interp

namespace Itasca.Interp

open Aeneas Aeneas.Std

/-- Administrative potential covers source constants, forward skip jumps,
and the second half of a branch, including backward loop targets. The pending
phase weighs more than any possible remaining instruction distance. -/
def dispatchMeasure (pending : Bool) (codeLength pc : Nat) (state : SourceMachine.AState) : Nat :=
  SourceMachine.administrativeMeasure state * (2 * (codeLength + 1)) +
    (if pending then codeLength + 1 else 0) + (codeLength - pc)

end Itasca.Interp

end InterpControlLabels


/-! ## Interp / ExecutionState -/

section InterpExecutionState

/-!
### Concrete execution loop state

`ExecutionState`, `ExecutionResult` and `finishExecution` name the concrete states and
outcomes threaded through the interpreter loop.
-/

namespace Itasca.Interp

open Aeneas Aeneas.Std

abbrev ExecutionState (M P : Type) :=
  runtime.interp.Execution × runtime.store.Store M × P × core.result.Result Unit runtime.ExecError

abbrev ExecutionResult (M P : Type) :=
  Usize × alloc.vec.Vec U64 × alloc.vec.Vec runtime.interp.Frame × alloc.vec.Vec runtime.Value ×
    alloc.vec.Vec runtime.Value × runtime.store.Store M × P × core.result.Result Unit runtime.ExecError

def finishExecution {M P : Type} (state : ExecutionState M P) : ExecutionResult M P :=
  (state.1.store, state.1.slots, state.1.frames, state.1.host_args, state.1.host_results,
    state.2.1, state.2.2.1, state.2.2.2)

end Itasca.Interp

end InterpExecutionState


namespace Itasca.Interp
open Aeneas Aeneas.Std
open Itasca.Representation

/-- Code safety and exact retained store lookups for a concrete frame. -/
structure FrameProgram {M : Type} (store : runtime.store.Store M)
    (raw : runtime.interp.Frame) (compiled : runtime.bytecode.CompiledFunction)
    (locals results : List valtype) (functions : List functype) : Prop where
  lookup : ∃ inst, store.instances.val[raw.instance.val]? = some inst ∧
    inst.module.functions.val[raw.function.val]? = some compiled ∧
    FunctionTable store inst functions
  checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true
  fetchBound : compiled.code.val.length ≤ U32.max
  localSlots : compiled.local_slots.val = Representation.slots locals
  epilogue : ∃ pc count : U32, compiled.code.val.length = pc.val + 1 ∧
    compiled.code.val[pc.val]? = some (.Return compiled.local_slots count)


end Itasca.Interp


namespace Itasca.Interp
open Aeneas Aeneas.Std

/-- A dispatch either consumes administrative potential without emitting an
observable event, or performs positive source reductions with its exact events. -/
def EventfulConcreteSim (codeLength : Nat) (beforePC afterPC : Nat)
    (beforePending afterPending : Bool) (before after : SourceMachine.AState)
    (events : List SpecExt.HostEvent) : Prop :=
  (SourceMachine.decode before = SourceMachine.decode after ∧ events = [] ∧
    dispatchMeasure afterPending codeLength afterPC after <
      dispatchMeasure beforePending codeLength beforePC before) ∨
  ∃ n, 0 < n ∧ Spec.StepsHN n (SourceMachine.decode before) events (SourceMachine.decode after)

end Itasca.Interp


namespace Itasca.Interp.Machine

open Aeneas.Std

structure FramePoint (sourceStore : _root_.store) (raw : runtime.interp.Frame)
    (frame : SourceMachine.AFrame) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype) : Prop where
  bindings : SourceMachine.ModuleBindings sourceStore frame.module C
  locals : C.LOCALS = frame.locals.map Representation.valueType
  labels : LabelsMatch frame.vals frame.labels targets
  code : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS frame.resultTypes
    C.LOCALS compiled.code.val compiled.jump_tables.val targets (frame.vals.map Representation.valueType) frame.code raw.pc.val next output

/-- A mutable caller retains its module context and its typed continuation
while its child's results have not yet been written into the operand area. -/
structure SuspendedFramePoint (sourceStore : _root_.store) (raw : runtime.interp.Frame)
    (source : SourceMachine.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output waiting : List valtype) : Prop where
  bindings : SourceMachine.ModuleBindings sourceStore source.module C
  locals : C.LOCALS = source.locals.map Representation.valueType
  labels : LabelsMatch source.vals source.labels targets
  code : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS source.resultTypes C.LOCALS
    compiled.code.val compiled.jump_tables.val targets (source.vals.map Representation.valueType ++ waiting) source.code raw.pc.val next output

/-- The second dispatch of a compiled branch is represented explicitly; its
operand transfer has already occurred in the abstract machine. -/
inductive ControlPoint (sourceStore : _root_.store) (raw : runtime.interp.Frame)
    (source : SourceMachine.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype) : Bool → Prop where
  | ready (point : FramePoint sourceStore raw source compiled C targets next output) :
      ControlPoint sourceStore raw source compiled C targets next output false
  | jump (target : U32) (fetched : compiled.code.val[raw.pc.val]? = some (.Jump target))
      (continuation : FramePoint sourceStore {raw with pc := target} source compiled C targets next output) :
      ControlPoint sourceStore raw source compiled C targets next output true

end Itasca.Interp.Machine

/-! ## Interp / Slots -/

section InterpSlots

open Itasca.Representation

/-!
### Source values in concrete slots

Word/value regions, frame slots and frame bindings relate physical slot storage to
source values and frame layouts.
-/

namespace Itasca.Interp

open Aeneas Aeneas.Std

/-- A live contiguous region represents the given mathematical slot words.
Slots outside that region may contain dead operands or another frame. -/
def WordsAt (words : List U64) (base : Nat) (bits : List Nat) : Prop :=
  ∀ index, index < bits.length →
    base + index < words.length ∧ words[base + index]!.val = bits[index]!

def ValuesAt (words : List U64) (base : Nat) (values : List val) : Prop :=
  WordsAt words base (Representation.encodeValues values)

def FrameSlots (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (source : SourceMachine.AFrame) : Prop :=
  ValuesAt exec.slots.val raw.base.val (source.locals ++ source.vals)

/-- Resolve a concrete frame through the retained store, instance, function,
and signature tables, preserving actual owning-module bindings. -/
def FrameBinding {M : Type} (s : runtime.store.Store M) (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (source : SourceMachine.AFrame) : Prop :=
  ∃ inst fn compiled signature,
    exec.store = s.id ∧ raw ∈ exec.frames.val ∧
    s.instances.val[raw.instance.val]? = some inst ∧
    s.funcs.val[source.fa]? = some fn ∧
    fn.code = .Wasm raw.instance raw.function ∧
    inst.module.functions.val[raw.function.val]? = some compiled ∧
    s.types.val[fn.signature.val]? = some signature ∧
    source.module = Representation.decodeInstance s inst ∧
    source.resultTypes = signature.results.val.map Itasca.Translation.valueType ∧
    source.locals.map Representation.valueType = compiled.locals.val.map Itasca.Translation.valueType ∧
    raw.base.val + compiled.slot_count.val ≤ exec.slots.length

end Itasca.Interp

end InterpSlots


/-! ## Interp / Machine / FrameStack -/

section InterpMachineFrameStack

open Itasca.Representation

/-!
### Compiled frame-stack relation

Saved and active frame relations connect all concrete frames and slot regions to the
corresponding source frame stack.
-/

namespace Itasca.Interp.Machine

open Aeneas Aeneas.Std

/-- One suspended caller, waiting for the child result types at `childBase`. -/
structure SavedFrame {M : Type} (store : runtime.store.Store M) (sourceStore : _root_.store)
    (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (source : SourceMachine.AFrame) (waiting : List valtype) (childBase : Nat) : Prop where
  /-- The concrete frame resolves to this source activation and its bindings. -/
  binding : FrameBinding store exec raw source
  /-- Concrete slot regions represent this source frame's locals and operands. -/
  slots : FrameSlots exec raw source
  /-- The child starts immediately after this frame's live source values. -/
  destination : childBase = raw.base.val + Representation.slots ((source.locals ++ source.vals).map Representation.valueType)
  /-- Retained compiled code identifies the suspended source continuation. -/
  continuation : ∃ compiled C targets next output,
    FrameProgram store raw compiled (source.locals.map Representation.valueType) source.resultTypes C.FUNCS ∧
    SuspendedFramePoint sourceStore raw source compiled C targets next output waiting

/-- Suspended concrete/source callers paired from the innermost caller outward. -/
inductive SavedFrames {M : Type} (store : runtime.store.Store M) (sourceStore : _root_.store)
    (exec : runtime.interp.Execution) :
    List runtime.interp.Frame → List SourceMachine.AFrame → List valtype → Nat → Prop where
  | nil (waiting) : SavedFrames store sourceStore exec [] [] waiting 0
  | cons {raw raws source sources waiting base} :
      SavedFrame store sourceStore exec raw source waiting base →
      SavedFrames store sourceStore exec raws sources source.resultTypes raw.base.val →
      SavedFrames store sourceStore exec (raw :: raws) (source :: sources) waiting base

/-- The currently executing concrete/source function activation. -/
structure ActiveFrame {M : Type} (store : runtime.store.Store M) (sourceStore : _root_.store)
    (exec : runtime.interp.Execution) (raw : runtime.interp.Frame) (source : SourceMachine.AFrame) : Prop where
  /-- The concrete frame resolves to this source activation and its bindings. -/
  binding : FrameBinding store exec raw source
  /-- Concrete slot regions represent this source frame's locals and operands. -/
  slots : FrameSlots exec raw source
  /-- Its current compiled point denotes the pending source continuation. -/
  continuation : ∃ compiled C targets next output pending,
    FrameProgram store raw compiled (source.locals.map Representation.valueType) source.resultTypes C.FUNCS ∧
    ControlPoint sourceStore raw source compiled C targets next output pending

/-- The concrete frame vector ends in the active frame; source frames are
listed active first, followed by the paired suspended callers. -/
inductive FrameStackRel {M : Type} (store : runtime.store.Store M) (sourceStore : _root_.store)
    (exec : runtime.interp.Execution) : List SourceMachine.AFrame → Prop where
  | empty (frames : exec.frames.val = []) : FrameStackRel store sourceStore exec []
  | active {raw source raws sources}
      (frames : exec.frames.val = raws.reverse ++ [raw])
      (top : ActiveFrame store sourceStore exec raw source)
      (saved : SavedFrames store sourceStore exec raws sources source.resultTypes raw.base.val) :
      FrameStackRel store sourceStore exec (source :: sources)

end Itasca.Interp.Machine

end InterpMachineFrameStack


/-! ## Interp / Machine / Execution -/

section InterpMachineExecution

/-!
### Complete machine relation

Store decoding, source typing/support, invocation results, compiled frame stacks and
cursor interpretation connect one concrete execution state to its flat source state.
-/

namespace Itasca.Interp.Machine

open Aeneas Aeneas.Std

def ControlTop {M : Type} (store : runtime.store.Store M) (sourceStore : _root_.store)
    (exec : runtime.interp.Execution) (source : SourceMachine.AFrame) (pc : Nat) (pending : Bool) : Prop :=
  ∃ raw compiled C targets next output,
    exec.frames.val.getLast? = some raw ∧ raw.pc.val = pc ∧
    FrameProgram store raw compiled (source.locals.map Representation.valueType) source.resultTypes C.FUNCS ∧
    ControlPoint sourceStore raw source compiled C targets next output pending

def ExecutionCursor {M : Type} (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (source : SourceMachine.AState) (pc : Nat) (pending : Bool) : Prop :=
  match source.frames with
  | [] => pc = 0 ∧ pending = false ∧ ValuesAt exec.slots.val 0 source.results
  | frame :: _ => ControlTop store source.store exec frame pc pending

/-- The mutable machine relates the current concrete store, complete source
state and all active/suspended compiled frames. Store identity is not confused
with equality of the changing object payloads. -/
structure Execution {M : Type} (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (source : SourceMachine.AState) (expected : List valtype) (pc : Nat) (pending : Bool) : Prop where
  /-- The source store is the decoding under the current code interpretation. -/
  storeEq : source.store = Representation.decodeStore view code store
  /-- The complete flat source configuration is well typed. -/
  typed : SourceMachine.CoreTyped source
  /-- Its frames and source instructions belong to the supported semantics. -/
  core : SourceMachine.SupportedState source
  /-- Source frame/result types match the external invocation's result types. -/
  result : SourceMachine.InvocationResult expected source
  /-- Active and suspended compiled frames represent the source frame stack. -/
  stack : FrameStackRel store source.store exec source.frames
  /-- The concrete program counter and pending flag identify the source point. -/
  cursor : ExecutionCursor store exec source pc pending

end Itasca.Interp.Machine

end InterpMachineExecution

end
