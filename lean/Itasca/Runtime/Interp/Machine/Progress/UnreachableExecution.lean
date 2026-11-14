import Itasca.Runtime.Interp.Machine.History.Append
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Machine.Progress.SupportedAdvance
import Itasca.Runtime.Interp.Machine.Control.BranchSource
import Itasca.Runtime.SourceMachine.Stateful.TableSet
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Interp.Machine.Emission.Unreachable
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatValueEncoding

/-!
Sections, each formerly its own module: ActiveLoop, UniformAdvance, UnreachableExecution.
-/

/-! ## ActiveLoop -/

section

/-!
Active-frame requirements for divergent execution loops and immediate errors.

Main declarations: `execution_loop_error` and `execution_loop_divergent_active`. A direct consumer is `Integration.Instantiation.InstantiateSourceOrigin`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem execution_loop_error {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (error : runtime.ExecError) :
    loop (executionBody memory hooks floats allocator) (exec, store, platform, .Err error) =
      .ok (finishExecution (exec, store, platform, .Err error)) := by
  rw [loop.eq_def]
  simp [executionBody, runtime.interp.invoke_with_loop1.body, core.result.Result.is_ok, finishExecution]

theorem execution_loop_divergent_active {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (divergent : loop (executionBody memory hooks floats allocator) (exec, store, platform, .Ok ()) = .div) :
    0 < exec.frames.length := by
  by_contra inactive
  have empty : ¬exec.frames.len > 0#usize := by scalar_tac
  rw [loop.eq_def] at divergent
  simp [executionBody, runtime.interp.invoke_with_loop1.body, empty] at divergent

end Itasca.Runtime.Interp

end

/-! ## UniformAdvance -/

section

/-!
The existing mutable advance, with the same endpoint and a uniform silent rank.

Main declarations: `UniformAdvance`. A direct consumer is `Interp.Machine.Progress.OrdinaryAdvance`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std

/-- The existing mutable advance, with the same endpoint and a uniform silent rank. -/
def UniformAdvance
 {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (expected : List valtype) (codeLength pc : Nat) (pending : Bool) (before : SourceMachine.AState) : Prop :=
  ∃ nextPC nextPending after,
    Execution view code store exec after expected nextPC nextPending ∧
    ConcreteSim codeLength pc nextPC pending nextPending before after ∧
    UniformConcreteSim pc nextPC pending nextPending before after [] ∧
    (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds before → SourceMachine.Ownership.StatefulOwned bounds after) ∧ after.ambient = before.ambient ∧
    (∀ bound, SourceMachine.CodeBound bound before → SourceMachine.CodeBound bound after)

variable  {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {codeLength pc : Nat} {pending : Bool} {before : SourceMachine.AState}

theorem UniformAdvance.forget
    (step : UniformAdvance view code store exec expected codeLength pc pending before) :
    Advance view code store exec expected codeLength pc pending before := by
  obtain ⟨nextPC,nextPending,after,machine,simulation,uniform,ownership,ambient,bounded⟩ := step
  exact ⟨nextPC,nextPending,after,machine,simulation,ownership,ambient,bounded⟩

theorem UniformAdvance.of_frame_forward {nextPC : Aeneas.Std.U32} {after : SourceMachine.AState}
    (machine : Execution view code store exec after expected nextPC.val false)
    (simulation : ConcreteSim codeLength pc nextPC.val false false before after)
    (forward : pc < nextPC.val)
    (ownership : ∀ bounds, SourceMachine.Ownership.StatefulOwned bounds before → SourceMachine.Ownership.StatefulOwned bounds after)
    (ambient : after.ambient = before.ambient)
    (bounded : ∀ bound, SourceMachine.CodeBound bound before → SourceMachine.CodeBound bound after) :
    UniformAdvance view code store exec expected codeLength pc false before :=
  ⟨nextPC.val,false,after,machine,simulation,
    simulation.uniform_forward forward (by scalar_tac),ownership,ambient,bounded⟩

end Itasca.Runtime.Interp.Machine

end

/-! ## UnreachableExecution -/

section

/-!
Unreachable execution with retained ownership.

Main declarations: `core_code_rel_unreachable_inv` and `step_unreachable_core_execution_owned`. A direct consumer is `Integration.Execution.Dispatch.Host`.
-/

namespace Itasca.Runtime.Interp.Machine.Unreachable
variable {jumpTables : List Aeneas.Std.U32}
variable {compiled : runtime.bytecode.CompiledFunction}
open Aeneas Aeneas.Std

theorem core_code_rel_unreachable_inv {C returns locals code labels stack pc next output after}
    (relation : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS returns locals code jumpTables labels stack (.UNREACHABLE :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS returns locals code jumpTables labels stack (.UNREACHABLE :: after) target.val next output) ∨
    code[pc]? = some .Unreachable := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (scalar_emission_not_unreachable (FloatHeads.project (.core (.pure .unreachable)) head))
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | unreachable instruction remaining scope => exact Or.inr instruction


/-- The explicit trap either follows a retained forward jump or produces the
positive source trap derivation. Every suspended caller survives a jump. -/
theorem step_unreachable_core_execution_owned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint (Store.decodeStore view code store) raw {f with code := .UNREACHABLE :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .UNREACHABLE::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS) :
    let initial : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .UNREACHABLE::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ pc : U32, out.2.1 = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        ((out.1 = .Ok () ∧ Execution view code store out.2.1 initial expected pc.val false ∧
          ConcreteSim compiled.code.length raw.pc.val pc.val false false initial initial ∧
          (∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds initial)) ∨
         (out.1 = .Err (.Trap .Unreachable) ∧ ∃ n, 0 < n ∧ Spec.StepsHN n (SourceMachine.decode initial) []
           ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  rcases core_code_rel_unreachable_inv point.code.current with skip | fetched
  · obtain ⟨target,forward,fetched,continuation⟩ := skip
    have pcBound : raw.pc.val < U32.max := by
      have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have cap := program.fetchBound
      omega
    apply WP.spec_mono (step_jump_exact memory hooks floats allocator exec store platform index raw inst compiled target last frameFound instanceFound codeFound pcBound fetched)
    intro out effect
    obtain ⟨success,exactState,sameStore,samePlatform⟩ := effect
    have targetPoint : FramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := .UNREACHABLE::after} compiled C targets next output :=
      ⟨point.bindings,point.locals,point.labels,continuation,point.code.targets,point.code.normal,point.code.exit,point.code.root⟩
    have represented : FrameSlots out.2.1 {raw with pc := target} {f with code := .UNREACHABLE::after} := by
      simpa only [exactState,FrameSlots] using slots
    have fresh := Execution.ordinary view code ambient {f with code := .UNREACHABLE::after} {f with code := .UNREACHABLE::after}
      rest expected raw.pc.val false machine (.refl store) (Itasca.Runtime.Spec.extend_store_refl _ machine.typed.typed.store)
      raw index target last frameFound program (.ready targetPoint) represented ⟨rfl,rfl,rfl,rfl⟩
      (by rw [exactState]) (by rw [exactState]; exact SlotPrefix.refl _ _) machine.typed machine.core
    exact ⟨sameStore,samePlatform,target,exactState,Or.inl ⟨success,fresh,
      Or.inl ⟨rfl,dispatch_measure_forward _ _ _ _ forward continuation.entry_bound⟩,fun _ h => h⟩⟩
  · have pcBound : raw.pc.val < U32.max := by
      have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have cap := program.fetchBound
      omega
    apply WP.spec_mono (step_unreachable_refines memory hooks floats allocator exec store platform index raw inst compiled
      (Store.decodeStore view code store) ambient f rest after last frameFound instanceFound codeFound pcBound fetched machine.typed.typed)
    intro out effect
    obtain ⟨trapped,sameStore,samePlatform,⟨pc,pcNext,exactState⟩,simulation⟩ := effect
    exact ⟨sameStore,samePlatform,pc,exactState,Or.inr ⟨trapped,simulation⟩⟩
end Itasca.Runtime.Interp.Machine.Unreachable

end
