import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.Interp.Machine.Emission.Unreachable
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatEmissionInversion
import Itasca.Runtime.SourceMachine.Stateful.OwnershipStore

/-!
Unreachable execution with retained ownership.

Main declarations: `coreCodeRel_unreachable_inv` and `step_unreachable_core_execution_owned`. A direct consumer is `Integration.Execution.Dispatch.Host`.
-/

namespace Itasca.Runtime.Interp.StructuredMachine.Unreachable
variable {jumpTables : List Aeneas.Std.U32}
variable {compiled : runtime.bytecode.CompiledFunction}
open Aeneas Aeneas.Std

theorem coreCodeRel_unreachable_inv {C returns locals code labels stack pc next output after}
    (relation : Code.StructuredCode (emission compiled C) C.TYPES C.FUNCS returns locals code jumpTables labels stack (.UNREACHABLE :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode (emission compiled C) C.TYPES C.FUNCS returns locals code jumpTables labels stack (.UNREACHABLE :: after) target.val next output) ∨
    code[pc]? = some .Unreachable := by
  cases relation with
  | linear head ordinary fragment rest => exact False.elim (scalarEmission_not_unreachable (FloatHeads.project (.core (.pure .unreachable)) head))
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
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
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
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .UNREACHABLE::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ pc : U32, out.2.1 = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        ((out.1 = .Ok () ∧ Execution view code store out.2.1 initial expected pc.val false ∧
          ConcreteSim compiled.code.length raw.pc.val pc.val false false initial initial ∧
          (∀ bounds, Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds initial)) ∨
         (out.1 = .Err (.Trap .Unreachable) ∧ ∃ n, 0 < n ∧ Spec.StepsHN n (Abs.decode initial) []
           ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  rcases coreCodeRel_unreachable_inv point.code.current with skip | fetched
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
      Or.inl ⟨rfl,dispatchMeasure_forward _ _ _ _ forward continuation.entry_bound⟩,fun _ h => h⟩⟩
  · have pcBound : raw.pc.val < U32.max := by
      have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have cap := program.fetchBound
      omega
    apply WP.spec_mono (step_unreachable_refines memory hooks floats allocator exec store platform index raw inst compiled
      (Store.decodeStore view code store) ambient f rest after last frameFound instanceFound codeFound pcBound fetched machine.typed.typed)
    intro out effect
    obtain ⟨trapped,sameStore,samePlatform,⟨pc,pcNext,exactState⟩,simulation⟩ := effect
    exact ⟨sameStore,samePlatform,pc,exactState,Or.inr ⟨trapped,simulation⟩⟩
end Itasca.Runtime.Interp.StructuredMachine.Unreachable
