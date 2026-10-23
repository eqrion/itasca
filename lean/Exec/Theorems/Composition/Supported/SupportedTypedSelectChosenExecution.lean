import Exec.Theorems.Composition.Supported.ChosenSupportedOutcome
import Exec.Interp.StructuredMachine.TypedSelectChosenExecution
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
theorem step_typed_select_supported_execution_chosen {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat)
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame)
    (f : Abs.AFrame) (rest : List Abs.AFrame) (declared : valtype) (after : List instr)
    (last : index.val+1 = exec.frames.length) (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint (Store.decodeStore view code store) raw {f with code := .SELECT (some [declared])::after} compiled C targets next output)
    (expected : List valtype)
    (machine : StructuredMachine.Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .SELECT (some [declared])::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ChosenSupportedStepOutcome choices occurrence allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=.SELECT (some [declared])::after}::rest,[]⟩ out ⦄ := by
  apply WP.spec_mono (StructuredMachine.TypedSelect.step_execution_chosen admissible vector occurrence memory hooks floats allocator exec store platform index raw inst compiled
    C targets next output view code ambient f rest declared after last frameFound instanceFound codeFound slots point expected machine program)
  rintro out ⟨success,sameStore,samePlatform,pc,g,fresh,simulation,owned,bounded⟩
  exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success
    (StructuredMachine.ChosenAdvance.of_frame fresh simulation owned rfl bounded)
end Exec.Theorems
