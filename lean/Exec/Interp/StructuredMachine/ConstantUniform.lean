import Exec.Interp.StructuredMachine.IntegerConstantExecutionOwned
import Exec.Interp.StructuredMachine.FloatConstantExecutionOwned
import Exec.Interp.StructuredMachine.UniformAdvance
namespace Exec.Interp.StructuredMachine
variable {emission : FunctionEmission} [∀ compiled, FloatHeads (emission compiled)]
variable {allowed supported owned} (semantics : ControlSemantics allowed supported owned)
include semantics
open Aeneas Aeneas.Std SpecExt
theorem IntegerConstant.step_integer32_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : U32) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      UniformAdvance emission supported owned view code store out.2.1 expected compiled.code.length raw.pc.val false initial ⦄ := by
  dsimp only
  apply WP.spec_mono (IntegerConstant.step_integer32_execution_owned_forward semantics memory hooks floats allocator exec store platform index raw inst compiled C targets next output view code ambient f rest value after last frameFound instanceFound codeFound slots point expected machine program)
  rintro out ⟨ok,same,platform,pc,g,forward,fresh,simulation,ownership,bounded⟩
  exact ⟨ok,same,platform,UniformAdvance.of_frame_forward fresh simulation forward ownership rfl bounded⟩

theorem IntegerConstant.step_integer64_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : U64) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      UniformAdvance emission supported owned view code store out.2.1 expected compiled.code.length raw.pc.val false initial ⦄ := by
  dsimp only
  apply WP.spec_mono (IntegerConstant.step_integer64_execution_owned_forward semantics memory hooks floats allocator exec store platform index raw inst compiled C targets next output view code ambient f rest value after last frameFound instanceFound codeFound slots point expected machine program)
  rintro out ⟨ok,same,platform,pc,g,forward,fresh,simulation,ownership,bounded⟩
  exact ⟨ok,same,platform,UniformAdvance.of_frame_forward fresh simulation forward ownership rfl bounded⟩

theorem FloatConstant.step_float32_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .CONST .F32 (.mk_num__1 .F32 value) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value)::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F32 (.mk_num__1 .F32 value)::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      UniformAdvance emission supported owned view code store out.2.1 expected compiled.code.length raw.pc.val false initial ⦄ := by
  dsimp only
  apply WP.spec_mono (FloatConstant.step_float32_execution_owned_forward semantics memory hooks floats allocator exec store platform index raw inst compiled C targets next output view code ambient f rest value after last frameFound instanceFound codeFound slots point expected machine program)
  rintro out ⟨ok,same,platform,pc,g,forward,fresh,simulation,ownership,bounded⟩
  exact ⟨ok,same,platform,UniformAdvance.of_frame_forward fresh simulation forward ownership rfl bounded⟩

theorem FloatConstant.step_float64_uniform {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (value : fN) (after : List instr)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (instanceFound : store.instances.val[raw.instance.val]? = some inst)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (slots : FrameSlots exec raw f)
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := .CONST .F64 (.mk_num__1 .F64 value) :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : Execution emission supported view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value)::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .CONST .F64 (.mk_num__1 .F64 value)::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      UniformAdvance emission supported owned view code store out.2.1 expected compiled.code.length raw.pc.val false initial ⦄ := by
  dsimp only
  apply WP.spec_mono (FloatConstant.step_float64_execution_owned_forward semantics memory hooks floats allocator exec store platform index raw inst compiled C targets next output view code ambient f rest value after last frameFound instanceFound codeFound slots point expected machine program)
  rintro out ⟨ok,same,platform,pc,g,forward,fresh,simulation,ownership,bounded⟩
  exact ⟨ok,same,platform,UniformAdvance.of_frame_forward fresh simulation forward ownership rfl bounded⟩

end Exec.Interp.StructuredMachine
