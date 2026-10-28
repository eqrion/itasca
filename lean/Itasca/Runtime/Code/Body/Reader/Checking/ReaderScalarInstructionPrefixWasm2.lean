import Itasca.Runtime.Code.Body.Reader.Checking.ReaderDeadScalarInstructionPrefix
import Itasca.Runtime.Code.Body.Reader.Checking.ReaderNoopInstructionPrefix
import Itasca.Runtime.Code.Body.Reader.Checking.ReaderConstantInstructionPrefix
import Itasca.Runtime.Code.Body.Reader.Checking.ReaderCoreInstructionPrefix
import Itasca.Runtime.Code.Body.Reader.Control.ReaderTerminalInstructionPrefix

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Every scalar reader kind preserves both instruction and recorded exit-slot
checks from its source-typed prefix, including all unreachable variants. -/
theorem reader_scalar_checked_prefix_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextSource : ctx.locals = sourceLocals) (C : context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (localsMatch : before.function.locals = sourceLocals)
    (contextLocals : C.LOCALS = locals)
    (globalsMatch : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (kind : ScalarReaderKind) (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = kind.opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 kind.opcode before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  have sourcePosition : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities sourcePosition
  have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have known := invariant.known live
    have layout := retained.layout
    have localTypes : C.LOCALS = compilerLocals before := contextLocals.trans retained.localsEq.symm
    obtain ⟨rawTypes,concrete⟩ := (concreteStack_iff st.core.vals.val).mp known
    have literalLayout : CompilerLayout before (rawTypes.map Translate.valueType) := by
      simpa only [concrete,Sequence.stackTypes,List.map_map,Function.comp_def] using layout
    cases kind with
    | nop =>
      exact reader_nop_open_instructions_wasm2 ops law before after st out data env ctx index held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | unreachable =>
      exact reader_unreachable_open_instructions_wasm2 p ops law initial before after out ctx contextSource invariant held exits bodyBound (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | drop =>
      exact reader_drop_open_instructions_wasm2 ops law before after st out data env ctx index held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | select =>
      exact reader_select_open_instructions_wasm2 p ops law before after out ctx contextSource C localTypes.symm known (monomorphic live) layout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | local_get =>
      exact reader_local_get_open_instructions_wasm2 p ops law before after out ctx contextSource localsMatch rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | local_set =>
      exact reader_local_set_open_instructions_wasm2 p ops law before after out ctx contextSource localsMatch known (monomorphic live) layout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | local_tee =>
      exact reader_local_tee_open_instructions_wasm2 p ops law before after out ctx contextSource localsMatch known (monomorphic live) layout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | global_get =>
      exact reader_global_get_open_instructions_wasm2 p ops law before after out ctx contextSource C localTypes.symm globalsMatch rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | global_set =>
      exact reader_global_set_open_instructions_wasm2 p ops law before after out ctx contextSource C localTypes.symm globalsMatch known (monomorphic live) layout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | i32_const =>
      exact reader_const32_open_instructions_wasm2 p ops law before after out ctx contextSource rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | i64_const =>
      exact reader_const64_open_instructions_wasm2 p ops law before after out ctx contextSource rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | f32_const =>
      exact reader_float32_open_instructions_wasm2 p ops law before after C localTypes out ctx contextSource rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
    | f64_const =>
      exact reader_float64_open_instructions_wasm2 p ops law before after C localTypes out ctx contextSource rawTypes concrete literalLayout live codeFits sourceFits coordinateFits held exits (by simpa only [ScalarReaderKind.opcode,global_simps] using byte) (by simpa only [ScalarReaderKind.opcode,global_simps] using accepted)
  · obtain ⟨_,raw⟩ := profile_base_success_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx ctx index kind.opcode before after
      kind.ordinary kind.plain kind.sign kind.misc rfl accepted
    exact reader_dead_scalar_checked_prefix ops law before after st.core out.core data env ctx kind
      (Bool.eq_false_iff.mpr live) codeFits sourceFits coordinateFits held exits raw

end Itasca.Runtime.Code
