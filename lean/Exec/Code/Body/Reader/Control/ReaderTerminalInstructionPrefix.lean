import Exec.Code.Body.Reader.Control.ReaderPrefixReturn
import Exec.Code.Body.Reader.Common.ReaderPrefixUnreachable
import Exec.Code.Body.Control.Table.StructuredCompilerPrefixWithTables
import Exec.Code.Local.Checking.TerminalInstructionPrefix
import Exec.Code.Local.Checking.ScalarExitSlotBounds

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Actual source RETURN checks its full result suffix and retains recorded exits. -/
theorem reader_return_open_instructions_wasm1 {jumpTables : List U32} {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {emit types functions locals parents current}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions (ctx.results.val.map Translate.valueType)
      locals parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (bodyResults : Control.resultTypes bt = ctx.results.val.map Translate.valueType)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_RETURN)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_RETURN before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨callback, read, values, post⟩ := reader_return_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
  refine ⟨?_,(compiler_return_ordinary_result ops law before after out (.Ok ()) callback).exit_slots exits⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨frame, found, resultWidth⟩ := reader_root_frame_wasm1 p before invariant.frames same
    rw [bodyResults] at resultWidth
    obtain ⟨_, outer, _, _, base, _, controls, vals⟩ := p.opened
    obtain ⟨front, input⟩ := reader_return_stack_wasm1 st out ctx outer p.current.vals vals
      (by simpa [Control.base, controls] using base)
      (invariant.known reachable) (by simpa [Control.polymorphic, controls] using monomorphic reachable) read
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    have layout := (invariant.live reachable).2.layout
    have capacity := layout.capacity reachable
    rw [input] at layout
    have bounded : slots (compilerLocals before)+slots front < 2^32 := by
      have bound := before.height.hBounds
      change before.height.val < 2^32 at bound
      rw [layout.height,slots_append] at bound
      omega
    let source : U32 := UScalar.ofNatCore (slots (compilerLocals before)+slots front) bounded
    have sourcePosition : source.val = slots (compilerLocals before)+slots front := rfl
    have height : before.height.val = source.val+frame.results.val := by
      rw [layout.height,slots_append,sourcePosition,resultWidth]
      omega
    exact compiler_return_live_open_instructions ops law before after out frame source reachable found height capacity
      codeFits sourceFits coordinateFits held callback
  · exact compiler_return_dead_open_instructions ops law before after out (Bool.eq_false_iff.mpr reachable) held callback

/-- Actual source RETURN checks its full result suffix and retains recorded exits. -/
theorem reader_return_open_instructions_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions locals parents current}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions (p.ft.results.val.map Translate.valueType)
      locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 15#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 15#u8 before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨callback, read, values, post⟩ := reader_return_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  refine ⟨?_,(compiler_return_ordinary_result ops law before after out.core (.Ok ()) callback).exit_slots exits⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨frame, found, resultWidth⟩ := reader_root_frame_wasm2 p before invariant.frames same
    obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
    obtain ⟨front, input⟩ := reader_return_stack_wasm2 st out env index p.ft.results.val outer p.current.vals
      (by simp [Wasm2.resolve, p.signature]) vals (by simpa [Control.base, controls] using base)
      (invariant.known reachable) (by simpa [Control.polymorphic, controls] using monomorphic reachable) read
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    have layout := (invariant.live reachable).2.layout
    have capacity := layout.capacity reachable
    rw [input] at layout
    have bounded : slots (compilerLocals before)+slots front < 2^32 := by
      have bound := before.height.hBounds
      change before.height.val < 2^32 at bound
      rw [layout.height,slots_append] at bound
      omega
    let source : U32 := UScalar.ofNatCore (slots (compilerLocals before)+slots front) bounded
    have sourcePosition : source.val = slots (compilerLocals before)+slots front := rfl
    have height : before.height.val = source.val+frame.results.val := by
      rw [layout.height,slots_append,sourcePosition,resultWidth]
      omega
    exact compiler_return_live_open_instructions ops law before after out.core frame source reachable found height capacity
      codeFits sourceFits coordinateFits held callback
  · exact compiler_return_dead_open_instructions ops law before after out.core (Bool.eq_false_iff.mpr reachable) held callback

/-- Actual trap reading preserves all earlier checks and emits a checked trap word when live. -/
theorem reader_unreachable_open_instructions_wasm1 {jumpTables : List U32} {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals parents current st.vals.val p.start.val)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨callback, values, post⟩ := reader_unreachable_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities sourceBound
  have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  exact ⟨compiler_unreachable_open_instructions ops law before after out codeFits sourceFits coordinateFits held callback,
    (compiler_unreachable_ordinary_result ops law before after out (.Ok ()) callback).exit_slots exits⟩

/-- Actual trap reading preserves all earlier checks and emits a checked trap word when live. -/
theorem reader_unreachable_open_instructions_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_UNREACHABLE before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨callback, values, post⟩ := reader_unreachable_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities sourceBound
  have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  exact ⟨compiler_unreachable_open_instructions ops law before after out.core codeFits sourceFits coordinateFits held callback,
    (compiler_unreachable_ordinary_result ops law before after out.core (.Ok ()) callback).exit_slots exits⟩

end Exec.Code
