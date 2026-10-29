import Itasca.Runtime.Compiler.Local.Lowering.Table.ScalarTablePreservation
import Itasca.Runtime.Compiler.Body.Reader.References.TypedSelectEmission
import Itasca.Runtime.Compiler.Body.Relations.Checking.ExecutableInstructionPrefix
import Itasca.Runtime.Compiler.Local.Checking.FrameExitSlotBounds
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Local.Checking.DeadInstructionPrefix

/-!
Open-instruction and checked-prefix preservation for typed-select reader steps.
-/

/-! ## Reader Typed Select Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual typed select uses the source-selected width for its instruction check. -/
theorem reader_typed_select_open_instructions_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (C : context) (localsMatch : compilerLocals before = C.LOCALS)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 28#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,ty,front,values,emitted,input,post,lowered,emission⟩ :=
    reader_emit_typed_select_wasm2 p ops law before after out ctx C localsMatch known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  obtain ⟨other,position,callback,_⟩ := reader_typed_select_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 28#u16 0#u32 0#u32 0#u128 = _ at callback
  have tables := compiler_core_tables ops law before after out.core (.select true) callback
  have growth := lowered.1.instruction_check_extends tables
  rw [input] at layout
  exact ⟨lowered.1.executable_instruction_prefix layout reachable localsMatch.symm
    (.typedSelect emission) (by intro depths fallback same; cases same) growth held stable.frames,
    exits.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity⟩

end Itasca.Runtime.Compiler

end

/-! ## Reader Typed Select Checked Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Typed select preserves both invariants for either source reachability bit;
only live source code emits the selected-width instruction. -/
theorem reader_typed_select_checked_prefix_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (C : context) (contextLocals : C.LOCALS = locals)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 28#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_typed_select_open_instructions_wasm2 p ops law before after out ctx C
      (retained.localsEq.trans contextLocals.symm) (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · obtain ⟨ty,position,callback,_⟩ := reader_typed_select_wasm2 p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
    change runtime.compiler.lower.FunctionCompiler.op ops before out.core 28#u16 0#u32 0#u32 0#u128 = _ at callback
    exact compiler_dead_op_checked_prefix ops law before after out.core 28#u16 0#u32 0#u32 0#u128
      (Bool.eq_false_iff.mpr live) held exits callback

end Itasca.Runtime.Compiler

end
