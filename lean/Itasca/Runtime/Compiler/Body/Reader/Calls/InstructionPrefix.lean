import Itasca.Runtime.Compiler.Body.Reader.Calls.CallLowering
import Itasca.Runtime.Compiler.Body.Reader.Replay.OrdinaryEffects
import Itasca.Runtime.Compiler.Body.Relations.Checking.ExecutableInstructionPrefix
import Itasca.Runtime.Compiler.Local.Checking.FrameExitSlotBounds
import Itasca.Runtime.Compiler.Body.Reader.Calls.IndirectEmission
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerPairTableAppend
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Local.Checking.DeadInstructionPrefix

/-!
Direct and indirect call instruction-prefix certificates, preserving checked instructions and exit-slot bounds for compiler replay.
-/

/-! ## Reader Call Instruction Prefix -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual direct-call reading bounds its source base and retains earlier instruction and exit-slot checks. -/
theorem reader_call_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env .Wasm2 locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (metadata : FunctionParameterSlots before env)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 16#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 16#u8 before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ft,values,front,base,found,input,post,baseAt,lowered⟩ :=
    reader_emit_call_wasm2 p ops law before after out ctx known monomorphic metadata layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_call_effects_wasm2 ops law before after st out data env ctx typeIndex (by simpa only [global_simps] using accepted)).tables
  obtain ⟨inputs,_⟩ := lowered.1.source_capacities layout reachable
  rw [input,slots_append] at inputs
  have valid : runtime.bytecode.CompiledFunction.instruction_valid after.function (.Call index base) = .ok true :=
    (CoreInstructionBounds.call (by omega)).accepts
  refine ⟨lowered.1.openInstructionPrefix tables held ?owners valid,
    exits.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity⟩
  intro index owned
  simpa only [PendingInstructionSite,stable.frames] using owned

end Itasca.Runtime.Code

end

/-! ## Reader Indirect Instruction Prefix -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual indirect-call reading checks the captured table row and source operand region. -/
theorem reader_indirect_call_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env .Wasm2 locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (C : context) (matched : EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = compilerLocals before)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex .Wasm2 17#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,table,values,emitted,output,pairs,post,lowered,emission⟩ :=
    reader_emit_indirect_call_wasm2 p ops law before after out ctx C matched contextLocals signatures known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  obtain ⟨otherIndex,otherTable,_,callback,_⟩ := reader_indirect_call_wasm2 p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 17#u16 otherIndex otherTable 0#u128 = _ at callback
  have tables := compiler_tables_pair_append before.function after.function _ pairs
    (compiler_indirect_call_auxiliary_tables ops law before after out.core otherIndex otherTable (.Ok ()) callback)
  have growth := instruction_check_extends_of_tables_append before.function after.function _ tables
    stable.capacity (by change before.function.code.val.length ≤ after.function.code.val.length; rw [lowered.1.1,List.length_append,List.length_singleton]; omega)
  exact ⟨lowered.1.executableInstructionPrefix layout reachable contextLocals
    (.indirect emission) (by intro depths fallback same; cases same) growth held stable.frames,
    exits.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity⟩

end Itasca.Runtime.Code

end

/-! ## Reader Call Checked Prefix -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual call reading preserves both invariants on live and unreachable paths. -/
theorem reader_call_checked_prefix_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (metadata : FunctionParameterSlots before env)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 16#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 16#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_call_open_instructions_wasm2 p ops law before after out ctx (invariant.known live) (monomorphic live) metadata retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · obtain ⟨target,_,callback,_⟩ := reader_call_wasm2 p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    change runtime.compiler.lower.FunctionCompiler.op ops before out.core 16#u16 target 0#u32 0#u128 = _ at callback
    exact compiler_dead_op_checked_prefix ops law before after out.core 16#u16 target 0#u32 0#u128 (Bool.eq_false_iff.mpr live) held exits callback

/-- Actual call reading preserves both invariants on live and unreachable paths. -/
theorem reader_indirect_call_checked_prefix_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (C : context) (matched : EnvTranslation.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 17#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_indirect_call_open_instructions_wasm2 p ops law before after out ctx C matched (contextLocals.trans retained.localsEq.symm) signatures (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · obtain ⟨target,table,_,callback,_⟩ := reader_indirect_call_wasm2 p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
    change runtime.compiler.lower.FunctionCompiler.op ops before out.core 17#u16 target table 0#u128 = _ at callback
    exact compiler_dead_op_checked_prefix ops law before after out.core 17#u16 target table 0#u128 (Bool.eq_false_iff.mpr live) held exits callback

end Itasca.Runtime.Code

end
