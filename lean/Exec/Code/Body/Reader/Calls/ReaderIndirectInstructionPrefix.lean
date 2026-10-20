import Exec.Code.Body.Reader.Calls.ReaderIndirectEmission
import Exec.Code.Body.Reader.Calls.ReaderIndirectEmissionWasm1
import Exec.Code.Body.Relations.Common.ExecutableInstructionPrefix
import Exec.Code.Local.Checking.FrameExitSlotBounds
import Exec.Code.Local.Callbacks.Table.CompilerPairTableAppend

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Actual indirect-call reading checks the captured table row and source operand region. -/
theorem reader_indirect_call_open_instructions_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context) (matched : EnvTranslation.Matches env ctx C)
    (contextLocals : C.LOCALS = compilerLocals before)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_CALL_INDIRECT before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,values,emitted,output,pairs,post,lowered,emission⟩ :=
    reader_emit_indirect_call_wasm1 p ops law before after out C matched contextLocals signatures known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  obtain ⟨otherIndex,_,callback,_⟩ := reader_indirect_call_wasm1 p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out
      (by have bound := p.val_capacity; omega) byte accepted
  change runtime.compiler.lower.FunctionCompiler.op ops before out 17#u16 otherIndex 0#u32 0#u128 = _ at callback
  have tables := compiler_tables_pair_append before.function after.function _ pairs
    (compiler_indirect_call_auxiliary_tables ops law before after out otherIndex 0#u32 (.Ok ()) callback)
  have growth := instruction_check_extends_of_tables_append before.function after.function _ tables
    stable.capacity (by change before.function.code.val.length ≤ after.function.code.val.length; rw [lowered.1.1,List.length_append,List.length_singleton]; omega)
  exact ⟨lowered.1.executableInstructionPrefix layout reachable contextLocals
    (.base (.left (.indirect emission))) (by intro depths fallback same; cases same) growth held stable.frames,
    exits.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity⟩

/-- Actual indirect-call reading checks the captured table row and source operand region. -/
theorem reader_indirect_call_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
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
    (.base (.left (.indirect emission))) (by intro depths fallback same; cases same) growth held stable.frames,
    exits.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity⟩

end Exec.Code
