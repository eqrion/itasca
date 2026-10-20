import Exec.Code.Body.Reader.Calls.ReaderCallLowering
import Exec.Code.Body.Reader.Table.ReaderLiteralTables
import Exec.Code.Body.Reader.Table.ReaderLiteralTablesWasm1
import Exec.Code.Body.Relations.Common.ExecutableInstructionPrefix
import Exec.Code.Local.Checking.FrameExitSlotBounds

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Actual direct-call reading bounds its source base and retains earlier instruction and exit-slot checks. -/
theorem reader_call_open_instructions_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (known : ConcreteStack st.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (metadata : FunctionParameterSlots before env)
    (layout : CompilerLayout before (Sequence.stackTypes st.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 16#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_CALL before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ft,values,front,base,found,input,post,baseAt,lowered⟩ :=
    reader_emit_call_wasm1 p ops law before after out known monomorphic metadata layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := reader_call_tables_wasm1 ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  obtain ⟨inputs,_⟩ := lowered.1.source_capacities layout reachable
  rw [input,slots_append] at inputs
  have valid : runtime.bytecode.CompiledFunction.instruction_valid after.function (.Call index base) = .ok true :=
    (CoreInstructionBounds.call (by omega)).accepts
  refine ⟨lowered.1.openInstructionPrefix tables held ?owners valid,
    exits.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity⟩
  intro index owned
  simpa only [PendingInstructionSite,stable.frames] using owned

/-- Actual direct-call reading bounds its source base and retains earlier instruction and exit-slot checks. -/
theorem reader_call_open_instructions_wasm2 {data env locals typeIndex st}
    (p : Wasm2.Pending data env locals typeIndex st) {A : Type}
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
  have tables := reader_call_tables_wasm2 ops law before after st out data env ctx typeIndex (by simpa only [global_simps] using accepted)
  obtain ⟨inputs,_⟩ := lowered.1.source_capacities layout reachable
  rw [input,slots_append] at inputs
  have valid : runtime.bytecode.CompiledFunction.instruction_valid after.function (.Call index base) = .ok true :=
    (CoreInstructionBounds.call (by omega)).accepts
  refine ⟨lowered.1.openInstructionPrefix tables held ?owners valid,
    exits.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity⟩
  intro index owned
  simpa only [PendingInstructionSite,stable.frames] using owned

end Exec.Code
