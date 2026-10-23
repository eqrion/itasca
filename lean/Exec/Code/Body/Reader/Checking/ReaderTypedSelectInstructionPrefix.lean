import Exec.Code.Local.Lowering.Table.ScalarTablePreservation
import Exec.Code.Body.Reader.Common.ReaderTypedSelectEmission
import Exec.Code.Body.Relations.Common.ExecutableInstructionPrefix
import Exec.Code.Local.Checking.FrameExitSlotBounds

namespace Exec.Code
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
  have growth := lowered.1.instructionCheckExtends tables
  rw [input] at layout
  exact ⟨lowered.1.executableInstructionPrefix layout reachable localsMatch.symm
    (.typedSelect emission) (by intro depths fallback same; cases same) growth held stable.frames,
    exits.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity⟩

end Exec.Code
