import Itasca.Runtime.Compiler.Body.Reader.Publication.NonScopeCallbackPublication
import Itasca.Runtime.Compiler.Local.Coordinates.LoweringTargetBounds
import Itasca.Runtime.Compiler.Local.Coordinates.TableCallbackTargetBounds
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CallbackTables
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Body.Reader.Control.EnterPublicationWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.EndPublication
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTablePublication
import Itasca.Runtime.Compiler.Body.Reader.Replay.CallbackProfile
import Itasca.Wasm2.Trace.TableBytes

/-!
Published jump-target bounds across ordinary and scope reader steps. The final reader theorem assembles the operation-specific target bounds.
-/

/-! ## Non Scope Target Bounds -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Every non-scope-boundary event retains valid jump-table targets. Tables
append only actual branch-stub positions; all other callbacks retain the table. -/
theorem compiler_non_scope_hook_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) {action : Action} (supported : NonScopePublicationAction action)
    (held : JumpTableBounds before)
    (called : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before (.op state action) =
      .ok (.Ok (),after)) : JumpTableBounds after := by
  cases supported with
  | scalar supported =>
    obtain ⟨opcode,a,b,bits,member,dispatch⟩ := scalar_hook_publication_dispatch ops before state supported
    rw [dispatch] at called
    exact compiler_scalar_target_bounds ops law before after state opcode a b bits member held called
  | numeric hook =>
    rcases numeric_hook_publication_dispatch ops before state hook with ⟨op,dispatch⟩ | ⟨op,dispatch⟩
    · rw [dispatch] at called
      exact compiler_numeric_target_bounds ops law before after state op held called
    · rw [dispatch] at called
      exact compiler_float_target_bounds ops law before after state op held called
  | extendedNumeric hook =>
    rcases extended_numeric_hook_publication_dispatch ops before state hook with ⟨op,dispatch⟩ | ⟨op,dispatch⟩
    · rw [dispatch] at called
      exact compiler_numeric_target_bounds ops law before after state op held called
    · rw [dispatch] at called
      exact compiler_float_target_bounds ops law before after state op held called
  | memory hook arg =>
    have range : 40 ≤ hook.opcode.val ∧ hook.opcode.val ≤ 62 := by cases hook <;> decide
    have visited := (MemoryHook.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before state hook arg).trans called
    rcases source_memory_byte_partition hook.opcode range.1 range.2 with ⟨op,byte⟩ | ⟨op,byte⟩
    · have dispatch := (memory_load_reader_facts ops before state op arg).2.2.2.2.1
      rw [← byte,dispatch] at visited
      exact compiler_core_target_bounds ops law before after state (.load op arg.offset arg.align) held visited
    · have dispatch := (memory_store_reader_facts ops before state op arg).2.2.2.2.1
      rw [← byte,dispatch] at visited
      exact compiler_core_target_bounds ops law before after state (.store op arg.offset arg.align) held visited
  | simd supported =>
    obtain ⟨opcode,a,b,bits,lower,upper,dispatch⟩ := simd_hook_publication_dispatch ops before state supported
    rw [dispatch] at called
    exact compiler_simd_target_bounds ops law before after state opcode a b bits lower upper held called
  | unreachable =>
    exact held.retained (after := after)
      (congrArg CompilerTables.jumpTables (compiler_unreachable_tables ops law before after state called))
      (compiler_unreachable_code_mono ops law before after state called)
  | return_ =>
    exact held.retained (after := after)
      (congrArg CompilerTables.jumpTables (compiler_return_tables ops law before after state called))
      (compiler_return_code_mono ops law before after state called)
  | br depth types =>
    exact held.retained (after := after)
      (congrArg CompilerTables.jumpTables (compiler_br_tables ops law before after state depth types called))
      (compiler_br_code_mono ops law before after state depth types called)
  | br_if depth types =>
    exact held.retained (after := after)
      (congrArg CompilerTables.jumpTables (compiler_br_if_tables ops law before after state depth types called))
      (compiler_br_if_code_mono ops law before after state depth types called)
  | label depth => exact compiler_table_label_target_bounds ops law before after state depth held called
  | table fallback types => exact compiler_br_table_target_bounds ops law before after state fallback types held called
  | else_ bt =>
    exact held.retained (after := after)
      (congrArg CompilerTables.jumpTables (compiler_else_tables ops law before after state bt called))
      (compiler_else_code_mono ops law before after state bt called)

end Itasca.Runtime.Code

end

/-! ## Reader Target Bounds -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Actual Wasm 2 openings retain targets independently of the selected signature. -/
theorem reader_enter_target_bounds_wasm2 {data env localTypes index st}
    (p : Wasm2.Pending data env .Wasm2 localTypes index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (held : JumpTableBounds before) (form : Wasm2.Frames.Form) (initial : form.Initial)
    (byte : data.val[p.start.val]'p.inbounds = form.opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 form.opcode before = .ok (.Ok (),out,after)) : JumpTableBounds after := by
  obtain ⟨bt,ins,outs,remaining,base,callback,_,post⟩ := reader_enter_wasm2 p form initial
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have called : runtime.compiler.control.FunctionCompiler.enter ops before out.core form.kind bt = .ok (.Ok (),after) := by
    rcases initial with rfl | rfl | rfl <;> exact callback
  exact compiler_enter_target_bounds ops law before after out.core form.kind bt held called

/-- Actual Wasm 2 END retains target bounds while patching instructions. -/
theorem reader_end_target_bounds_wasm2 {data env localTypes index st}
    (p : Wasm2.Pending data env .Wasm2 localTypes index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (held : JumpTableBounds before) (byte : data.val[p.start.val]'p.inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after)) : JumpTableBounds after := by
  have callback := (reader_end_wasm2 p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    before after out ctx byte accepted).1
  exact compiler_end_target_bounds ops law before after out.core p.current.ctrl.kind p.current.bt held callback

/-- Wasm 2 selector and label collection retain all prior targets before dispatch. -/
theorem reader_table_target_bounds_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : module.Env) (held : JumpTableBounds before)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env .Wasm2 before = .ok (.Ok (),final,after)) : JumpTableBounds after := by
  obtain ⟨count,first,selector,popped,depths,fallback,types,last,readState,budget,buffer,_,_,_,_,_,_,_,callback⟩ :=
    compiler_read_br_table ops law before after st final data env _ accepted
  exact compiler_br_table_target_bounds ops law {before with budget,table_depths := buffer} after final.core fallback
    types (by simpa only [JumpTableBounds] using held) callback

end Itasca.Runtime.Code

end

/-! ## Reader Jump Targets -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace Itasca.Wasm2

/-- Every accepted complete-profile Wasm 2 reader step retains bounded jump
targets, including SIMD, dead bodies, branches, references and streamed tables. -/
theorem reader_jump_targets_wasm2 {data env localTypes index st}
    (p : Wasm2.Pending data env .Wasm2 localTypes index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (held : JumpTableBounds before)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (data.val[p.start.val]'p.inbounds) before = .ok (.Ok (),out,after)) : JumpTableBounds after := by
  let opcode := data.val[p.start.val]'p.inbounds
  by_cases h2 : opcode = 2#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index .Wasm2 2#u8 before = .ok (.Ok (),out,after) := by simpa only [← h2] using accepted
    exact reader_enter_target_bounds_wasm2 p ops law before after out ctx held .block (.inl rfl) h2 call
  by_cases h3 : opcode = 3#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index .Wasm2 3#u8 before = .ok (.Ok (),out,after) := by simpa only [← h3] using accepted
    exact reader_enter_target_bounds_wasm2 p ops law before after out ctx held .loop (.inr (.inl rfl)) h3 call
  by_cases h4 : opcode = 4#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index .Wasm2 4#u8 before = .ok (.Ok (),out,after) := by simpa only [← h4] using accepted
    exact reader_enter_target_bounds_wasm2 p ops law before after out ctx held .then_ (.inr (.inr rfl)) h4 call
  by_cases h11 : opcode = 11#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after) := by simpa only [← h11] using accepted
    exact reader_end_target_bounds_wasm2 p ops law before after out ctx held h11 call
  by_cases h14 : opcode = 14#u8
  · have call : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
        st data env ctx index .Wasm2 14#u8 before = .ok (.Ok (),out,after) := by simpa only [← h14] using accepted
    rw [CallbackTrace.dispatch_br_table] at call
    exact reader_table_target_bounds_wasm2 ops law before after st out data env held call
  have blocked : opcode ≠ code.OP_BLOCK ∧ opcode ≠ code.OP_LOOP ∧ opcode ≠ code.OP_IF ∧
      opcode ≠ code.OP_END ∧ opcode ≠ code.OP_BR_TABLE := by
    simp only [global_simps]
    tauto
  obtain ⟨action,ordinary,range,callback⟩ := reader_single_callback_profile_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index opcode before after blocked accepted
  exact compiler_non_scope_hook_target_bounds ops law before after out.core (.of_range action range ordinary) held callback

end Itasca.Runtime.Code

end
