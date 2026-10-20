import Exec.Code.Body.Reader.Control.ReaderEnterPublicationWasm1
import Exec.Code.Body.Reader.Control.ReaderEnterPublicationWasm2
import Exec.Code.Body.Reader.Control.ReaderEndPublication
import Exec.Code.Body.Reader.Table.ReaderTablePublication
import Exec.Code.Local.Coordinates.LoweringTargetBounds
import Exec.Code.Local.Coordinates.TableCallbackTargetBounds

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Actual Wasm 1 opening readers retain jump targets while emitting entry code. -/
theorem reader_enter_target_bounds_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (held : JumpTableBounds before) (opcode : U8)
    (allowed : opcode = code.OP_BLOCK ∨ opcode = code.OP_LOOP ∨ opcode = code.OP_IF)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode before = .ok (.Ok (),out,after)) : JumpTableBounds after := by
  rcases allowed with rfl | rfl | rfl
  · obtain ⟨bt,callback,_,_⟩ := reader_block_wasm1 p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
    exact compiler_enter_target_bounds ops law before after out .Block (Control.signature bt) held callback
  · obtain ⟨bt,callback,_,_⟩ := reader_loop_wasm1 p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
    exact compiler_enter_target_bounds ops law before after out .Loop (Control.signature bt) held callback
  · obtain ⟨bt,remaining,callback,_,_⟩ := reader_if_wasm1 p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
    exact compiler_enter_target_bounds ops law before after out .Then (Control.signature bt) held callback

/-- Actual Wasm 2 openings retain targets independently of the selected signature. -/
theorem reader_enter_target_bounds_wasm2 {data env localTypes index st}
    (p : Wasm2.Pending data env localTypes index st) {A : Type}
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

/-- Actual Wasm 1 END retains target bounds while patching instructions. -/
theorem reader_end_target_bounds_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (held : JumpTableBounds before) (byte : data.val[p.start.val]'p.inbounds = code.OP_END)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx code.OP_END before = .ok (.Ok (),out,after)) : JumpTableBounds after := by
  have callback := (reader_end_wasm1 p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    before after out byte accepted).1
  exact compiler_end_target_bounds ops law before after out p.current.ctrl.kind (Control.signature p.current.ctrl.block_type) held callback

/-- Actual Wasm 2 END retains target bounds while patching instructions. -/
theorem reader_end_target_bounds_wasm2 {data env localTypes index st}
    (p : Wasm2.Pending data env localTypes index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (held : JumpTableBounds before) (byte : data.val[p.start.val]'p.inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after)) : JumpTableBounds after := by
  have callback := (reader_end_wasm2 p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    before after out ctx byte accepted).1
  exact compiler_end_target_bounds ops law before after out.core p.current.ctrl.kind p.current.bt held callback

/-- Wasm 1 collection changes only scratch before its final table callback. -/
theorem reader_table_target_bounds_wasm1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (held : JumpTableBounds before)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BR_TABLE before = .ok (.Ok (),final,after)) : JumpTableBounds after := by
  obtain ⟨actual,common,collected,read,callback⟩ := reader_table_dispatch_wasm1
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st final data env ctx before after accepted
  obtain ⟨count,first,last,ending,depths,budget,buffer,_,_,_,_,same,_⟩ :=
    compiler_read_br_table_wasm1 ops law before collected st final data actual common read
  subst collected
  exact compiler_br_table_target_bounds ops law {before with budget,table_depths := buffer} after final actual
    (Control.resultView common) (by simpa only [JumpTableBounds] using held) callback

/-- Wasm 2 selector and label collection retain all prior targets before dispatch. -/
theorem reader_table_target_bounds_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st final : code.BodyState) (data : Slice U8) (env : module.Env) (held : JumpTableBounds before)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env before = .ok (.Ok (),final,after)) : JumpTableBounds after := by
  obtain ⟨count,first,selector,popped,depths,fallback,types,last,readState,budget,buffer,_,_,_,_,_,_,_,callback⟩ :=
    compiler_read_br_table_wasm2 ops law before after st final data env accepted
  exact compiler_br_table_target_bounds ops law {before with budget,table_depths := buffer} after final.core fallback
    types (by simpa only [JumpTableBounds] using held) callback

end Exec.Code
