import Itasca.Runtime.Code.Body.Reader.Control.ReaderEnterPublicationWasm2
import Itasca.Runtime.Code.Body.Reader.Control.ReaderEndPublication
import Itasca.Runtime.Code.Body.Reader.Table.ReaderTablePublication
import Itasca.Runtime.Code.Local.Coordinates.LoweringTargetBounds
import Itasca.Runtime.Code.Local.Coordinates.TableCallbackTargetBounds

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
