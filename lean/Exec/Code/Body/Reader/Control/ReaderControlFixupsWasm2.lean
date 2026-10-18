import Exec.Code.Local.Callbacks.Calls.FixupCallbacks
import Exec.Code.Body.Reader.Common.ReaderEnterWasm2
import Exec.Code.Body.Reader.Control.ReaderBranchWasm2
import Exec.Code.Body.Reader.Common.ReaderCloseWasm2
import Exec.Code.Body.Reader.Control.ReaderCompilerScopes
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_block_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = 2#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 2#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  obtain ⟨bt,ins,outs,remaining,base,callback,_,_⟩ := reader_enter_wasm2 p .block (.inl rfl)
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_enter_fixup_budget ops law before after out.core .Block bt budget callback

theorem reader_loop_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = 3#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 3#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  obtain ⟨bt,ins,outs,remaining,base,callback,_,_⟩ := reader_enter_wasm2 p .loop (.inr (.inl rfl))
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_enter_fixup_budget ops law before after out.core .Loop bt budget callback

theorem reader_if_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = 4#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 4#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  obtain ⟨bt,ins,outs,remaining,base,callback,_,_⟩ := reader_enter_wasm2 p .then_ (.inr (.inr rfl))
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_enter_fixup_budget ops law before after out.core .Then bt budget callback

theorem reader_br_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = 12#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 12#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  obtain ⟨depth,view,callback,_,_⟩ := reader_br_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_br_fixup_budget ops law before after out.core depth view budget callback

theorem reader_br_if_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = 13#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 13#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  obtain ⟨depth,view,values,callback,_,_⟩ := reader_br_if_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_br_if_fixup_budget ops law before after out.core depth view budget callback

theorem reader_else_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = 5#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 5#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  have callback := (reader_else_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted).1
  exact compiler_else_fixup_budget ops law before after out.core p.current.bt budget callback

theorem reader_end_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  have callback := (reader_end_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted).1
  exact compiler_end_fixup_budget ops law before after out.core p.current.ctrl.kind p.current.bt budget callback

theorem reader_scope_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (opcode : U8) (supported : ScopeOpcode opcode)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  simp only [ScopeOpcode,List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with h | h | h | h | h
  · have equal : opcode = 2#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_block_fixup_budget_wasm2 p ops law before after out ctx budget byte accepted
  · have equal : opcode = 3#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_loop_fixup_budget_wasm2 p ops law before after out ctx budget byte accepted
  · have equal : opcode = 4#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_if_fixup_budget_wasm2 p ops law before after out ctx budget byte accepted
  · have equal : opcode = 12#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_br_fixup_budget_wasm2 p ops law before after out ctx budget byte accepted
  · have equal : opcode = 13#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_br_if_fixup_budget_wasm2 p ops law before after out ctx budget byte accepted
end Exec.Code
