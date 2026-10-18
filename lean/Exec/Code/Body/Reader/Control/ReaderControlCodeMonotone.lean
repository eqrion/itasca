import Exec.Code.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Exec.Code.Body.Reader.Common.ReaderEnterWasm2
import Exec.Code.Body.Reader.Control.ReaderBranchWasm2
import Exec.Code.Body.Reader.Common.ReaderCloseWasm2
import Exec.Code.Body.Reader.Control.ReaderCompilerScopes
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_block_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 2#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 2#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨bt,ins,outs,remaining,base,callback,_,_⟩ := reader_enter_wasm2 p .block (.inl rfl)
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_block_code_mono ops law before after out.core bt callback

theorem reader_loop_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 3#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 3#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨bt,ins,outs,remaining,base,callback,_,_⟩ := reader_enter_wasm2 p .loop (.inr (.inl rfl))
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_loop_code_mono ops law before after out.core bt callback

theorem reader_if_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 4#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 4#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨bt,ins,outs,remaining,base,callback,_,_⟩ := reader_enter_wasm2 p .then_ (.inr (.inr rfl))
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_if_code_mono ops law before after out.core bt callback

theorem reader_br_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 12#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 12#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨depth,view,callback,_,_⟩ := reader_br_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_br_code_mono ops law before after out.core depth view callback

theorem reader_br_if_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 13#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 13#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨depth,view,values,callback,_,_⟩ := reader_br_if_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_br_if_code_mono ops law before after out.core depth view callback

theorem reader_else_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 5#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 5#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  have callback := (reader_else_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted).1
  exact compiler_else_code_mono ops law before after out.core p.current.bt callback

theorem reader_end_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  have callback := (reader_end_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted).1
  exact compiler_end_code_mono ops law before after out.core p.current.ctrl.kind p.current.bt callback

theorem reader_scope_code_mono_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (opcode : U8) (supported : ScopeOpcode opcode)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  simp only [ScopeOpcode,List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with h | h | h | h | h
  · have equal : opcode = 2#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_block_code_mono_wasm2 p ops law before after out ctx byte accepted
  · have equal : opcode = 3#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_loop_code_mono_wasm2 p ops law before after out ctx byte accepted
  · have equal : opcode = 4#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_if_code_mono_wasm2 p ops law before after out ctx byte accepted
  · have equal : opcode = 12#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_br_code_mono_wasm2 p ops law before after out ctx byte accepted
  · have equal : opcode = 13#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_br_if_code_mono_wasm2 p ops law before after out ctx byte accepted
end Exec.Code
