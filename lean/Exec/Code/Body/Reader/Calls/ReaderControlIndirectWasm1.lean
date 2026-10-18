import Exec.Code.Local.Callbacks.Calls.CallbackIndirect
import Exec.Code.Body.Reader.Common.ReaderEnterWasm1
import Exec.Code.Body.Reader.Control.ReaderBranchWasm1
import Exec.Code.Body.Reader.Common.ReaderCloseWasm1
import Exec.Code.Body.Reader.Control.ReaderCompilerScopes
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_block_indirect_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 2#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 2#u8 before = .ok (.Ok (),out,after)) :
    after.function.indirect = before.function.indirect := by
  obtain ⟨bt,callback,_,_⟩ := reader_block_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  exact compiler_block_indirect ops law before after out (Control.signature bt) callback

theorem reader_loop_indirect_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 3#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 3#u8 before = .ok (.Ok (),out,after)) :
    after.function.indirect = before.function.indirect := by
  obtain ⟨bt,callback,_,_⟩ := reader_loop_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  exact compiler_loop_indirect ops law before after out (Control.signature bt) callback

theorem reader_if_indirect_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 4#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 4#u8 before = .ok (.Ok (),out,after)) :
    after.function.indirect = before.function.indirect := by
  obtain ⟨bt,remaining,callback,_,_⟩ := reader_if_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  exact compiler_if_indirect ops law before after out (Control.signature bt) callback

theorem reader_br_indirect_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 12#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 12#u8 before = .ok (.Ok (),out,after)) :
    after.function.indirect = before.function.indirect := by
  obtain ⟨depth,view,callback,_,_⟩ := reader_br_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  exact compiler_br_indirect ops law before after out depth (Control.resultView view) callback

theorem reader_br_if_indirect_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 13#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 13#u8 before = .ok (.Ok (),out,after)) :
    after.function.indirect = before.function.indirect := by
  obtain ⟨depth,view,values,callback,_,_⟩ := reader_br_if_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  exact compiler_br_if_indirect ops law before after out depth (Control.resultView view) callback

theorem reader_else_indirect_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 5#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 5#u8 before = .ok (.Ok (),out,after)) :
    after.function.indirect = before.function.indirect := by
  have callback := (reader_else_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)).1
  exact compiler_else_indirect ops law before after out (Control.signature p.current.ctrl.block_type) callback

theorem reader_end_indirect_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 11#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 11#u8 before = .ok (.Ok (),out,after)) :
    after.function.indirect = before.function.indirect := by
  have callback := (reader_end_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)).1
  exact compiler_end_indirect ops law before after out p.current.ctrl.kind (Control.signature p.current.ctrl.block_type) callback

theorem reader_scope_indirect_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (opcode : U8) (supported : ScopeOpcode opcode)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode before = .ok (.Ok (),out,after)) :
    after.function.indirect = before.function.indirect := by
  simp only [ScopeOpcode,List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with h | h | h | h | h
  · have equal : opcode = 2#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_block_indirect_wasm1 p ops law before after out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  · have equal : opcode = 3#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_loop_indirect_wasm1 p ops law before after out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  · have equal : opcode = 4#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_if_indirect_wasm1 p ops law before after out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  · have equal : opcode = 12#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_br_indirect_wasm1 p ops law before after out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  · have equal : opcode = 13#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_br_if_indirect_wasm1 p ops law before after out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
end Exec.Code
