import Exec.Code.Local.Capacity.AuxiliaryGrowth
import Exec.Code.Body.Reader.Table.ReaderControlTables
import Exec.Code.Body.Reader.Table.ReaderControlTablesWasm1
import Exec.Code.Body.Reader.Control.ReaderControlCodeMonotone
import Exec.Code.Body.Reader.Control.ReaderControlCodeMonotoneWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem reader_block_auxiliary_growth_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 2#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 2#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_block_tables_wasm1 p ops law before after out byte accepted)
    (reader_block_code_mono_wasm1 p ops law before after out byte accepted)

theorem reader_loop_auxiliary_growth_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 3#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 3#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_loop_tables_wasm1 p ops law before after out byte accepted)
    (reader_loop_code_mono_wasm1 p ops law before after out byte accepted)

theorem reader_if_auxiliary_growth_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 4#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 4#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_if_tables_wasm1 p ops law before after out byte accepted)
    (reader_if_code_mono_wasm1 p ops law before after out byte accepted)

theorem reader_br_auxiliary_growth_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 12#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 12#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_br_tables_wasm1 p ops law before after out byte accepted)
    (reader_br_code_mono_wasm1 p ops law before after out byte accepted)

theorem reader_br_if_auxiliary_growth_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 13#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 13#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_br_if_tables_wasm1 p ops law before after out byte accepted)
    (reader_br_if_code_mono_wasm1 p ops law before after out byte accepted)

theorem reader_else_auxiliary_growth_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 5#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 5#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_else_tables_wasm1 p ops law before after out byte accepted)
    (reader_else_code_mono_wasm1 p ops law before after out byte accepted)

theorem reader_end_auxiliary_growth_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (byte : data.val[p.start.val]'p.inbounds = 11#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx 11#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_end_tables_wasm1 p ops law before after out byte accepted)
    (reader_end_code_mono_wasm1 p ops law before after out byte accepted)

theorem reader_scope_auxiliary_growth_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (opcode : U8) (supported : ScopeOpcode opcode)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_scope_tables_wasm1 p ops law before after out opcode supported byte accepted)
    (reader_scope_code_mono_wasm1 p ops law before after out opcode supported byte accepted)

theorem reader_block_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 2#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 2#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_block_tables_wasm2 p ops law before after out ctx byte accepted)
    (reader_block_code_mono_wasm2 p ops law before after out ctx byte accepted)

theorem reader_loop_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 3#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 3#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_loop_tables_wasm2 p ops law before after out ctx byte accepted)
    (reader_loop_code_mono_wasm2 p ops law before after out ctx byte accepted)

theorem reader_if_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 4#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 4#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_if_tables_wasm2 p ops law before after out ctx byte accepted)
    (reader_if_code_mono_wasm2 p ops law before after out ctx byte accepted)

theorem reader_br_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 12#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 12#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_br_tables_wasm2 p ops law before after out ctx byte accepted)
    (reader_br_code_mono_wasm2 p ops law before after out ctx byte accepted)

theorem reader_br_if_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 13#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 13#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_br_if_tables_wasm2 p ops law before after out ctx byte accepted)
    (reader_br_if_code_mono_wasm2 p ops law before after out ctx byte accepted)

theorem reader_else_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 5#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 5#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_else_tables_wasm2 p ops law before after out ctx byte accepted)
    (reader_else_code_mono_wasm2 p ops law before after out ctx byte accepted)

theorem reader_end_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_end_tables_wasm2 p ops law before after out ctx byte accepted)
    (reader_end_code_mono_wasm2 p ops law before after out ctx byte accepted)

theorem reader_scope_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (opcode : U8) (supported : ScopeOpcode opcode)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after :=
  .of_tables (reader_scope_tables_wasm2 p ops law before after out ctx opcode supported byte accepted)
    (reader_scope_code_mono_wasm2 p ops law before after out ctx opcode supported byte accepted)

end Exec.Code
