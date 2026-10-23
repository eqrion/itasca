import Exec.Code.Local.Callbacks.Calls.CallbackCapacity
import Exec.Code.Local.Capacity.CapacityTactic
import Exec.Code.Local.Capacity.LiteralCapacity
import Exec.Code.Local.Lowering.Common.LiteralSources
import Exec.Code.Local.Source.SourceLengthsTactic
import Exec.Code.Local.Lowering.Common.LoweringArithmetic
import Exec.Code.Local.Lowering.Local.LoweringLocal
import Exec.Code.Local.Lowering.Common.LiteralCursor
import Exec.Code.Local.Source.SourceCursorTactic
import Exec.Code.Body.Source.TypedLowering
import Exec.Code.Local.Callbacks.Common.CompilerLiteralMetadata
import Exec.Code.Local.Callbacks.Common.CompilerMetadataTactic
import Exec.Code.Body.Reader.Common.ReaderEmissions
import Exec.Code.Body.Reader.Control.ReaderReturn
import Exec.Code.Local.Relations.Common.ReaderOpcode
import Exec.Code.Local.Callbacks.Control.ControlEffects

/-!
Every successful structured-control reader step is one control compiler
callback with `ControlEffects`.
-/

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_block_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 2#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_block] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_block_effects ops law before after out.core value called

theorem reader_loop_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 3#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_loop] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_loop_effects ops law before after out.core value called

theorem reader_if_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 4#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_if] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_if_effects ops law before after out.core value called

theorem reader_else_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 5#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_else] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_else_effects ops law before after out.core value.2 called

theorem reader_end_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 11#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_end] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_end_effects ops law before after out.core value.1 value.2 called

theorem reader_br_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 12#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_br] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_br_effects ops law before after out.core value.1 value.2 called

theorem reader_br_if_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 13#u8 before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rw [Wasm2.CallbackTrace.dispatch_br_if] at accepted
  obtain ⟨value, _, called⟩ := reader_body_success _ _ _ _ _ _ accepted
  exact compiler_br_if_effects ops law before after out.core value.1 value.2 called

theorem reader_control_effects_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (opcode : U8) (control : ScopeOpcode opcode ∨ opcode = 5#u8 ∨ opcode = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (), out, after)) :
    ControlEffects before after out.core := by
  rcases control with scope | rfl | rfl
  · simp only [ScopeOpcode, List.mem_cons, List.not_mem_nil, or_false] at scope
    rcases scope with h | h | h | h | h
    · obtain rfl : opcode = 2#u8 := (UScalar.eq_equiv _ _).mpr h
      exact reader_block_effects_wasm2 ops law before after st out data env ctx index accepted
    · obtain rfl : opcode = 3#u8 := (UScalar.eq_equiv _ _).mpr h
      exact reader_loop_effects_wasm2 ops law before after st out data env ctx index accepted
    · obtain rfl : opcode = 4#u8 := (UScalar.eq_equiv _ _).mpr h
      exact reader_if_effects_wasm2 ops law before after st out data env ctx index accepted
    · obtain rfl : opcode = 12#u8 := (UScalar.eq_equiv _ _).mpr h
      exact reader_br_effects_wasm2 ops law before after st out data env ctx index accepted
    · obtain rfl : opcode = 13#u8 := (UScalar.eq_equiv _ _).mpr h
      exact reader_br_if_effects_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_else_effects_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_end_effects_wasm2 ops law before after st out data env ctx index accepted
end Exec.Code
