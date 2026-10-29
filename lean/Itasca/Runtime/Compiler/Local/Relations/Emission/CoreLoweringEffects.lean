import Itasca.Runtime.Compiler.Local.Relations.Select.SelectLowering
import Itasca.Runtime.Compiler.Local.Relations.Global.GlobalLowering
import Itasca.Runtime.Compiler.Local.Relations.Memory.MemoryEmission
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadataTactic
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Local.Capacity.CapacityTactic

/-!
Discriminates actual scalar mutable callbacks and their binary immediates.

Main declarations: `CoreOperation` and `CoreOperation.opcode`. A direct consumer is `Compiler.Body.Reader.Checking.OperationInstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Discriminates actual scalar mutable callbacks and their binary immediates. -/
inductive CoreOperation where
  | select (typed : Bool)
  | globalGet (index : U32)
  | globalSet (index : U32)
  | load (operation : SourceMachine.Memory.Load) (offset alignment : U32)
  | store (operation : SourceMachine.Memory.Store) (offset alignment : U32)

def CoreOperation.opcode : CoreOperation → U16
  | .select typed => if typed then 28#u16 else 27#u16
  | .globalGet _ => 35#u16
  | .globalSet _ => 36#u16
  | .load op _ _ => memoryLoadOpcode op
  | .store op _ _ => memoryStoreOpcode op

def CoreOperation.first : CoreOperation → U32
  | .select _ => 0#u32
  | .globalGet index | .globalSet index => index
  | .load _ offset _ | .store _ offset _ => offset

def CoreOperation.second : CoreOperation → U32
  | .load _ _ alignment | .store _ _ alignment => alignment
  | _ => 0#u32

noncomputable def coreLowering {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) :
    CoreOperation → Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A)
  | .select _ => selectLowering ops compiler state
  | .globalGet index => globalGetLowering ops compiler state index
  | .globalSet index => globalSetLowering ops compiler state index
  | .load op offset _ => memoryLoadLowering ops compiler state op offset
  | .store op offset _ => memoryStoreLowering ops compiler state op offset

theorem lower_core_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : CoreOperation) (reachable : compiler.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state op.opcode op.first op.second 0#u128 =
      coreLowering ops compiler state op := by
  cases op with
  | select typed =>
    cases typed <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos reachable] <;> rfl
  | globalGet index => unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl
  | globalSet index => unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl
  | load op offset alignment => exact lower_memory_load_dispatch ops compiler state op offset alignment reachable
  | store op offset alignment => exact lower_memory_store_dispatch ops compiler state op offset alignment reachable

theorem compiler_core_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : CoreOperation)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state op.opcode op.first op.second 0#u128 = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · rw [lower_core_dispatch ops before state op reach] at accepted
    cases op <;> unfold coreLowering at accepted
    all_goals simp only [selectLowering, globalGetLowering, globalSetLowering,
      memoryLoadLowering, memoryStoreLowering] at accepted
    all_goals repeat' metadata_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_core_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : CoreOperation)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state op.opcode op.first op.second 0#u128 = .ok ((.Ok ()), after)) :
    SourceProgress before after := by
  by_cases reach : before.reachable = true
  · rw [lower_core_dispatch ops before state op reach] at accepted
    cases op <;> unfold coreLowering at accepted
    all_goals simp only [selectLowering, globalGetLowering, globalSetLowering,
      memoryLoadLowering, memoryStoreLowering] at accepted
    all_goals repeat' sources_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_sources ops law before after state (.Ok ()) accepted

theorem compiler_core_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : CoreOperation)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state op.opcode op.first op.second 0#u128 = .ok ((.Ok ()), after)) :
    after.next_source = state.pos := by
  by_cases reach : before.reachable = true
  · rw [lower_core_dispatch ops before state op reach] at accepted
    cases op <;> unfold coreLowering at accepted
    all_goals simp only [selectLowering, globalGetLowering, globalSetLowering,
      memoryLoadLowering, memoryStoreLowering] at accepted
    all_goals repeat' cursor_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_cursor ops law before after state (.Ok ()) accepted rfl

theorem compiler_core_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : CoreOperation)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state op.opcode op.first op.second 0#u128 = .ok ((.Ok ()), after)) :
    CapacityStep before after state := by
  by_cases reach : before.reachable = true
  · rw [lower_core_dispatch ops before state op reach] at accepted
    cases op <;> unfold coreLowering at accepted
    all_goals simp only [selectLowering, globalGetLowering, globalSetLowering,
      memoryLoadLowering, memoryStoreLowering] at accepted
    all_goals repeat' capacity_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact ⟨(compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).1,
      (compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).2 rfl⟩
end Itasca.Runtime.Compiler
