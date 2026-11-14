import Itasca.Runtime.Compiler.Local.Relations.Function.EnvironmentContracts
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEnvironment
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulSuccess
import Itasca.Runtime.Compiler.Local.Relations.Calls.StatefulCallbacks

/-!
Sections, each formerly its own module: SignatureTable, StatefulAuxiliaryTables.
-/

/-! ## SignatureTable -/

section

/-! The actual scheduler loop constructs a source-aligned signature table
from every module type, retaining exact value and word arities. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem SignatureSequence.lookup {signatures types}
    (sequence : SignatureSequence signatures types) {index : Nat} {signature : runtime.compiler.Signature}
    (found : signatures[index]? = some signature) :
    ∃ ty : Itasca.wasm_types.FuncType, types[index]? = some ty ∧ SignatureMatches signature
      (ty.params.val.map Itasca.Translate.valueType) (ty.results.val.map Itasca.Translate.valueType) := by
  induction sequence generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst signature
              exact ⟨_, rfl, head⟩
    | succ index => exact ih (by simpa using found)

theorem SignatureSequence.table {signatures : Slice runtime.compiler.Signature}
    {types : List Itasca.wasm_types.FuncType} (sequence : SignatureSequence signatures.val types) :
    SignatureTable signatures (types.map Itasca.EnvTranslation.funcType) := by
  intro index signature found
  obtain ⟨ty, lookup, matched⟩ := SignatureSequence.lookup sequence found
  refine ⟨_, _, ?_, matched⟩
  simp [List.getElem?_map, lookup, Itasca.EnvTranslation.funcType]

@[step] theorem capture_signatures_loop_frame {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (index : Usize) (status : core.result.Result Unit Itasca.error.Error)
    (bound : index.val ≤ env.types.val.length)
    (prefixMatches : status = .Ok () → SignatureSequence scheduler.signatures.val (env.types.val.take index.val)) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
      ops scheduler env index status ⦃ out =>
      out.2.2.2.2.2.2.2 = .Ok () → SignatureSequence out.1.val env.types.val ∧
        out.2.1 = scheduler.func_param_slots ∧ out.2.2.2.1 = scheduler.functions ⦄ := by
  exact runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.total ops law scheduler env index status bound prefixMatches

end Itasca.Runtime.Compiler

end

/-! ## StatefulAuxiliaryTables -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
theorem compiler_stateful_auxiliary_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Stateful.Instruction) (a b : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (status, after)) :
    compilerAuxiliaryTables after.function = compilerAuxiliaryTables before.function := by
  by_cases reach : before.reachable = true
  · rw [lower_stateful_dispatch ops before state op a b reach] at accepted
    cases op <;> simp only [statefulLowering] at accepted
    all_goals repeat' auxiliary_tables_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    have tables := compiler_observe_tables ops law before after state status accepted
    simpa only [CompilerTables.ofFunction, CompilerTables.mk.injEq, compilerAuxiliaryTables] using
      congrArg (fun t : CompilerTables => (t.simd,t.constants,t.jumpTables)) tables
theorem compiler_indirect_call_auxiliary_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 = .ok (status, after)) :
    compilerAuxiliaryTables after.function = compilerAuxiliaryTables before.function := by
  by_cases reach : before.reachable = true
  · rw [lower_indirect_call_dispatch ops before state a b reach] at accepted
    unfold indirectCallLowering at accepted
    repeat' auxiliary_tables_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    have tables := compiler_observe_tables ops law before after state status accepted
    simpa only [CompilerTables.ofFunction, CompilerTables.mk.injEq, compilerAuxiliaryTables] using
      congrArg (fun t : CompilerTables => (t.simd,t.constants,t.jumpTables)) tables
end Itasca.Runtime.Compiler

end
