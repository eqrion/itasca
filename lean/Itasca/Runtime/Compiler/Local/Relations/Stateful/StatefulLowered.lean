import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulOperands
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulSuccess

/-!
Actual accepted non-pair callbacks produce their source-indexed emission.

Main declarations: `compiler_stateful_single_emission` and `compiler_stateful_emission`. A direct consumer is `Compiler.Body.Control.Closing.IndexedAdvanceOrClosed`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual accepted non-pair callbacks produce their source-indexed emission. -/
theorem compiler_stateful_single_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (C : context) (front input output : List valtype) (op : SourceMachine.Stateful.Instruction) (a b : U32)
    (signature : SourceMachine.Stateful.Signature C op input output)
    (locals : C.LOCALS = compilerLocals before) (arguments : StatefulArguments op a b)
    (layout : CompilerLayout before (front ++ input)) (reachable : before.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ output)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (single : statefulUsesPair op = false)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after))
    (pairs : List (U32 × U32) := after.function.indirect.val) :
    after.function.indirect = before.function.indirect ∧ ∃ instruction,
      Lowered before after instruction (front ++ output) ∧
      StatefulEmission pairs C (front ++ input) op.source [instruction] (front ++ output) := by
  obtain ⟨first,second,reads,position,secondPosition⟩ := stateful_operands ops before C front input output op signature layout
  rw [lower_stateful_eq ops before state op first second a b 0#u32 reachable single reads] at accepted
  have lowered := finish_op ops law before state types (statefulInstruction op first second a 0#u32)
    _ layout concrete codeFits sourceFits coordinateFits
  rw [accepted,WP.spec_ok] at lowered
  refine ⟨compiler_finish_indirect ops law before after state _ accepted,statefulInstruction op first second a 0#u32,?_,?_⟩
  · simpa only [typed] using lowered rfl
  · apply StatefulEmission.instruction front input output op signature first second a b 0#u32
      (by simpa only [locals] using position) secondPosition arguments
    cases op <;> simp_all [statefulUsesPair,StatefulPair]

/-- Pair callbacks append exactly their supplied indices and then emit using
the returned table entry; layout and code evidence refer to the original state. -/
theorem compiler_stateful_pair_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (C : context) (front input output : List valtype) (op : SourceMachine.Stateful.Instruction) (a b : U32)
    (signature : SourceMachine.Stateful.Signature C op input output)
    (locals : C.LOCALS = compilerLocals before) (arguments : StatefulArguments op a b)
    (layout : CompilerLayout before (front ++ input)) (reachable : before.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ output)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (pairOpcode : statefulUsesPair op = true)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after)) :
    after.function.indirect.val = before.function.indirect.val ++ [(a,b)] ∧ ∃ instruction,
      Lowered before after instruction (front ++ output) ∧
      StatefulEmission after.function.indirect.val C (front ++ input) op.source [instruction] (front ++ output) := by
  obtain ⟨entry,paired,pairRun⟩ := lower_stateful_pair_success ops before after state op a b reachable pairOpcode accepted
  obtain ⟨budget,pairs,pairedEq,pairsEq,indexEq⟩ := compiler_pair_success ops law before paired a b entry pairRun
  subst paired
  let paired := {before with budget, function := {before.function with indirect := pairs}}
  have pairedLayout : CompilerLayout paired (front ++ input) :=
    ⟨layout.localSlots,layout.localOffsets,layout.operandOffsets,layout.height,layout.capacity⟩
  obtain ⟨first,second,reads,position,secondPosition⟩ := stateful_operands ops paired C front input output op signature pairedLayout
  have arity : op.arity = 3 := by cases op <;> simp_all [statefulUsesPair,SourceMachine.Stateful.Instruction.arity]
  have read : runtime.compiler.FunctionCompiler.operand ops paired 3#usize = .ok (.Ok first) := by
    simpa [statefulDepth,arity] using reads.1
  rw [lower_stateful_pair_eq ops before paired state op first second a b entry reachable pairOpcode pairRun read] at accepted
  have lowered := finish_op ops law paired state types (statefulInstruction op first second a entry)
    _ pairedLayout concrete codeFits sourceFits coordinateFits
  rw [accepted,WP.spec_ok] at lowered
  have kept := compiler_finish_indirect ops law paired after state _ accepted
  have afterPairs : after.function.indirect.val = before.function.indirect.val ++ [(a,b)] := by
    rw [kept]; exact pairsEq
  refine ⟨afterPairs,statefulInstruction op first second a entry,?_,?_⟩
  · simpa only [typed,Lowered,paired,compilerLocals] using lowered rfl
  · apply StatefulEmission.instruction front input output op signature first second a b entry
      (by simpa only [locals,paired,compilerLocals] using position) secondPosition arguments
    have lookup : after.function.indirect.val[entry.val]? = some (a,b) := by
      rw [afterPairs,indexEq]
      simp
    cases op <;> simp_all [statefulUsesPair,StatefulPair]

theorem compiler_stateful_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (C : context) (front input output : List valtype) (op : SourceMachine.Stateful.Instruction) (a b : U32)
    (signature : SourceMachine.Stateful.Signature C op input output)
    (locals : C.LOCALS = compilerLocals before) (arguments : StatefulArguments op a b)
    (layout : CompilerLayout before (front ++ input)) (reachable : before.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ output)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after)) :
    (∃ extra, after.function.indirect.val = before.function.indirect.val ++ extra) ∧ ∃ instruction,
      Lowered before after instruction (front ++ output) ∧
      StatefulEmission after.function.indirect.val C (front ++ input) op.source [instruction] (front ++ output) := by
  by_cases pairOpcode : statefulUsesPair op = true
  · obtain ⟨pairs,emission⟩ := compiler_stateful_pair_emission ops law before after state types C front input output op a b
      signature locals arguments layout reachable concrete typed codeFits sourceFits coordinateFits pairOpcode accepted
    exact ⟨⟨[(a,b)],pairs⟩,emission⟩
  · have single : statefulUsesPair op = false := Bool.eq_false_iff.mpr pairOpcode
    obtain ⟨pairs,emission⟩ := compiler_stateful_single_emission ops law before after state types C front input output op a b
      signature locals arguments layout reachable concrete typed codeFits sourceFits coordinateFits single accepted
    exact ⟨⟨[],by simp [pairs]⟩,emission⟩

end Itasca.Runtime.Compiler
