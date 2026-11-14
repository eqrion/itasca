import Itasca.Runtime.SourceMachine.Stateful.Signature
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulSuccess
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Local.Capacity.ControlCapacity

/-!
Sections, each formerly its own module: StatefulEmission, StatefulEmissionTransport, StatefulEffects, StatefulOperands, StatefulLowered.
-/

/-! ## StatefulEmission -/

section

/-!
Reference and bulk instructions retain their exact function-local pair table. This is syntactic compiler evidence, independent of execution correctness.

Main declarations: `StatefulEmission`. A direct consumer is `Compiler.Local.Relations.Calls.IndirectCallExclusions`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Reference and bulk instructions retain their exact function-local pair table.
This is syntactic compiler evidence, independent of execution correctness. -/
inductive StatefulEmission (pairs : List (U32 × U32)) (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | instruction (stack input output) (op : SourceMachine.Stateful.Instruction)
      (signature : SourceMachine.Stateful.Signature C op input output)
      (first second a b entry : U32)
      (firstSlot : first.val = slots C.LOCALS + slots stack)
      (secondSlot : op.arity ≥ 2 → second.val = first.val + 1)
      (arguments : StatefulArguments op a b)
      (pair : StatefulPair pairs op a b entry) :
      StatefulEmission pairs C (stack ++ input) op.source
        [statefulInstruction op first second a entry] (stack ++ output)

end Itasca.Runtime.Compiler

end

/-! ## StatefulEmissionTransport -/

section

/-!
Transport of stateful emission across compiler index-pair tables.

Main declarations: `StatefulEmission.map_pairs`. A direct consumer is `Compiler.Body.Control.Control.CumulativePointControl`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem StatefulEmission.map_pairs {beforePairs afterPairs C before instruction emitted after}
    (preserve : ∀ (index : Nat) (pair : U32 × U32), beforePairs[index]? = some pair → afterPairs[index]? = some pair)
    (head : StatefulEmission beforePairs C before instruction emitted after) :
    StatefulEmission afterPairs C before instruction emitted after := by
  cases head with
  | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
    refine .instruction stack input output op signature first second a b entry firstSlot secondSlot arguments ?_
    cases op <;> simp only [StatefulPair] at pair ⊢ <;> try trivial
    all_goals exact preserve _ _ pair

end Itasca.Runtime.Compiler

end

/-! ## StatefulEffects -/

section

/-!
Metadata, source-offset and capacity effects of stateful lowering.

Main declarations: `compiler_stateful_ordinary_result` and `compiler_stateful_capacity`. A direct consumer is `Compiler.Local.Publication.LoweringMapPublication`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std SourceMachine.Stateful
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
theorem compiler_stateful_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Instruction) (a b : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · rw [lower_stateful_dispatch ops before state op a b reach] at accepted
    cases op <;> simp only [statefulLowering] at accepted
    all_goals repeat' metadata_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_stateful_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Instruction) (a b : U32)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (.Ok (), after)) :
    SourceProgress before after := by
  by_cases reach : before.reachable = true
  · rw [lower_stateful_dispatch ops before state op a b reach] at accepted
    cases op <;> simp only [statefulLowering] at accepted
    all_goals repeat' sources_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_sources ops law before after state (.Ok ()) accepted

theorem compiler_stateful_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Instruction) (a b : U32)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  by_cases reach : before.reachable = true
  · rw [lower_stateful_dispatch ops before state op a b reach] at accepted
    cases op <;> simp only [statefulLowering] at accepted
    all_goals repeat' cursor_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_cursor ops law before after state (.Ok ()) accepted rfl

theorem compiler_stateful_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Instruction) (a b : U32)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (statefulOpcode op) a b 0#u128 = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  by_cases reach : before.reachable = true
  · rw [lower_stateful_dispatch ops before state op a b reach] at accepted
    cases op <;> simp only [statefulLowering] at accepted
    all_goals repeat' capacity_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact ⟨(compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).1,
      (compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).2 rfl⟩

end Itasca.Runtime.Compiler

end

/-! ## StatefulOperands -/

section

/-!
Actual compiler operand reads and coordinates follow from the source signature and full stack layout, including reference values.

Main declarations: `stateful_operands`. A direct consumer is `Compiler.Local.Relations.Stateful.StatefulLowered`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

private theorem first_suffix_operand {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (front input : List valtype)
    (layout : CompilerLayout compiler (front ++ input)) (depth : Usize)
    (positive : 0 < depth.val) (count : depth.val = input.length) :
    ∃ first : U32, runtime.compiler.FunctionCompiler.operand ops compiler depth = .ok (.Ok first) ∧
      first.val = slots (compilerLocals compiler) + slots front := by
  obtain ⟨r,read,first,rfl,position⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout depth positive (by simp [count]))
  refine ⟨first,read,?_⟩
  simpa [offset,List.length_append,count] using position

private theorem next_suffix_operand {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (front input : List valtype)
    (layout : CompilerLayout compiler (front ++ input)) (depth : Usize)
    (positive : 0 < depth.val) (count : depth.val + 1 = input.length)
    (scalar : ∀ type ∈ input, type ≠ valtype.V128) :
    ∃ second : U32, runtime.compiler.FunctionCompiler.operand ops compiler depth = .ok (.Ok second) ∧
      second.val = slots (compilerLocals compiler) + slots front + 1 := by
  obtain ⟨r,read,second,rfl,position⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout depth positive (by simp only [List.length_append]; omega))
  have index : (front ++ input).length - depth.val = front.length + 1 := by
    simp only [List.length_append]; omega
  have takeFront : front.take (front.length + 1) = front := List.take_of_length_le (by omega)
  have firstWidth : slots (input.take 1) = 1 := by
    cases input with
    | nil => simp at count
    | cons head tail =>
      have nonvector := scalar head (by simp)
      cases head <;> simp_all [slots,width]
  refine ⟨second,read,?_⟩
  rw [index] at position
  simpa [offset,List.take_append,takeFront,slots_append,firstWidth,Nat.add_assoc] using position

/-- Actual compiler operand reads and coordinates follow from the source
signature and full stack layout, including reference values. -/
theorem stateful_operands {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (C : context)
    (front input output : List valtype) (op : SourceMachine.Stateful.Instruction)
    (signature : SourceMachine.Stateful.Signature C op input output)
    (layout : CompilerLayout compiler (front ++ input)) :
    ∃ first second : U32, StatefulReads ops compiler op first second ∧
      first.val = slots (compilerLocals compiler) + slots front ∧
      (op.arity ≥ 2 → second.val = first.val + 1) := by
  have count := signature.input_length
  have bound := op.arity_le_three
  have alternatives : op.arity = 0 ∨ op.arity = 1 ∨ op.arity = 2 ∨ op.arity = 3 := by omega
  rcases alternatives with zero | one | two | three
  · have empty : input = [] := List.length_eq_zero_iff.mp (count.trans zero)
    refine ⟨compiler.height,compiler.height,⟨?_,?_⟩,?_,?_⟩
    · simp [StatefulReads,zero]
    · intro table same
      have impossible := congrArg SourceMachine.Stateful.Instruction.arity same
      change op.arity = 2 at impossible
      omega
    · simpa [empty] using layout.height
    · omega
  · obtain ⟨first,read,position⟩ := first_suffix_operand ops compiler front input layout 1#usize (by decide) (by simpa [one] using count.symm)
    refine ⟨first,first,⟨?_,?_⟩,position,?_⟩
    · simpa [one,statefulDepth] using read
    · intro table same
      have impossible := congrArg SourceMachine.Stateful.Instruction.arity same
      change op.arity = 2 at impossible
      omega
    · omega
  · obtain ⟨first,read,position⟩ := first_suffix_operand ops compiler front input layout 2#usize (by decide) (by simpa [two] using count.symm)
    obtain ⟨second,readSecond,secondPosition⟩ := next_suffix_operand ops compiler front input layout 1#usize (by decide)
      (by simpa [two] using count.symm) signature.inputs_scalar
    refine ⟨first,second,⟨?_,?_⟩,position,?_⟩
    · simpa [two,statefulDepth] using read
    · intro table same; exact readSecond
    · intro _; omega
  · obtain ⟨first,read,position⟩ := first_suffix_operand ops compiler front input layout 3#usize (by decide) (by simpa [three] using count.symm)
    obtain ⟨second,readSecond,secondPosition⟩ := next_suffix_operand ops compiler front input layout 2#usize (by decide)
      (by simpa [three] using count.symm) signature.inputs_scalar
    refine ⟨first,second,⟨?_,?_⟩,position,?_⟩
    · simpa [three,statefulDepth] using read
    · intro table same
      have impossible := congrArg SourceMachine.Stateful.Instruction.arity same
      change op.arity = 2 at impossible
      omega
    · intro _; omega

end Itasca.Runtime.Compiler

end

/-! ## StatefulLowered -/

section

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

end
