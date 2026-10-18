import Exec.Code.Local.Relations.Calls.IndirectCallOperands
import Exec.Code.Local.Relations.Calls.IndirectCallEmission
import Exec.Code.Body.Relations.Calls.IndirectCallSignature
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Successful indirect-call lowering appends the exact table/type pair and
emits the source-determined selector and argument coordinates. -/
theorem compiler_indirect_call_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (C : context) (front params results : List valtype) (typeIndex tableIndex : U32)
    (bounds : limits) (signature : runtime.compiler.Signature)
    (signatureFound : C.TYPES[typeIndex.val]? = some ⟨.mk_list params,.mk_list results⟩)
    (tableFound : C.TABLES[tableIndex.val]? = some (.mk_tabletype bounds .FUNCREF))
    (read : Slice.index_usize before.signatures (UScalar.cast .Usize typeIndex) = .ok signature)
    (parameterWidth : signature.param_slots.val = slots params)
    (locals : C.LOCALS = compilerLocals before)
    (layout : CompilerLayout before ((front ++ params) ++ [.I32]))
    (reachable : before.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ results)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 typeIndex tableIndex 0#u128 = .ok (.Ok (),after)) :
    after.function.indirect.val = before.function.indirect.val ++ [(tableIndex,typeIndex)] ∧
    ∃ instruction, Lowered before after instruction (front ++ results) ∧
      IndirectCallEmission after.function.indirect.val C ((front ++ params) ++ [.I32])
        (.CALL_INDIRECT (.mk_uN tableIndex.val) (.mk_uN typeIndex.val)) [instruction] (front ++ results) := by
  obtain ⟨total,base,added,subtracted,basePosition⟩ := indirect_call_arithmetic before front params signature layout parameterWidth
  obtain ⟨entry,paired,pairRun⟩ := lower_indirect_call_pair_success ops before after state typeIndex tableIndex total base
    signature reachable read added subtracted accepted
  obtain ⟨budget,pairs,pairedEq,pairsEq,indexEq⟩ := compiler_pair_success ops law before paired tableIndex typeIndex entry pairRun
  subst paired
  let paired := {before with budget, function := {before.function with indirect := pairs}}
  have pairedLayout : CompilerLayout paired ((front ++ params) ++ [.I32]) :=
    ⟨layout.localSlots,layout.localOffsets,layout.operandOffsets,layout.height,layout.capacity⟩
  obtain ⟨index,operand,indexPosition⟩ := indirect_call_operand ops paired front params pairedLayout
  rw [lower_indirect_call_eq ops before paired state typeIndex tableIndex total base entry index signature
    reachable read added subtracted pairRun operand] at accepted
  have lowered := finish_op ops law paired state types (.CallIndirect entry index base)
    _ pairedLayout concrete codeFits sourceFits coordinateFits
  rw [accepted,WP.spec_ok] at lowered
  have kept := compiler_finish_indirect ops law paired after state _ accepted
  have afterPairs : after.function.indirect.val = before.function.indirect.val ++ [(tableIndex,typeIndex)] := by
    rw [kept]; exact pairsEq
  refine ⟨afterPairs,.CallIndirect entry index base,?_,?_⟩
  · simpa only [typed,Lowered,paired,compilerLocals] using lowered rfl
  · apply IndirectCallEmission.call front params results typeIndex tableIndex entry index base bounds
      signatureFound tableFound
    · rw [afterPairs,indexEq]; simp
    · simpa only [locals] using basePosition
    · simp only [paired,compilerLocals] at indexPosition basePosition
      omega
/-- The public compiler-side constructor reads signature metadata from the actual
captured source sequence, rather than assuming a width or a successful lookup. -/
theorem compiler_indirect_call_emission_captured {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (sourceTypes : List Itasca.types.FuncType) (sequence : SignatureSequence before.signatures.val sourceTypes)
    (C : context) (contextTypes : C.TYPES = sourceTypes.map Itasca.EnvTranslation.funcType)
    (front params results : List valtype) (typeIndex tableIndex : U32) (bounds : limits)
    (signatureFound : C.TYPES[typeIndex.val]? = some ⟨.mk_list params,.mk_list results⟩)
    (tableFound : C.TABLES[tableIndex.val]? = some (.mk_tabletype bounds .FUNCREF))
    (locals : C.LOCALS = compilerLocals before)
    (layout : CompilerLayout before ((front ++ params) ++ [.I32]))
    (reachable : before.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ results)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 typeIndex tableIndex 0#u128 = .ok (.Ok (),after)) :
    after.function.indirect.val = before.function.indirect.val ++ [(tableIndex,typeIndex)] ∧
    ∃ instruction, Lowered before after instruction (front ++ results) ∧
      IndirectCallEmission after.function.indirect.val C ((front ++ params) ++ [.I32])
        (.CALL_INDIRECT (.mk_uN tableIndex.val) (.mk_uN typeIndex.val)) [instruction] (front ++ results) := by
  obtain ⟨signature,read,matched⟩ := sequence.indirect_call typeIndex params results (by simpa only [contextTypes] using signatureFound)
  exact compiler_indirect_call_emission ops law before after state types C front params results typeIndex tableIndex bounds
    signature signatureFound tableFound read matched.paramWords locals layout reachable concrete typed
    codeFits sourceFits coordinateFits accepted
end Exec.Code
