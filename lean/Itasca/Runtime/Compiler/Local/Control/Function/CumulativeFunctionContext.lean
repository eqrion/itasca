import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredFunction
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunctionContext
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered

/-!
Sections, each formerly its own module: IndexedFunctionAssembly, IndexedFunction, CumulativeFunctionContext.
-/

/-! ## IndexedFunctionAssembly -/

section

/-!
Finishing the actual compiler assembles the retained function certificate. The body relation and epilogue come from the completed source prefix; fixed signature/local metadata is transported from the function-start callback.

Main declarations: `indexed_compiler_finish_certificate`. A direct consumer is `Compiler.Body.Reader.Replay.IndexedCompilerFinish`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Finishing the actual compiler assembles the retained function certificate.
The body relation and epilogue come from the completed source prefix; fixed
signature/local metadata is transported from the function-start callback. -/
theorem indexed_compiler_finish_certificate {A : Type} (ops : runtime.platform.Alloc A)
    (initial final : runtime.compiler.FunctionCompiler A)
    (validated : core.result.Result Unit Itasca.error.Error)
    (compiled : runtime.bytecode.CompiledFunction) (budget : runtime.compiler.Budget A)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (params declared results : List valtype)
    (body : List instr) (epilogue : U32)
    (stable : CompilerStable initial final)
    (signature : types[initial.function.type_index.val]? = some ⟨.mk_list params, .mk_list results⟩)
    (locals : initial.function.locals.val.map Itasca.Translate.valueType = params ++ declared)
    (parameterSlots : initial.function.param_slots.val = slots params)
    (localSlots : initial.function.local_slots.val = slots (params ++ declared))
    (capacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (fetchBound : final.function.code.val.length ≤ U32.max)
    (bodyCode : StructuredCode emit types functions results (params ++ declared) final.function.code.val final.function.jump_tables.val
      [functionRootLabel results final.function epilogue] [] body 0 epilogue.val results)
    (returnCode : ∃ count, final.function.code.val[epilogue.val]? =
      some (.Return initial.function.local_slots count))
    (endPosition : final.function.code.val.length = epilogue.val + 1)
    (accepted : runtime.compiler.FunctionCompiler.finish ops final validated = .ok (.Ok compiled, budget)) :
    StructuredFunctionCode emit types functions params declared results body compiled epilogue := by
  obtain ⟨_, rfl, _, _, checked⟩ := compiler_finish_accepted ops final validated compiled budget accepted
  obtain ⟨_, _, _, typeEq, localsEq, paramsEq, slotsEq, _, _, _⟩ := stable.fields
  refine ⟨?_, ?_, ?_, ?_, ?_, fetchBound, checked, bodyCode, ?_, endPosition⟩
  · simpa only [typeEq] using signature
  · simpa only [localsEq] using locals
  · simpa only [paramsEq] using parameterSlots
  · simpa only [slotsEq] using localSlots
  · rw [slotsEq]
    exact capacity.trans stable.capacity
  · simpa only [slotsEq] using returnCode
end Itasca.Runtime.Compiler

end

/-! ## IndexedFunction -/

section

/-!
Contextual function syntax with the actual retained jump table. The certificate contains source/layout evidence, never an execution premise.

Main declarations: `IndexedFunctionCode` and `DefinedIndexedFunctionCode`. A direct consumer is `Compiler.Body.Relations.Executable.ExecutableFunction`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Contextual function syntax with the actual retained jump table. The
certificate contains source/layout evidence, never an execution premise. -/
def IndexedFunctionCode
    (emission : CompilerTables → context → List valtype → instr → List Bytecode → List valtype → Prop)
    (C : context) (params declared results : List valtype) (body : List instr)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32) : Prop :=
  C.LOCALS=params++declared ∧
  StructuredFunctionCode (emission (CompilerTables.ofFunction compiled) C)
    C.TYPES C.FUNCS params declared results body compiled epilogue

def DefinedIndexedFunctionCode
    (emission : CompilerTables → context → List valtype → instr → List Bytecode → List valtype → Prop)
    (env : Itasca.metadata.Env) (typeIndex : U32) (source : funccode)
    (compiled : runtime.bytecode.CompiledFunction) : Prop :=
  compiled.type_index=typeIndex ∧ ∃ signature declared body epilogue,
    env.types.val[typeIndex.val]?=some signature ∧
    source=.FUNC (.mk_uN typeIndex.val) (declared.map local.LOCAL) body ∧
    IndexedFunctionCode emission (sourceFunctionContext env
      (signature.params.val.map Itasca.Translate.valueType++declared)
      (signature.results.val.map Itasca.Translate.valueType))
      (signature.params.val.map Itasca.Translate.valueType) declared
      (signature.results.val.map Itasca.Translate.valueType) body compiled epilogue
end Itasca.Runtime.Compiler

end

/-! ## CumulativeFunctionContext -/

section

/-!
Signature transport across source contexts.

Main declarations: `Signature.context`. A direct consumer is `Integration.Execution.Dispatch.Host`.
-/

namespace Itasca.Runtime.SourceMachine.Stateful

theorem Signature.context {C D op input output}
    (functions : D.FUNCS = C.FUNCS) (tables : D.TABLES = C.TABLES)
    (memories : D.MEMS = C.MEMS) (elements : D.ELEMS = C.ELEMS)
    (datas : ∀ index : Nat, C.DATAS[index]? = some datatype.OK → D.DATAS[index]? = some datatype.OK)
    (signature : Signature C op input output) : Signature D op input output := by
  cases signature with
  | refNull type => exact .refNull type
  | refFunc index type found => exact .refFunc index type (by simpa only [functions] using found)
  | refIsNull type => exact .refIsNull type
  | tableGet index type bounds found => exact .tableGet index type bounds (by simpa only [tables] using found)
  | tableSet index type bounds found => exact .tableSet index type bounds (by simpa only [tables] using found)
  | tableSize index type found => exact .tableSize index type (by simpa only [tables] using found)
  | tableGrow index type bounds found => exact .tableGrow index type bounds (by simpa only [tables] using found)
  | tableFill index type bounds found => exact .tableFill index type bounds (by simpa only [tables] using found)
  | tableCopy destination source type destinationBounds sourceBounds destinationFound sourceFound =>
    exact .tableCopy destination source type destinationBounds sourceBounds
      (by simpa only [tables] using destinationFound) (by simpa only [tables] using sourceFound)
  | tableInit table element type bounds tableFound elementFound =>
    exact .tableInit table element type bounds (by simpa only [tables] using tableFound)
      (by simpa only [elements] using elementFound)
  | elemDrop index type found => exact .elemDrop index type (by simpa only [elements] using found)
  | memorySize type found => exact .memorySize type (by simpa only [memories] using found)
  | memoryGrow type found => exact .memoryGrow type (by simpa only [memories] using found)
  | memoryFill type found => exact .memoryFill type (by simpa only [memories] using found)
  | memoryCopy type found => exact .memoryCopy type (by simpa only [memories] using found)
  | memoryInit index type found dataFound =>
    exact .memoryInit index type (by simpa only [memories] using found) (datas index dataFound)
  | dataDrop index found => exact .dataDrop index (datas index found)
end Itasca.Runtime.SourceMachine.Stateful

end
