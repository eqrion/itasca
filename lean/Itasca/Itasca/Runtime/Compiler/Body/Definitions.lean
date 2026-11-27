import Itasca.Runtime.Compiler.Local.Definitions

open WebAssembly

/-! Completed function certificates used to construct the verified runtime protocol. -/

/-! ## Compiler / Body / Functions -/

section CompilerBodyFunctions

/-!
### Executable functions and frame capacities

Executable emission joins instruction families without assuming execution
correctness. Source-indexed function certificates and frame bounds separately
connect each defined function to its compiled code and storage capacity.
-/

section

/-!
## Module frame capacities

`ModuleCapacities` retains source function/frame capacity certificates for the
executable module.
-/

namespace Itasca.Compiler

open Aeneas Aeneas.Std Itasca

/-- Source-indexed frame bounds retained for the defined function prefix. -/
structure ModuleCapacities (module : runtime.compiler.ExecutableModule)
    (sources : List funccode) : Prop where
  count : sources.length = module.module.env.func_type_indices.val.length
  entry : ∀ (index : Nat) (typeIndex : U32),
    module.module.env.func_type_indices.val[index]? = some typeIndex →
      ∃ compiled source, module.functions.val[index]? = some compiled ∧
        sources[index]? = some source ∧
        Representation.CompiledFunctionCapacity module.module.env typeIndex source compiled

end Itasca.Compiler

end

section

/-!
## Executable function syntax

Ordinary, stateful, indirect, SIMD, typed-select and branch-table emission combine into
function/module code certificates without execution-correctness assumptions.
-/

namespace Itasca.Compiler

open Aeneas.Std

/-- Every emitted ordinary instruction, with the function-local index-pair, SIMD
and constant tables it uses, and the branch-table control gate. A branch-table gate
can only enter `StructuredCode` through its structural constructor, which retains
the actual target-table layout. -/
inductive ExecutableEmission (tables : CompilerTables) (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | scalar {before source emitted after} (head : ScalarEmission C before source emitted after) :
      ExecutableEmission tables C before source emitted after
  | stateful {before source emitted after} (head : StatefulEmission tables.indirect C before source emitted after) :
      ExecutableEmission tables C before source emitted after
  | indirect {before source emitted after} (head : IndirectCallEmission tables.indirect C before source emitted after) :
      ExecutableEmission tables C before source emitted after
  | simd {before source emitted after} (head : SimdEmission tables.simd tables.constants C before source emitted after) :
      ExecutableEmission tables C before source emitted after
  | typedSelect {before source emitted after} (head : TypedSelectEmission C before source emitted after) :
      ExecutableEmission tables C before source emitted after
  | branchTable (stack : List valtype) (depths : List labelidx) (fallback : labelidx)
      (selector start len : U32) :
      ExecutableEmission tables C (stack ++ [.I32]) (.BR_TABLE depths fallback)
        [.JumpTable selector start len] stack

end Itasca.Compiler

namespace Itasca.Compiler

abbrev DefinedExecutableFunctionCode := DefinedIndexedFunctionCode ExecutableEmission

end Itasca.Compiler

namespace Itasca.Compiler

open Aeneas Aeneas.Std Itasca

structure ExecutableModuleFunctions (module : runtime.compiler.ExecutableModule)
    (sources : List funccode) : Prop where
  /-- Source bodies and defined function declarations have the same count. -/
  count : sources.length = module.module.env.func_type_indices.val.length
  /-- At each source index, the concrete function has the corresponding type
  index and complete syntactic function certificate. -/
  entry : ∀ (index : Nat) (typeIndex : U32),
    module.module.env.func_type_indices.val[index]? = some typeIndex →
      ∃ compiled source, module.functions.val[index]? = some compiled ∧
        sources[index]? = some source ∧ DefinedExecutableFunctionCode module.module.env typeIndex source compiled

end Itasca.Compiler

end

end CompilerBodyFunctions
