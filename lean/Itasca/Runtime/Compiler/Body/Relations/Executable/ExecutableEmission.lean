import Itasca.Runtime.Compiler.Body.Control.Embedding.OrdinaryEmbedding
import Itasca.Runtime.Compiler.Local.Control.Simd.StructuredSimdEmbedding
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTables
import Itasca.Runtime.Compiler.Local.Source.TypedSelectEmission

/-!
Every emitted ordinary instruction, with the function-local index-pair, SIMD and constant tables it uses, and the branch-table control gate. A branch-table gate can only enter `StructuredCode` through its structural constructor, which retains the actual target-table layout.

Main declarations: `ExecutableEmission`. A direct consumer is `Compiler.Body.Relations.Checking.ExecutableInstructionAcceptance`.
-/

namespace Itasca.Runtime.Compiler
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

instance (tables C) : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C) :=
  ⟨.scalar, .stateful, .indirect⟩
instance (tables C) : SimdEmbedding tables.simd tables.constants C (ExecutableEmission tables C) :=
  ⟨.simd⟩

end Itasca.Runtime.Compiler
