import Exec.Code.Body.Reader.Common.CumulativeReaderCompilerState
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerPoint
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A complete compiler point is retained for every future extension of the
current pair table. Each point includes its own exact canonical source zipper. -/
def CumulativeReaderCompilerPointWasm1 {A : Type} (C : context)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bodyBt : code.BlockType)
    (st : code.OpIterState) : Prop :=
  ∀ future : List (U32 × U32),
    StructuredReaderCompilerPointWasm1 (CumulativeEmission (compiler.function.indirect.val ++ future) C)
      initial compiler types functions returns locals data env ctx bodyBt st

def CumulativeReaderCompilerPointWasm2 {A : Type} (C : context)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : module.Env) (sourceLocals : alloc.vec.Vec Itasca.types.ValueType)
    (index : U32) (ft : Itasca.types.FuncType) (st : code.BodyState) : Prop :=
  ∀ future : List (U32 × U32),
    StructuredReaderCompilerPointWasm2 (CumulativeEmission (compiler.function.indirect.val ++ future) C)
      initial compiler types functions returns locals data env sourceLocals index ft st

theorem CumulativeReaderCompilerStateWasm1.point {A : Type}
    {C initial compiler types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : @CumulativeReaderCompilerStateWasm1 C A initial compiler types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent) :
    CumulativeReaderCompilerPointWasm1 C initial compiler types functions returns locals data env ctx bodyBt st := by
  intro future
  exact ⟨parents,current,savedParents,savedCurrent,state.compiled future,state.boundary,state.sources,
    state.reach,state.fronts,state.knownFronts⟩

theorem CumulativeReaderCompilerStateWasm2.point {A : Type}
    {C initial compiler types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : @CumulativeReaderCompilerStateWasm2 C A initial compiler types functions returns locals data env sourceLocals index ft st
      parents current savedParents savedCurrent) :
    CumulativeReaderCompilerPointWasm2 C initial compiler types functions returns locals data env sourceLocals index ft st := by
  intro future
  exact ⟨parents,current,savedParents,savedCurrent,state.compiled future,state.boundary,state.sources,
    state.reach,state.fronts,state.knownFronts⟩

theorem CumulativeReaderCompilerPointWasm2.append_step {A : Type}
    {C initial before after types functions returns locals data env sourceLocals index ft st out}
    (point : @CumulativeReaderCompilerPointWasm2 A C initial before types functions returns locals data env sourceLocals index ft st)
    (extra : List (U32 × U32)) (pairs : after.function.indirect.val = before.function.indirect.val ++ extra)
    (step : ∀ future,
      StructuredReaderCompilerPointWasm2 (CumulativeEmission (after.function.indirect.val ++ future) C)
        initial before types functions returns locals data env sourceLocals index ft st →
      StructuredReaderCompilerPointWasm2 (CumulativeEmission (after.function.indirect.val ++ future) C)
        initial after types functions returns locals data env sourceLocals index ft out) :
    CumulativeReaderCompilerPointWasm2 C initial after types functions returns locals data env sourceLocals index ft out := by
  intro future
  apply step future
  simpa only [pairs,List.append_assoc] using point (extra ++ future)

theorem CumulativeReaderCompilerPointWasm2.preserved_step {A : Type}
    {C initial before after types functions returns locals data env sourceLocals index ft st out}
    (point : @CumulativeReaderCompilerPointWasm2 A C initial before types functions returns locals data env sourceLocals index ft st)
    (pairs : after.function.indirect = before.function.indirect)
    (step : ∀ future,
      StructuredReaderCompilerPointWasm2 (CumulativeEmission (before.function.indirect.val ++ future) C)
        initial before types functions returns locals data env sourceLocals index ft st →
      StructuredReaderCompilerPointWasm2 (CumulativeEmission (before.function.indirect.val ++ future) C)
        initial after types functions returns locals data env sourceLocals index ft out) :
    CumulativeReaderCompilerPointWasm2 C initial after types functions returns locals data env sourceLocals index ft out := by
  intro future
  simpa only [pairs] using step future (point future)

end Exec.Code
