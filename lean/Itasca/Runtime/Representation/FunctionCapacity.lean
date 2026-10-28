import Itasca.Runtime.Representation.ValidatedStacks
import Itasca.Runtime.Equations
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- A source frame's word requirement: its parameter/local words plus the
maximum operand width in a complete canonical validation trace. The reader
trace uses the empty visitor and contains no compiled-code premise. -/
def SourceFrameCapacity (profile : ValidationProfile) (env : module.Env)
    (typeIndex : U32) (source : funccode) (words : Nat) : Prop :=
  ∃ (signature : types.FuncType) (declared : List types.ValueType)
      (data : Slice U8) (ctx : code.Context) (body : List instr)
      (samples : List (List code.StackType)),
    env.types.val[typeIndex.val]? = some signature ∧
    source = .FUNC (.mk_uN typeIndex.val) (declared.map (local.LOCAL ∘ Translate.valueType)) body ∧
    ctx.locals.val = signature.params.val ++ declared ∧
    ctx.results.val = signature.results.val ∧
    Profile.BodyEncoding profile data body ∧
    ValidatedStacksWasm2 data env ctx typeIndex (Wasm2.initial typeIndex) samples ∧
    words = slots ((signature.params.val ++ declared).map Translate.valueType) + maximumStackWords samples

/-- The allocated compiled frame is bounded by the independently described
source frame requirement. This is separate from the emitted-code relation. -/
def FunctionCapacity (profile : ValidationProfile) (env : module.Env)
    (typeIndex : U32) (source : funccode) (compiled : runtime.bytecode.CompiledFunction) : Prop :=
  ∃ words, SourceFrameCapacity profile env typeIndex source words ∧ compiled.slot_count.val ≤ words

end Itasca.Runtime.Code
