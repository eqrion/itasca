import Itasca.Runtime.Representation.StackLayout
import Itasca.Wasm2.Invariant
import Itasca.Profile.BodySpec

/-!
Independent validated source stacks and their maximum slot demand. Function-capacity certificates and compiler folds share this source-only bound.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A source-only successful validation trace, recording every operand stack.
Its reader equations use the empty visitor, independently of compiled code. -/
inductive ValidatedStacksWasm2 (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) : code.BodyState → List (List code.StackType) → Prop where
  | done {st} (typed : Wasm2.State data env .Wasm2 ctx.locals index st)
      (closed : st.blocks.val = []) (finished : st.core.pos = Slice.len data) :
      ValidatedStacksWasm2 data env ctx index st [st.core.vals.val]
  | step {st next out samples}
      (typed : Wasm2.State data env .Wasm2 ctx.locals index st)
      (pending : Wasm2.Pending data env .Wasm2 ctx.locals index {core := {st.core with pos := next}})
      (start : pending.start = st.core.pos) (advance : next.val = st.core.pos.val + 1)
      (read : code.step_profile code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
        {core := {st.core with pos := next}} data env ctx index .Wasm2
        (data.val[pending.start.val]'pending.inbounds) () = .ok (.Ok (), out, ()))
      (rest : ValidatedStacksWasm2 data env ctx index out samples) :
      ValidatedStacksWasm2 data env ctx index st (st.core.vals.val :: samples)

/-- Maximum word width of the actual validated operand samples, including
unreachable source positions. Scalars/references use one word and vectors two. -/
def maximumStackWords (samples : List (List code.StackType)) : Nat :=
  samples.foldr (fun stack bound => max (stackWords stack) bound) 0

end Itasca.Runtime.Compiler
