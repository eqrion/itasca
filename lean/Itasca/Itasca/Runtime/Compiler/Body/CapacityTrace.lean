import Itasca.Runtime.Representation.Definitions
import Itasca.Body.Correctness
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterContracts
import Itasca.Runtime.Compiler.Body.Reader.StackValues
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body.

This module collects CapacityTrace, TypedLowering.
Each section documents its contracts and consumers.
-/

/-! ## CapacityTrace -/

section

open Aeneas Aeneas.Std
/-!
# Internal validation samples and their source-size bound

The compiler proof first accounts for its concrete validation samples. Body
completeness then supplies a deterministic execution with the independent byte
bound, eliminating those samples from the public capacity certificate.
-/
namespace Itasca.Representation

/-- A source-only successful validation trace, recording every operand stack.
Its reader equations use the empty visitor, independently of compiled code. -/
inductive ValidatedStacks (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) : code.BodyState → List (List code.StackType) → Prop where
  | done {st} (typed : Body.State data env ctx.locals index st)
      (closed : st.blocks.val = []) (finished : st.core.pos = Slice.len data) :
      ValidatedStacks data env ctx index st [st.core.vals.val]
  | step {st next out samples}
      (typed : Body.State data env ctx.locals index st)
      (pending : Body.Pending data env ctx.locals index {core := {st.core with pos := next}})
      (start : pending.start = st.core.pos) (advance : next.val = st.core.pos.val + 1)
      (read : code.step_body code.DefaultOpVisitor.Insts.ItascaCodeOpVisitor
        {core := {st.core with pos := next}} data env ctx index
        (data.val[pending.start.val]'pending.inbounds) () = .ok (.Ok (), out, ()))
      (rest : ValidatedStacks data env ctx index out samples) :
      ValidatedStacks data env ctx index st (st.core.vals.val :: samples)

/-- Maximum word width of the actual validated operand samples, including
unreachable source positions. Scalars/references use one word and vectors two. -/
def maximumStackWords (samples : List (List code.StackType)) : Nat :=
  samples.foldr (fun stack bound => max (stackWords stack) bound) 0


/-- The empty visitor and the factored reader step describe the same dispatch. -/
theorem empty_dispatch_eq {data env ctx index} {st next out : code.BodyState} {opcode pos}
    (nonempty : st.blocks.val ≠ [])
    (read : reader.read_byte data st.core.pos = .ok (.Ok (opcode, pos)))
    (step : Body.step {st with core := {st.core with pos := pos}} data env ctx index opcode =
      .ok (.Ok (), next))
    (dispatch : code.step_body code.DefaultOpVisitor.Insts.ItascaCodeOpVisitor
      {core := {st.core with pos := pos}} data env ctx index opcode () = .ok (.Ok (),out,())) :
    out = next := by
  have hn : st.core.ctrls.val ≠ [] := by simpa using nonempty
  have actual := Body.emptyVisitorLoop.body_eq data env ctx index st
  have loop := Body.loop_body_eq data env ctx index st
  simp only [if_neg nonempty, read, bind_ok, step, Body.continueStep] at loop
  change Body.emptyVisitorLoop.body data env index ctx.locals ctx.results st () = _ at loop
  rw [loop] at actual
  have expected : code.body_loop_loop.body code.DefaultOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx index () st = .ok (.cont ((),out)) := by
    simp [code.body_loop_loop.body, alloc.vec.Vec.is_empty, hn, read, dispatch,
      core.result.Result.Insts.CoreOpsTry.branch]
  rw [expected] at actual
  simpa using actual

theorem ValidatedStacks.byte_bound {data env ctx index st last samples}
    (trace : ValidatedStacks data env ctx index st samples)
    (run : Body.Completeness.BoundedExecution data env ctx index st last)
    (finished : last.core.pos.val = data.length) (empty : last.core.vals.val = []) :
    maximumStackWords samples ≤ 1000 * data.length := by
  induction run generalizing samples with
  | nil st =>
    cases trace with
    | done typed closed ended => simp [maximumStackWords, empty, stackWords]
    | step typed pending start advance read rest =>
      have inside := pending.inbounds
      rw [start] at inside
      omega
  | cons st next last opcode pos bound nonempty read step rest ih =>
    cases trace with
    | done typed closed ended => exact False.elim (nonempty closed)
    | @step _ cursor out samples typed pending start advance dispatch trace =>
      have inside : st.core.pos.val < data.length := by simpa only [start] using pending.inbounds
      obtain ⟨reply, read', cursor', rfl, advance'⟩ := WP.spec_imp_exists
        (reader.read_byte.spec data st.core.pos inside)
      have cursorEq : cursor' = cursor := by scalar_tac
      subst cursor'
      have eqRead := read.symm.trans read'
      have eqs : opcode = data.val[st.core.pos.val] ∧ pos = cursor := by simpa using eqRead
      have opEq : opcode = data.val[pending.start.val]'pending.inbounds := by
        simpa only [start] using eqs.1
      have posEq := eqs.2
      subst opcode
      subst pos
      have same := empty_dispatch_eq nonempty read step dispatch
      subst out
      have tail := ih trace finished empty
      have width := Itasca.Compiler.stack_words_le_twice_length st.core.vals.val
      change max (stackWords st.core.vals.val) (maximumStackWords samples) ≤ 1000 * data.length
      omega

end Itasca.Representation

end

/-! ## TypedLowering -/

section

/-!
# Typed source lowering

`SourceStack` records the validator's complete concrete source types. Typed lowering combines that stack interpretation with the instruction-emission relation used by body constructions.
-/
namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The exact concrete source types of the validator's complete operand stack. -/
structure SourceStack (raw : List code.StackType) (types : List valtype) : Prop where
  concrete : ConcreteStack raw
  decoded : Body.Stack.stackTypes raw = types

theorem SourceStack.of_map {raw : List code.StackType} {types : List valtype}
    (values : List Itasca.wasm_types.ValueType) (concrete : raw = values.map code.StackType.Val)
    (decoded : values.map Translation.valueType = types) : SourceStack raw types := by
  refine ⟨(concrete_stack_iff raw).mpr ⟨values, concrete⟩, ?_⟩
  simpa only [concrete, Body.Stack.stackTypes, List.map_map, Function.comp_def] using decoded

/-- Actual lowering plus the exact post-reader type vector. Word offsets alone
would not distinguish source types that share the same machine width. -/
def TypedLowered {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (raw : List code.StackType) (instruction : Bytecode) (stack : List valtype) : Prop :=
  Lowered before after instruction stack ∧ SourceStack raw stack

def TypedLoweredEmpty {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (raw : List code.StackType) (stack : List valtype) : Prop :=
  LoweredEmpty before after stack ∧ SourceStack raw stack

end Itasca.Compiler

end
