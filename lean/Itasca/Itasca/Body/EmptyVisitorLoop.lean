import Itasca.Binary.Definitions
import Itasca.Support.Translation
import Itasca.Handler.Environment
import Itasca.Body.TableAdapters
import Itasca.Handler.StackEffects
import Itasca.Binary.Scalar.Encoding

/-!
Proofs for Body.

This module collects State, EmptyVisitorLoop.
Each section documents its contracts and consumers.
-/

/-! ## State -/

section

/-!
# Internal body validation invariant

The zipper and pending-state witnesses connect the mutable validator stacks to
independent syntax and typing. Public body validity retains only the resulting
source certificate; these states are used to construct it.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Frames

/-- The kind of an open construct. An `else_` frame remembers the tokens and instructions of its
`then` arm. -/
inductive Form where
  | body | block | loop | then_
  | else_ (thenTokens : List Token) (thenOps : List instr)

/-- The runtime label kind of a frame form. -/
def Form.kind : Form → code.LabelKind
  | .body => .Body
  | .block => .Block
  | .loop => .Loop
  | .then_ => .Then
  | .else_ _ _ => .Else

/-- Function parameters live in locals; all nested constructs start with
their declared block parameters on the operand stack. -/
def Form.params (form : Form) (ins : List wasm_types.ValueType) : List wasm_types.ValueType :=
  match form with
  | .body => []
  | _ => ins

/-- The operands consumed on entry: the block parameters, plus the `i32` condition of `if`. -/
def Form.args (form : Form) (ins : List wasm_types.ValueType) : List valtype :=
  ins.map Translation.valueType ++ match form with
  | .then_ | .else_ _ _ => [.I32]
  | _ => []

/-- The types a branch to the frame carries: the parameters for `loop`, the results otherwise. -/
def Form.label (form : Form) (ins outs : List wasm_types.ValueType) : List valtype :=
  (match form with | .loop => ins | _ => outs).map Translation.valueType

/-- The typing context inside a frame: its label pushed onto the enclosing context. -/
def enter (C : context) (form : Form) (ins outs : List wasm_types.ValueType) : context :=
  Body.Control.labelContext (form.label ins outs) ++ C

/-- The already completed material of a frame is well typed. Only an `else_` frame has any: its
`then` arm. -/
def Form.Valid (C : context) (ins outs : List wasm_types.ValueType) : Form → Prop
  | .else_ tokens ops => Emits tokens ops ∧
      Instrs_ok (enter C (.else_ tokens ops) ins outs) ops
        (.mk_functype (.mk_list (ins.map Translation.valueType))
          (.mk_list (outs.map Translation.valueType)))
  | _ => True

/-- A frame of the zipper: its runtime control entry, block type, resolved signature, form, and
the instructions, operand stack and tokens read so far. -/
structure Saved where
  /-- Concrete control entry, including label kind, type and operand base. -/
  ctrl : code.Ctrl
  /-- Independent binary block signature for this frame. -/
  bt : signature.BlockType
  /-- Resolved input types of the block signature. -/
  ins : List wasm_types.ValueType
  /-- Resolved output types of the block signature. -/
  outs : List wasm_types.ValueType
  /-- Source construct and any completed then-arm material. -/
  form : Form
  /-- Structured instructions completed within this frame. -/
  ops : List instr
  /-- Concrete operand segment above this frame's base. -/
  vals : List code.StackType
  /-- Exact flat tokens spelling the completed frame prefix. -/
  tokens : List Token

/-- The static facts about a frame: its control entry matches its form, its signature resolves
from its block type, and its completed material is valid and emitted by its tokens. -/
structure Header (env : metadata.Env) (C : context) (f : Saved) : Prop where
  /-- Concrete and source control kinds agree. -/
  kind : f.ctrl.kind = f.form.kind
  /-- The binary signature resolves to these input types. -/
  inputs : resolve env (Body.inputs f.bt) = some f.ins
  /-- The binary signature resolves to these result types. -/
  outputs : resolve env (Body.outputs f.bt) = some f.outs
  /-- Any completed then arm retains its encoding and typing. -/
  prior : f.form.Valid C f.ins f.outs
  /-- The retained tokens spell the same completed instructions. -/
  emits : Emits f.tokens f.ops

/-- Suspended frames retain typing from their own input vector and remember
the child arguments removed from the concrete operand stack. -/
inductive Spine (env : metadata.Env) (root : context) :
    List Saved → context → List code.StackType → Form → List wasm_types.ValueType → Prop where
  | root (ins) : Spine env root [] root [] .body ins
  | push (parents : List Saved) (C : context) (outer : List code.StackType)
      (parent : Saved) (child : Form) (ins : List wasm_types.ValueType)
      (spine : Spine env root parents C outer parent.form parent.ins)
      (header : Header env C parent)
      (base : parent.ctrl.value_stack_base.val = outer.length)
      (resume : ResumePrefix (enter C parent.form parent.ins parent.outs)
        ((parent.form.params parent.ins).map Translation.valueType)
        parent.ops parent.ctrl.polymorphic_base parent.vals (child.args ins))
      (notBody : child ≠ .body) :
      Spine env root (parents ++ [parent]) (enter C parent.form parent.ins parent.outs)
        (outer ++ parent.vals) child ins

/-- The semantic control invariant aligns both physical control vectors with
a typed syntax zipper, and partitions operands at each frame's actual base. -/
def Open (env : metadata.Env) (root : context) (st : code.BodyState)
    (parents : List Saved) (current : Saved) : Prop :=
  ∃ C outer, Spine env root parents C outer current.form current.ins ∧
    Header env C current ∧ current.ctrl.value_stack_base.val = outer.length ∧
    TypedPrefix (enter C current.form current.ins current.outs)
      ((current.form.params current.ins).map Translation.valueType)
      current.ops current.ctrl.polymorphic_base current.vals ∧
    st.core.ctrls.val = parents.map Saved.ctrl ++ [current.ctrl] ∧
    st.blocks.val = parents.map Saved.bt ++ [current.bt] ∧
    st.core.vals.val = outer ++ current.vals

/-- The tokens emitted when a frame is opened (and, for `else_`, its `then` arm is closed). -/
def Form.opening (form : Form) (bt : signature.BlockType) : List Token :=
  match form with
  | .body => []
  | .block => [.block bt]
  | .loop => [.loop bt]
  | .then_ => [.if_ bt]
  | .else_ tokens _ => [.if_ bt] ++ tokens ++ [.else_]

/-- The tokens of a frame from its opening onwards. -/
def Saved.trace (f : Saved) : List Token := f.form.opening f.bt ++ f.tokens

/-- The tokens read so far across all open frames, outermost first. -/
def trace (parents : List Saved) (current : Saved) : List Token :=
  parents.flatMap Saved.trace ++ current.trace

/-- The outermost descriptor stays fixed while nested frames are opened,
advanced, switched to else, and closed. -/
def bodyType (parents : List Saved) (current : Saved) : Option signature.BlockType :=
  ((parents ++ [current]).head?).map Saved.bt

end Itasca.Body.Frames

namespace Itasca.Body

/-- Implementation limits on the body size, the byte cursor and the number of open frames. -/
structure Bounds (data : Slice U8) (st : code.BodyState) : Prop where
  /-- The complete body fits the implementation byte cap. -/
  size : data.length ≤ limits.MAX_FUNCTION_BYTES.val
  /-- The concrete cursor stays within the complete body. -/
  pos : st.core.pos.val ≤ data.length
  /-- Open block descriptors are bounded by consumed bytes plus the root. -/
  ctrls : st.blocks.val.length ≤ st.core.pos.val + 1

/-- A running typed zipper or a completed typed body, with exact provenance
for the consumed prefix. No condition is placed on unread bytes. -/
inductive State (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) : code.BodyState → Prop where
  | running (st : code.BodyState) (ft : wasm_types.FuncType)
      (parents : List Frames.Saved) (current : Frames.Saved) :
      env.types.val[index.val]? = some ft → Bounds data st →
      Frames.Open env (bodyContext env locals ft) st parents current →
      Frames.bodyType parents current = some (.TypeIndex index) →
      Consumed data 0#usize (Frames.trace parents current) st.core.pos →
      TokensDeclared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) (Frames.trace parents current) →
      State data env locals index st
  | closed (st : code.BodyState) (ft : wasm_types.FuncType) (ops : List instr) (tokens : List Token) :
      env.types.val[index.val]? = some ft → Bounds data st →
      st.core.ctrls.val = [] → st.blocks.val = [] → BodyTokens tokens ops →
      FunctionTyped env locals ft ops → Consumed data 0#usize tokens st.core.pos →
      TokensDeclared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) tokens →
      State data env locals index st

/-- The loop's initial body state: one body frame for the function type at `index`. -/
def initial (index : U32) : code.BodyState :=
  { core := ⟨alloc.vec.Vec.new _,
      alloc.vec.Vec.from [⟨.Body, .TypeIndex index, 0#usize, false⟩] (by scalar_tac), 0#usize⟩ }

/-- The opcode at `start` has been consumed; its immediate remains arbitrary.
The retained prefix, open frames and bounds describe the state before dispatch. -/
structure Pending (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (st : code.BodyState) where
  /-- Body-relative byte position of the consumed opcode. -/
  start : Usize
  /-- Function signature selected from the environment's type table. -/
  ft : wasm_types.FuncType
  /-- Suspended source frames surrounding the current control frame. -/
  parents : List Frames.Saved
  /-- Source witness for the currently open control frame. -/
  current : Frames.Saved
  /-- The selected type index denotes `ft`. -/
  signature : env.types.val[index.val]? = some ft
  /-- Complete body bytes satisfy the implementation byte cap. -/
  size : data.length ≤ limits.MAX_FUNCTION_BYTES.val
  /-- Saved source frames represent the concrete operand/control stacks. -/
  opened : Frames.Open env (bodyContext env locals ft) st parents current
  /-- The outer body frame retains this function's type index. -/
  bodyType : Frames.bodyType parents current = some (.TypeIndex index)
  /-- The preceding body bytes encode the reconstructed instruction prefix. -/
  consumed : Consumed data 0#usize (Frames.trace parents current) start
  /-- Every `ref.func` in that prefix satisfies the declared-reference condition. -/
  declared : TokensDeclared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) (Frames.trace parents current)
  /-- The consumed opcode position is within the complete body buffer. -/
  inbounds : start.val < data.length
  /-- The concrete cursor is immediately after the opcode byte. -/
  pos : st.core.pos.val = start.val + 1
  /-- Open block descriptors are bounded by the consumed byte prefix. -/
  ctrls : st.blocks.val.length ≤ start.val + 1

end Itasca.Body

end

/-! ## EmptyVisitorLoop -/

section

/-!
# Empty Visitor Loop

Empty-visitor execution preserves result stacks and exact source prefixes or suffixes. These facts connect plain body validation to the instruction-loop invariant.
-/

/-! ## ResultStack -/

section

/-!
# Descriptor stack operations

Specs of the extracted operand-stack operations that take a `signature.ResultType` descriptor:
`code.check_func_type`, `code.push_results` and `code.pop_results`. `push_results.spec` and
`pop_results.concrete` and `.polymorphic` describe their effect on the stack for a resolved
descriptor. The following semantic and normal-return sections strengthen these effects.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `code.check_func_type` accepts exactly the function types within the parameter and result
limits and reports which limit is exceeded otherwise. -/
@[step]
theorem code.check_func_type.spec (ft : wasm_types.FuncType) :
    code.check_func_type ft ⦃ r =>
      match r with
      | .Ok _ => ft.params.val.length ≤ 1000 ∧ ft.results.val.length ≤ 1000
      | .Err .TooManyParams => 1000 < ft.params.val.length
      | .Err .TooManyResults => 1000 < ft.results.val.length
      | .Err _ => False ⦄ := by
  unfold code.check_func_type
  simp only [limits.MAX_MULTI_VALUE_PARAMS, limits.MAX_MULTI_VALUE_RESULTS]
  step*

/-- Pushing a resolved descriptor has exactly the shared stack primitive's
    effect, with no intermediate runtime vector. -/
theorem code.push_results.spec (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (ts : List wasm_types.ValueType)
    (hts : Body.resolve env view = some ts)
    (hcap : st.vals.val.length + ts.length ≤ Usize.max) :
    code.push_results st env view ⦃ r =>
      r.1 = .Ok () ∧ r.2.vals.val = st.vals.val ++ ts.map code.StackType.Val ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  obtain ⟨r, hr, ht⟩ := WP.spec_imp_exists (signature.ResultType.len.spec view env)
  cases r with
  | Err e => simp [hts] at ht
  | Ok n =>
    obtain ⟨ts', he, hn⟩ := ht
    have heq : ts' = ts := by simpa [hts] using he.symm
    subst ts'
    unfold code.push_results
    rw [hr]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step
    split
    · scalar_tac
    · cases view with
      | Empty => simp_all [Body.resolve]
      | One t =>
        simp [Body.resolve] at hts
        subst ts
        step*
        all_goals simp_all
      | «Type» index part =>
        by_cases hi : index.val < env.types.val.length
        · cases part <;> simp [Body.resolve, List.getElem?_eq_getElem hi] at hts
          all_goals subst ts
          all_goals step*
          all_goals simp_all [alloc.vec.Vec.deref]
        · simp [Body.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hts

end Itasca

end

/-! ## ResultStackSemantics -/

section

/-!
# Descriptor stack operations, semantics and totality

Semantic specs of `code.pop_results` and `code.push_results`. `code.pop_results.realizes` relates
a successful pop to the backward stack interpretation, `.complete` gives acceptance from
independent stack compatibility, and `.total` and `code.push_results.total` show that neither
panics or diverges on arbitrary descriptors and environments.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- Descriptor pops preserve the backward stack interpretation, including
mixed concrete/`Bot` stacks and implicit operands at an unreachable base. -/
theorem code.pop_results.realizes (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (expected : List wasm_types.ValueType)
    (outer segment : List code.StackType)
    (hts : Body.resolve env view = some expected)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Body.Control.base st).val = outer.length) :
    code.pop_results st env view ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
        (r.1 = .Ok () → ∀ ts, Body.Stack.Realizes (Body.Control.polymorphic st) rest ts →
          Body.Stack.Realizes (Body.Control.polymorphic st) segment
            (ts ++ expected.map Translation.valueType)) ⦄ := by
  cases view with
  | Empty =>
    simp [Body.resolve] at hts
    subst expected
    simp only [code.pop_results, WP.spec_ok]
    exact ⟨trivial, trivial, segment, hvals, le_refl _, by simp⟩
  | One t =>
    simp [Body.resolve] at hts
    subst expected
    obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hl, ht⟩ := WP.spec_imp_exists
      (code.pop_with_type.realizes st outer segment t hvals hbase)
    cases res <;> simp [code.pop_results, hr,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · exact ⟨hc, hp, rest, hv, hl, ht.2⟩
    · exact ⟨hc, hp, rest, hv, hl⟩
  | «Type» index part =>
    by_cases hi : index.val < env.types.val.length
    · cases part <;> simp [Body.resolve, List.getElem?_eq_getElem hi] at hts
      all_goals subst expected
      all_goals unfold code.pop_results
      all_goals step
      all_goals split
      all_goals first | scalar_tac | skip
      all_goals step
      all_goals step with code.pop_types.realizes st outer segment _ hvals hbase
      all_goals simp_all [alloc.vec.Vec.deref]
      all_goals intro hok; simpa [hok] using r_post4
    · simp [Body.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hts

/-- Independent stack compatibility suffices for descriptor-pop acceptance. -/
theorem code.pop_results.complete (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (expected : List wasm_types.ValueType)
    (outer segment : List code.StackType) (ts : List valtype)
    (hts : Body.resolve env view = some expected)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Body.Control.base st).val = outer.length)
    (ht : Body.Stack.Realizes (Body.Control.polymorphic st) segment
      (ts ++ expected.map Translation.valueType)) :
    code.pop_results st env view ⦃ r =>
      r.1 = .Ok () ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
        Body.Stack.Realizes (Body.Control.polymorphic st) rest ts ⦄ := by
  cases view with
  | Empty =>
    simp [Body.resolve] at hts
    subst expected
    simp only [code.pop_results, WP.spec_ok]
    exact ⟨trivial, trivial, trivial, segment, hvals, le_refl _, by simpa using ht⟩
  | One t =>
    simp [Body.resolve] at hts
    subst expected
    obtain ⟨v, s, rest, hr, hc, hp, hv, hl, _, ht'⟩ :=
      code.pop_with_type.complete st outer segment ts t hvals hbase (by simpa using ht)
    simpa [code.pop_results, hr, core.result.Result.Insts.CoreOpsTry.branch]
      using And.intro hc (And.intro hp ⟨rest, hv, hl, ht'⟩)
  | «Type» index part =>
    by_cases hi : index.val < env.types.val.length
    · cases part <;> simp [Body.resolve, List.getElem?_eq_getElem hi] at hts
      all_goals subst expected
      all_goals unfold code.pop_results
      all_goals step
      all_goals split
      all_goals first | scalar_tac | skip
      all_goals step
      all_goals first
        | step with code.pop_types.complete st outer segment ts (alloc.vec.Vec.deref ft.params) hvals hbase (by simpa [alloc.vec.Vec.deref, ft_post, r_post] using ht)
        | step with code.pop_types.complete st outer segment ts (alloc.vec.Vec.deref ft.results) hvals hbase (by simpa [alloc.vec.Vec.deref, ft_post, r_post] using ht)
      all_goals simp_all
    · simp [Body.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hts

/-- No descriptor, including an invalid type index, can make a bounded pop
panic or diverge. Frame bounds are preserved even on rejection. -/
@[step]
theorem code.pop_results.total (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (hshape : Body.Control.Shape st) :
    code.pop_results st env view ⦃ r =>
      Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
        r.2.vals.val.length ≤ st.vals.val.length ⦄ := by
  cases view with
  | Empty => simp [code.pop_results, hshape]
  | One t =>
    unfold code.pop_results
    step with code.pop_with_type.total st t hshape
    step*
  | «Type» index part =>
    unfold code.pop_results
    step
    split
    · simp [hshape]
    · cases part <;> step
      all_goals step with code.pop_types.total st _ hshape
      all_goals simp_all

/-- The explicit capacity guard makes descriptor pushes total for arbitrary
environments, including invalid descriptors and oversized stored signatures. -/
@[step]
theorem code.push_results.total (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (hshape : Body.Control.Shape st) :
    code.push_results st env view ⦃ r =>
      Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      (r.1 = .Ok () → ∃ ts, Body.resolve env view = some ts ∧
        r.2.vals.val = st.vals.val ++ ts.map code.StackType.Val) ⦄ := by
  obtain ⟨res, hr, hs⟩ := WP.spec_imp_exists (signature.ResultType.len.spec view env)
  cases res with
  | Err e =>
    simp [code.push_results, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hshape]
  | Ok n =>
    obtain ⟨ts, hts, hn⟩ := hs
    by_cases hcap : st.vals.val.length + ts.length ≤ Usize.max
    · obtain ⟨⟨r, s⟩, hrun, hok, hv, hc, hp⟩ := WP.spec_imp_exists
        (code.push_results.spec st env view ts hts hcap)
      rw [hrun, WP.spec_ok]
      refine ⟨hshape.replace_operands hc ?_, hc, hp, fun _ => ⟨ts, hts, hv⟩⟩
      have hb := hshape.base_le
      simp only [hv, List.length_append, List.length_map]
      omega
    · unfold code.push_results
      rw [hr]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step
      split
      · simp [hshape]
      · scalar_tac

end Itasca

end

/-! ## Suffix -/

section

/-!
# Operand suffix compatibility

The non-destructive operand check that `br_table` applies to each target. `Body.Fits`
and `Body.Suffix` independently specify that the top of an operand stack is compatible with a
signature, `code.check_suffix_loop.spec` is the exact contract of the extracted loop, and
`code.check_suffix.spec` and `.complete` give soundness, totality and completeness of
`code.check_suffix`.
-/

open Aeneas Aeneas.Std

set_option maxRecDepth 2048

namespace Itasca.Body

/-- Compatibility from the top of an operand stack downwards. Each target is
compared to the original operands; a `Bot` is never specialized to one target. -/
def Fits : Bool → List code.StackType → List wasm_types.ValueType → Prop
  | _, _, [] => True
  | poly, [], _ :: _ => poly = true
  | poly, v :: vs, t :: ts =>
      Body.Stack.Accepts v (Translation.valueType t) ∧ Fits poly vs ts

@[simp] theorem Fits.nil (poly : Bool) (vs : List code.StackType) : Fits poly vs [] := by
  cases vs <;> trivial

@[simp] theorem Fits.unreachable (ts : List wasm_types.ValueType) : Fits true [] ts := by
  cases ts <;> trivial

/-- Independent compatibility of a signature with the current operand suffix. -/
def Suffix (st : code.OpIterState) (ts : List wasm_types.ValueType) : Prop :=
  Fits (Body.Control.polymorphic st)
    (st.vals.val.drop (Body.Control.base st).val).reverse ts.reverse

end Itasca.Body

namespace Itasca

/-- Exact loop contract: rejection is equivalent to incompatibility of the
remaining signature with the unchanged stack slice. -/
theorem code.check_suffix_loop.spec (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (ts : List wasm_types.ValueType)
    (hts : Body.resolve env view = some ts) (stack i : Usize)
    (hb : (Body.Control.base st).val ≤ stack.val) (hs : stack.val ≤ st.vals.val.length)
    (hi : i.val ≤ ts.length) :
    code.check_suffix_loop st.vals st.ctrls st.pos env view (Body.Control.base st) stack i ⦃ r =>
      r = .Ok () ↔ Body.Fits (Body.Control.polymorphic st)
        ((st.vals.val.take stack.val).drop (Body.Control.base st).val).reverse
        (ts.take i.val).reverse ⦄ := by
  unfold code.check_suffix_loop
  apply loop.spec_decr_nat (fun p => p.2.val)
    (fun p => (Body.Control.base st).val ≤ p.1.val ∧ p.1.val ≤ st.vals.val.length ∧
      p.2.val ≤ ts.length ∧
      (Body.Fits (Body.Control.polymorphic st)
          ((st.vals.val.take stack.val).drop (Body.Control.base st).val).reverse
          (ts.take i.val).reverse ↔
        Body.Fits (Body.Control.polymorphic st)
          ((st.vals.val.take p.1.val).drop (Body.Control.base st).val).reverse
          (ts.take p.2.val).reverse))
  · rintro ⟨s, j⟩ ⟨hb', hs', hj, he⟩
    dsimp only at hb' hs' hj he
    unfold code.check_suffix_loop.body
    dsimp only
    split
    · rename_i hz
      simpa [hz] using he.symm
    · rename_i hnz
      step
      have hj' : i2.val < ts.length := by omega
      have hjstep : j.val = i2.val + 1 := by omega
      have ht : (ts.take j.val).reverse = ts[i2.val] :: (ts.take i2.val).reverse := by
        rw [hjstep, List.take_succ_eq_append_getElem hj']
        simp
      rw [signature.ResultType.get.complete view env ts hts i2]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        List.getElem?_eq_getElem hj']
      split
      · rename_i hbase
        have hempty : ((st.vals.val.take s.val).drop (Body.Control.base st).val).reverse = [] := by
          rw [hbase]
          simp
        step with code.cur_polymorphic.spec st
        subst b
        split
        · rename_i hpoly
          simp only [WP.spec_ok]
          refine ⟨hb', hs', by omega, ?_, by omega⟩
          simpa [hempty, ht, hpoly, Body.Fits] using he
        · rename_i hpoly
          simp only [WP.spec_ok]
          simpa [hempty, ht, Body.Fits, hpoly] using he.symm
      · rename_i hbase
        have hbne : s.val ≠ (Body.Control.base st).val := fun h => hbase (UScalar.eq_of_val_eq h)
        step
        have hidx : stack1.val < st.vals.val.length := by omega
        have hbstep : (Body.Control.base st).val ≤ stack1.val := by omega
        have hsstep : s.val = stack1.val + 1 := by omega
        have hv : ((st.vals.val.take s.val).drop (Body.Control.base st).val).reverse =
            st.vals.val[stack1.val] ::
              ((st.vals.val.take stack1.val).drop (Body.Control.base st).val).reverse := by
          rw [hsstep, List.take_succ_eq_append_getElem hidx,
            List.drop_append_of_le_length (by simp; omega)]
          simp
        step as ⟨operand, hop⟩
        rw [hop]
        clear hop
        split
        · rename_i actual hactual
          step with core.cmp.PartialEq.ne.trait_default.spec
            wasm_types.ValueType.Insts.CoreCmpPartialEqValueType _ _ (wasm_types.ValueType.eq_spec _ _)
            as ⟨different, hdifferent⟩
          split
          · rename_i hne
            have hbad : Translation.valueType actual ≠ Translation.valueType ts[i2.val] :=
              fun h => (hdifferent.mp hne) (Translation.value_type_injective h)
            simp only [WP.spec_ok]
            simpa [hv, ht, hactual, Body.Fits, Body.Stack.Accepts, eq_comm, hbad] using he.symm
          · rename_i heq
            have hequal : actual = ts[i2.val] := by simpa [heq] using hdifferent
            simp only [WP.spec_ok]
            refine ⟨hbstep, by omega, by omega, ?_, by omega⟩
            simpa [hv, ht, hactual, Body.Fits, Body.Stack.Accepts, eq_comm, hequal] using he
        · rename_i hbot
          simp only [WP.spec_ok]
          refine ⟨hbstep, by omega, by omega, ?_, by omega⟩
          simpa [hv, ht, hbot, Body.Fits, Body.Stack.Accepts] using he
  · exact ⟨hb, hs, hi, Iff.rfl⟩

/-- The actual non-destructive suffix checker is total, sound, and complete
for the independently specified operand compatibility relation. -/
theorem code.check_suffix.spec (st : code.OpIterState) (env : metadata.Env)
    (view : signature.ResultType) (hshape : Body.Control.Shape st) :
    code.check_suffix st env view ⦃ r =>
      r = .Ok () ↔ ∃ ts, Body.resolve env view = some ts ∧ Body.Suffix st ts ⦄ := by
  unfold code.check_suffix
  step with code.cur_base.spec st
  subst base
  obtain ⟨r, hr, ht⟩ := WP.spec_imp_exists (signature.ResultType.len.spec view env)
  rw [hr]
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ht.2]
  | Ok n =>
    obtain ⟨ts, hts, hn⟩ := ht
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_mono (code.check_suffix_loop.spec st env view ts hts
      (alloc.vec.Vec.len st.vals) n hshape.base_le (by simp) (by omega))
    intro res hs
    simpa [hts, hn, Body.Suffix] using hs

end Itasca

end

/-! ## Prefix -/

section

/-!
# Typed instruction prefixes

`TypedPrefix` says that the instructions read so far in a frame are well formed and typed by the
generated `Instrs_ok` rules for every interpretation of the current operand stack. `ResumePrefix`
is the form kept for a suspended parent frame. `TypedPrefix.append` extends a prefix by one typed
instruction, and `ResumePrefix.finish` appends the finished child construct to a suspended
parent.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- A frame with no instructions is a typed prefix of its parameter vector. -/
theorem TypedPrefix.start (C : context) (hC : wf_context C) (inputs : List wasm_types.ValueType) :
    TypedPrefix C (inputs.map Translation.valueType) [] false
      (inputs.map code.StackType.Val) := by
  constructor
  · simp [Forall]
  · intro ts ht
    obtain ⟨pre, hp, rfl⟩ := (Body.Stack.realizes_append_concrete false [] inputs ts).mp
      (by simpa using ht)
    have he := (Body.Stack.realizes_empty pre).mp hp
    subst pre
    simpa using Instrs_ok.frame C [] (inputs.map Translation.valueType) [] []
      (.empty C hC) hC (by simp [Forall])

/-- Appending a typed instruction to a typed prefix gives a typed prefix. -/
theorem TypedPrefix.append {C inputs ops poly poly' vals vals'}
    (h : TypedPrefix C inputs ops poly vals) (hC : wf_context C)
    (op : instr) (hwf : wf_instr op)
    (hstep : ∀ out, Body.Stack.Realizes poly' vals' out →
      ∃ before, Body.Stack.Realizes poly vals before ∧
        Instrs_ok C [op] (.mk_functype (.mk_list before) (.mk_list out))) :
    TypedPrefix C inputs (ops ++ [op]) poly' vals' := by
  constructor
  · simpa [Forall, or_imp, forall_and] using And.intro h.wellFormed hwf
  · intro out hout
    obtain ⟨before, hin, hop⟩ := hstep out hout
    exact .seq C ops [op] inputs out before (h.typed before hin) hop hC
      h.wellFormed (by simpa [Forall] using hwf)

/-- Popping the child's arguments from a typed prefix gives the parent's resume prefix. -/
theorem ResumePrefix.after_pop {C inputs ops poly before after args}
    (h : TypedPrefix C inputs ops poly before)
    (hpop : ∀ ts, Body.Stack.Realizes poly after ts →
      Body.Stack.Realizes poly before (ts ++ args)) :
    ResumePrefix C inputs ops poly after args :=
  ⟨h.wellFormed, fun ts ht => h.typed _ (hpop ts ht)⟩

/-- A finished child construct typed from the saved arguments to its results extends the suspended
parent to a typed prefix. -/
theorem ResumePrefix.finish {C inputs ops poly vals args}
    (h : ResumePrefix C inputs ops poly vals args) (hC : wf_context C)
    (op : instr) (results : List wasm_types.ValueType) (hwf : wf_instr op)
    (hop : Instr_ok C op
      (.mk_functype (.mk_list args) (.mk_list (results.map Translation.valueType)))) :
    TypedPrefix C inputs (ops ++ [op]) poly (vals ++ results.map code.StackType.Val) := by
  constructor
  · simpa [Forall, or_imp, forall_and] using And.intro h.wellFormed hwf
  · intro ts ht
    obtain ⟨pre, hp, rfl⟩ := (Body.Stack.realizes_append_concrete poly vals results ts).mp ht
    exact .seq C ops [op] inputs (pre ++ results.map Translation.valueType) (pre ++ args)
      (h.typed pre hp)
      (.frame C [op] pre args (results.map Translation.valueType)
        (.instr C op args _ hop hC hwf) hC (by simpa [Forall] using hwf))
      hC h.wellFormed (by simpa [Forall] using hwf)

end Itasca.Body

end

/-! ## EmptyVisitorLoop -/

section

/-!
# Body loop with the empty visitor

Proof-side views of the extracted visiting loop `code.body_loop_loop` instantiated with
`code.EmptyOpVisitor`. `Body.emptyVisitorLoop.body` drops the visitor from the loop body,
`Body.emptyVisitorLoop.body_eq` relates it to the extracted body, and `code.bodyCore` is the
visitor-free body validator.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca

/-- One iteration of the extracted loop body with the visitor argument kept only as a pass-through
value, so semantic proofs do not track the empty visitor. -/
def Body.emptyVisitorLoop.body
  (data : Slice U8) (env : metadata.Env) (type_index : U32)
  (locals : alloc.vec.Vec wasm_types.ValueType)
  (results : alloc.vec.Vec wasm_types.ValueType)
  (st : code.BodyState)
  (visitor : code.EmptyOpVisitor) :
  Result (ControlFlow (code.BodyState ×
    code.EmptyOpVisitor) (core.result.Result Unit
    error.OpError))
  := do
  let b ← alloc.vec.Vec.is_empty Global st.blocks
  if b
  then
    let i2 := Slice.len data
    if st.core.pos != i2
    then ok (done (core.result.Result.Err error.OpError.TrailingBytes))
    else ok (done (core.result.Result.Ok ()))
  else
    let r ← reader.read_byte data st.core.pos
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue (op, «end») =>
      match op with
      | 2#uscalar =>
        let (r1, st1) ←
          code.enter { st with core := { st.core with pos := «end» } }
            data
            env code.LabelKind.Block
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 3#uscalar =>
        let (r1, st1) ←
          code.enter { st with core := { st.core with pos := «end» } }
            data
            env code.LabelKind.Loop
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 4#uscalar =>
        let (r1, st1) ←
          code.enter { st with core := { st.core with pos := «end» } }
            data
            env code.LabelKind.Then
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 5#uscalar =>
        let (r1, st1) ←
          code.end_frame
            { st with core := { st.core with pos := «end» } }
            env true
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 11#uscalar =>
        let (r1, st1) ←
          code.end_frame
            { st with core := { st.core with pos := «end» } }
            env false
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 12#uscalar =>
        let (r1, st1) ←
          code.branch
            { st with core := { st.core with pos := «end» } } data
            env false
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 13#uscalar =>
        let (r1, st1) ←
          code.branch
            { st with core := { st.core with pos := «end» } } data
            env true
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 14#uscalar =>
        let (r1, st1) ←
          code.branch_table
            { st with core := { st.core with pos := «end» } } data
            env
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 15#uscalar =>
        let (r1, ois) ←
          code.pop_results { st.core with pos := «end» }
            env (signature.ResultType.Type type_index signature.TypePart.Results)
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let ois1 ← code.mark_unreachable ois
          ok (cont ({ st with core := ois1 }, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 16#uscalar =>
        let (r1, st1) ←
          code.call { st with core := { st.core with pos := «end» } }
            data
            env false
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | 17#uscalar =>
        let (r1, st1) ←
          code.call { st with core := { st.core with pos := «end» } }
            data
            env true
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (cont (st1, visitor))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.OpError) residual
          ok (done r2)
      | _ =>
        let i2 := alloc.vec.Vec.len st.core.vals
        if i2 = core.num.Usize.MAX
        then ok (done (core.result.Result.Err error.OpError.StackTooLarge))
        else
          let (r1, ois, visitor1) ←
            code.step_wasm2 code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
              { st.core with pos := «end» } data
              env { locals, results } op visitor
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            ok (cont ({ st with core := ois }, visitor1))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r2 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame error.OpError)
                residual
            ok (done r2)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.OpError) residual
      ok (done r1)

/-- The extracted loop `code.body_loop_loop` run with the empty visitor, returning only the
validation result. -/
def Body.emptyVisitorLoop
  (data : Slice U8) (env : metadata.Env) (type_index : U32)
  (st : code.BodyState)
  (locals : alloc.vec.Vec wasm_types.ValueType)
  (results : alloc.vec.Vec wasm_types.ValueType)
  (visitor : code.EmptyOpVisitor) :
  Result (core.result.Result Unit error.OpError)
  := do
  let (r, _) ← code.body_loop_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor data env
    ⟨locals, results⟩ type_index visitor st
  .ok r

/-- Only the placement of the empty visitor changes between the semantic
adapter and the extracted visiting loop. -/
theorem Body.emptyVisitorLoop.body_eq (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (st : code.BodyState) :
    code.body_loop_loop.body code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx index () st = (do
      let r ← Body.emptyVisitorLoop.body data env index ctx.locals ctx.results st ()
      .ok (match r with | .cont (s, _) => .cont ((), s) | .done result => .done (result, ()))) := by
  unfold code.body_loop_loop.body code.step_profile Body.emptyVisitorLoop.body
  simp only [code.BodyState.blocks_is_empty, Std.bind_assoc]
  congr 1
  funext b
  split
  · split <;> simp
  · simp only [Std.bind_assoc]
    congr 1
    funext r
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨opcode, pos⟩ := pair
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry, Std.bind_assoc]
      split
      all_goals simp_all only [code.enter, code.end_frame,
        code.branch, code.branch_table, code.call, Bool.false_eq_true, ↓reduceIte, Std.bind_assoc]
      all_goals first
        | (congr 1; funext pair; rcases pair with ⟨r, s⟩; cases r <;>
            simp [code.OpVisitor.on_block.default,
              code.OpVisitor.on_loop.default, code.OpVisitor.on_if.default,
              code.OpVisitor.on_else.default, code.OpVisitor.on_end.default,
              code.OpVisitor.on_br.default, code.OpVisitor.on_br_if.default,
              code.OpVisitor.on_call.default, code.OpVisitor.on_call_indirect.default,
              code.OpVisitor.on_return.default, code.visit, Std.bind_assoc,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual])
        | skip
      all_goals try (rcases s with ⟨s, v⟩; cases v; simp)
      split
      · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp only [Std.bind_assoc]
        congr 1
        funext pair
        obtain ⟨r, s, v⟩ := pair
        cases v
        cases r <;> simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- The visitor-free body validator with the loop replaced by `Body.emptyVisitorLoop`. -/
def code.bodyCore
  (data : Slice U8) (env : metadata.Env)
  (locals results : alloc.vec.Vec wasm_types.ValueType) (type_index : U32)
   :
  Result (core.result.Result Unit error.OpError)
  := do
  let i := Slice.len data
  if i > limits.MAX_FUNCTION_BYTES
  then ok (core.result.Result.Err error.OpError.BodyTooLarge)
  else
    let i1 ← lift (UScalar.cast .Usize type_index)
    let i2 := alloc.vec.Vec.len env.types
    if i1 >= i2
    then ok (core.result.Result.Err error.OpError.UnknownType)
    else
      let ft ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          wasm_types.FuncType) env.types i1
      let r ← code.check_func_type ft
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let st ←
          code.push_frame
            {
              core :=
                {
                  vals := (alloc.vec.Vec.new code.StackType),
                  ctrls := (alloc.vec.Vec.new code.Ctrl),
                  pos := 0#usize
                }
            } code.LabelKind.Body (signature.BlockType.TypeIndex type_index)
        Body.emptyVisitorLoop data env type_index st locals results ()
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.OpError) residual

end Itasca

end

end
