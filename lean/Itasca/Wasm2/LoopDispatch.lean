import Itasca.Binary.Wasm2.SyntaxUnique
import Itasca.Binary.Wasm2.DeclaredReferences
import Itasca.Support.Result
import Itasca.Wasm2.Control.Frame
import Itasca.Wasm2.EmptyVisitorLoop
import Itasca.Wasm2.TableAdapters

/-!
Sections, each formerly its own module: BodySpec, Frames, Invariant, LoopDispatch.
-/

/-! ## BodySpec -/

section

/-!
# Wasm 2.0 body contract

The contract that the body validator is proved against, stated without reference to the
validator. `Validated` says that a body is a binary-grammar instruction sequence (`BodyEncoding`),
is typed by the generated `Instrs_ok` rules (`FunctionTyped`), and satisfies the
declared-function-reference condition.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- The typing context of a function body. Return typing comes from the selected type-section
entry. The runtime's shared scalar context carries empty results because `return` is dispatched by
the Wasm 2.0 body loop itself. Function parameters are already included in locals. -/
def bodyContext (env : metadata.Env) (locals : alloc.vec.Vec wasm_types.ValueType)
    (ft : wasm_types.FuncType) : context := EnvTranslation.context env ⟨locals, ft.results⟩

/-- The context of a function body: the function label on top of `bodyContext`. -/
def functionContext (env : metadata.Env) (locals : alloc.vec.Vec wasm_types.ValueType)
    (ft : wasm_types.FuncType) : context :=
  Control.labelContext (ft.results.val.map Translate.valueType) ++ bodyContext env locals ft

/-- The instruction sequence is typed by the generated `Instrs_ok` rules from no operands to the
function's result type, with the function label in scope. -/
def FunctionTyped (env : metadata.Env) (locals : alloc.vec.Vec wasm_types.ValueType)
    (ft : wasm_types.FuncType) (ops : List instr) : Prop :=
  Instrs_ok (functionContext env locals ft)
    ops (.mk_functype (.mk_list []) (.mk_list (ft.results.val.map Translate.valueType)))

/-- The whole-body certificate used by both soundness and completeness. It contains no
validator-success premise. -/
def Validated (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) : Prop :=
  ∃ ft ops, env.types.val[index.val]? = some ft ∧ BodyEncoding data ops ∧
    FunctionTyped env locals ft ops ∧
    DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops

end Itasca.Wasm2

end

/-! ## Frames -/

section

/-!
# Typed frame zipper

The zipper that relates the extracted control stack (`code.BodyState.core.ctrls` and
`code.BodyState.blocks`) to the syntax and typing of the body read so far. A `Saved` frame records
the typed prefix of one open construct, `Spine` chains the suspended parents, and `Open` is the
control invariant. `Open.enter_child`, `Open.else_`, `Open.close` and `Open.finish_body` show how
opening a block, switching to `else`, closing a frame and closing the body maintain it.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Frames

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
  ins.map Translate.valueType ++ match form with
  | .then_ | .else_ _ _ => [.I32]
  | _ => []

/-- The types a branch to the frame carries: the parameters for `loop`, the results otherwise. -/
def Form.label (form : Form) (ins outs : List wasm_types.ValueType) : List valtype :=
  (match form with | .loop => ins | _ => outs).map Translate.valueType

/-- The typing context inside a frame: its label pushed onto the enclosing context. -/
def enter (C : context) (form : Form) (ins outs : List wasm_types.ValueType) : context :=
  Control.labelContext (form.label ins outs) ++ C

/-- The already completed material of a frame is well typed. Only an `else_` frame has any: its
`then` arm. -/
def Form.Valid (C : context) (ins outs : List wasm_types.ValueType) : Form → Prop
  | .else_ tokens ops => Emits tokens ops ∧
      Instrs_ok (enter C (.else_ tokens ops) ins outs) ops
        (.mk_functype (.mk_list (ins.map Translate.valueType))
          (.mk_list (outs.map Translate.valueType)))
  | _ => True

/-- A frame of the zipper: its runtime control entry, block type, resolved signature, form, and
the instructions, operand stack and tokens read so far. -/
structure Saved where
  ctrl : code.Ctrl
  bt : signature.BlockType
  ins : List wasm_types.ValueType
  outs : List wasm_types.ValueType
  form : Form
  ops : List instr
  vals : List code.StackType
  tokens : List Token

/-- The static facts about a frame: its control entry matches its form, its signature resolves
from its block type, and its completed material is valid and emitted by its tokens. -/
structure Header (env : metadata.Env) (C : context) (f : Saved) : Prop where
  kind : f.ctrl.kind = f.form.kind
  inputs : resolve env (Wasm2.inputs f.bt) = some f.ins
  outputs : resolve env (Wasm2.outputs f.bt) = some f.outs
  prior : f.form.Valid C f.ins f.outs
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
        ((parent.form.params parent.ins).map Translate.valueType)
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
      ((current.form.params current.ins).map Translate.valueType)
      current.ops current.ctrl.polymorphic_base current.vals ∧
    st.core.ctrls.val = parents.map Saved.ctrl ++ [current.ctrl] ∧
    st.blocks.val = parents.map Saved.bt ++ [current.bt] ∧
    st.core.vals.val = outer ++ current.vals

theorem enter_wf (C : context) (hC : wf_context C) (form : Form) (ins outs) :
    wf_context (enter C form ins outs) := Control.enter_context_wf C hC _

theorem Spine.context_wf {env root parents C outer form ins}
    (h : Spine env root parents C outer form ins) (hroot : wf_context root) :
    wf_context C := by
  induction h with
  | root => exact hroot
  | push _ _ _ _ _ _ _ _ _ _ _ ih => exact enter_wf _ ih _ _ _

theorem Spine.types {env root parents C outer form ins}
    (h : Spine env root parents C outer form ins) : C.TYPES = root.TYPES := by
  induction h with
  | root => rfl
  | push _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

theorem Spine.returns {env root parents C outer form ins}
    (h : Spine env root parents C outer form ins) : C.RETURN = root.RETURN := by
  induction h with
  | root => rfl
  | push _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

/-- The label types of a list of frames, innermost first. -/
def labels (frames : List Saved) : List resulttype :=
  frames.reverse.map (fun f => .mk_list (f.form.label f.ins f.outs))

theorem Spine.labels {env root parents C outer form ins}
    (h : Spine env root parents C outer form ins) : C.LABELS = labels parents ++ root.LABELS := by
  induction h with
  | root => simp [Frames.labels]
  | push parents C outer parent child ins spine header base resume notBody ih =>
    simp [enter, Control.labelContext_labels, Frames.labels, List.reverse_append, ih]

theorem Header.target {env C f} (h : Header env C f) :
    resolve env (target f.ctrl.kind f.bt) =
      some (match f.form with | .loop => f.ins | _ => f.outs) := by
  rw [h.kind]
  cases hf : f.form <;> simp only [Form.kind, Wasm2.target]
  all_goals first | exact h.inputs | exact h.outputs

/-- An omitted else is the identity arm. It is valid for a nonempty indexed
signature too, provided its resolved parameters and results are equal. -/
inductive Closed : Form → signature.BlockType → List instr → instr → Prop where
  | block (bt ops) : Closed .block bt ops (.BLOCK (blockType bt) ops)
  | loop (bt ops) : Closed .loop bt ops (.LOOP (blockType bt) ops)
  | then_ (bt ops) : Closed .then_ bt ops (.IFELSE (blockType bt) ops [])
  | else_ (bt thenTokens thenOps ops) :
      Closed (.else_ thenTokens thenOps) bt ops (.IFELSE (blockType bt) thenOps ops)

theorem Closed.not_body {form bt ops op} (closed : Closed form bt ops op) : form ≠ .body := by
  cases closed <;> simp

theorem Closed.wf {form bt ops op} (closed : Closed form bt ops op)
    (C : context) (ins outs) (hprior : form.Valid C ins outs)
    (hops : Forall wf_instr ops) : wf_instr op := by
  cases closed with
  | block => exact .instr_case_4 _ _ (blockType_wf _) hops
  | loop => exact .instr_case_5 _ _ (blockType_wf _) hops
  | then_ => exact .instr_case_6 _ _ _ (blockType_wf _) hops (by simp [Forall])
  | else_ => exact .instr_case_6 _ _ _ (blockType_wf _) hprior.1.wellFormed hops

theorem Closed.typed {env C f op}
    (closed : Closed f.form f.bt f.ops op) (hC : wf_context C)
    (htypes : C.TYPES = env.types.val.map EnvTranslation.funcType)
    (header : Header env C f)
    (htyped : TypedPrefix (enter C f.form f.ins f.outs)
      ((f.form.params f.ins).map Translate.valueType) f.ops f.ctrl.polymorphic_base f.vals)
    (hresults : Sequence.Realizes f.ctrl.polymorphic_base f.vals (f.outs.map Translate.valueType))
    (hthen : f.form = .then_ → f.ins = f.outs) :
    Instr_ok C op (.mk_functype (.mk_list (f.form.args f.ins))
      (.mk_list (f.outs.map Translate.valueType))) := by
  have hbt := blockType_ok env C hC htypes f.bt f.ins f.outs header.inputs header.outputs
  have hbody := htyped.typed _ hresults
  have hwf := closed.wf C f.ins f.outs header.prior htyped.wellFormed
  generalize hf : f.form = form at closed hbody hthen hwf ⊢
  cases closed with
  | block =>
    simpa [Form.args] using Instr_ok.block C _ _ _ _ hbt hbody hC hwf (Control.labelContext_wf _)
  | loop =>
    simpa [Form.args] using Instr_ok.loop C _ _ _ _ hbt hbody hC hwf (Control.labelContext_wf _)
  | then_ =>
    have he := hthen rfl
    have hempty : Instrs_ok (enter C .then_ f.ins f.outs) []
        (.mk_functype (.mk_list (f.ins.map Translate.valueType))
          (.mk_list (f.outs.map Translate.valueType))) := by
      rw [he]
      simpa using Instrs_ok.frame _ [] (f.outs.map Translate.valueType) [] []
        (.empty _ (enter_wf C hC _ _ _)) (enter_wf C hC _ _ _) (by simp [Forall])
    exact .if C _ _ _ _ _ hbt hbody hempty hC hwf (Control.labelContext_wf _)
  | else_ bt tokens ops body =>
    have hp := header.prior
    rw [hf] at hp
    exact .if C _ _ _ _ _ hbt hp.2 hbody hC hwf (Control.labelContext_wf _)

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

theorem Closed.emits {form bt ops op tokens} (closed : Closed form bt ops op)
    (C : context) (ins outs) (hprior : form.Valid C ins outs) (hemits : Emits tokens ops) :
    Emits (form.opening bt ++ tokens ++ [.end_]) [op] := by
  cases closed with
  | block => simpa [Form.opening] using Emits.block bt .nil hemits
  | loop => simpa [Form.opening] using Emits.loop bt .nil hemits
  | then_ => simpa [Form.opening] using Emits.ifEnd bt .nil hemits
  | else_ => simpa [Form.opening] using Emits.ifElse bt .nil hprior.1 hemits

/-- Closing a child resumes the parent's own input-to-stack derivation. -/
theorem Open.close {env root st st' parents current}
    (h : Open env root st parents current) (hroot : wf_context root)
    (htypes : root.TYPES = env.types.val.map EnvTranslation.funcType) (op : instr)
    (closed : Closed current.form current.bt current.ops op)
    (hresults : Sequence.Realizes current.ctrl.polymorphic_base current.vals
      (current.outs.map Translate.valueType))
    (hthen : current.form = .then_ → current.ins = current.outs)
    (hctrls : st'.core.ctrls.val = parents.map Saved.ctrl)
    (hblocks : st'.blocks.val = parents.map Saved.bt)
    (hvals : st'.core.vals.val = st.core.vals.val.take current.ctrl.value_stack_base.val ++
      current.outs.map code.StackType.Val) :
    ∃ grandparents parent, parents = grandparents ++ [parent] ∧
      let resumed := { parent with
        ops := parent.ops ++ [op]
        vals := parent.vals ++ current.outs.map code.StackType.Val
        tokens := parent.tokens ++ current.trace ++ [.end_] }
      Open env root st' grandparents resumed ∧
        trace grandparents resumed = trace parents current ++ [.end_] := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := h
  have hC := spine.context_wf hroot
  have hop := closed.typed hC (spine.types.trans htypes) header typed hresults hthen
  have hwf := closed.wf C current.ins current.outs header.prior typed.wellFormed
  have hemit := closed.emits C current.ins current.outs header.prior header.emits
  generalize hform : current.form = form at spine
  cases spine with
  | root => exact False.elim (closed.not_body hform)
  | push gps parentC outer parent child ins spine pheader pbase resume notBody =>
    refine ⟨gps, parent, rfl, ?_, ?_⟩
    · refine ⟨parentC, outer, spine, ?_, pbase,
        resume.finish hC op current.outs hwf (by simpa [hform] using hop),
        by simpa using hctrls, by simpa using hblocks, ?_⟩
      · exact ⟨pheader.kind, pheader.inputs, pheader.outputs,
          pheader.prior, by
            simpa [Saved.trace, List.append_assoc] using pheader.emits.append hemit⟩
      · have htake : st.core.vals.val.take current.ctrl.value_stack_base.val =
            outer ++ parent.vals := by rw [vals, base, List.take_left]
        simpa [htake, List.append_assoc] using hvals
    · simp [trace, Saved.trace, List.flatMap_append, List.append_assoc]

theorem Spine.change_form {env root parents C outer before after ins}
    (h : Spine env root parents C outer before ins)
    (hargs : before.args ins = after.args ins)
    (hbody : before = .body ↔ after = .body) : Spine env root parents C outer after ins := by
  cases h with
  | root => rw [hbody.mp rfl]; exact .root _
  | push ps pc out parent child ins spine header base resume notBody =>
    exact .push ps pc out parent after ins spine header base
      (by simpa [hargs] using resume) (fun heq => notBody (hbody.mpr heq))

/-- The frame after `else`: the `then` arm is saved in the form and the arm restarts with the
block parameters. -/
def Saved.nextElse (current : Saved) : Saved :=
  { current with
    ctrl := { current.ctrl with kind := .Else, polymorphic_base := false }
    form := .else_ current.tokens current.ops
    ops := [], vals := current.ins.map code.StackType.Val, tokens := [] }

/-- Else starts with the complete parameter vector and a reachable base. -/
theorem Open.else_ {env root st st' parents current}
    (h : Open env root st parents current) (hroot : wf_context root)
    (hform : current.form = .then_)
    (hresults : Sequence.Realizes current.ctrl.polymorphic_base current.vals
      (current.outs.map Translate.valueType))
    (hctrls : st'.core.ctrls.val = parents.map Saved.ctrl ++ [current.nextElse.ctrl])
    (hblocks : st'.blocks = st.blocks)
    (hvals : st'.core.vals.val = st.core.vals.val.take current.ctrl.value_stack_base.val ++
      current.ins.map code.StackType.Val) :
    Open env root st' parents current.nextElse ∧
      trace parents current.nextElse = trace parents current ++ [.else_] := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := h
  have hC := spine.context_wf hroot
  constructor
  · refine ⟨C, outer, spine.change_form (by simp [hform, Saved.nextElse, Form.args])
      (by simp [hform, Saved.nextElse]), ?_, base, ?_, hctrls, ?_, ?_⟩
    · exact ⟨rfl, header.inputs, header.outputs,
        ⟨header.emits, by
          simpa [hform, Saved.nextElse, enter, Form.label, Form.params]
            using typed.typed _ hresults⟩, .nil⟩
    · exact TypedPrefix.start _ (enter_wf C hC _ _ _) current.ins
    · simpa [hblocks, Saved.nextElse] using blocks
    · simpa [vals, base, Saved.nextElse] using hvals
  · simp [trace, Saved.trace, Saved.nextElse, hform, Form.opening, List.append_assoc]

/-- A newly opened frame with the given stack base and an empty body. -/
def Saved.fresh (base : Usize) (form : Form) (bt : signature.BlockType)
    (ins outs : List wasm_types.ValueType) : Saved :=
  { ctrl := ⟨form.kind, bt, base, false⟩, bt, ins, outs, form,
    ops := [], vals := (form.params ins).map code.StackType.Val, tokens := [] }

/-- The forms that `block`, `loop` and `if` open. -/
def Form.Initial (form : Form) : Prop := form = .block ∨ form = .loop ∨ form = .then_

/-- Opening a `block`, `loop` or `if` pushes a fresh frame and keeps `Open`, extending the trace
by the form's opening token. -/
theorem Open.enter_child {env root st st' parents current}
    (h : Open env root st parents current) (hroot : wf_context root)
    (form : Form) (bt : signature.BlockType) (ins outs : List wasm_types.ValueType)
    (hi : form.Initial) (hin : resolve env (inputs bt) = some ins)
    (hout : resolve env (outputs bt) = some outs) (base : Usize)
    (remaining : List code.StackType)
    (hpop : ∀ ts, Sequence.Realizes current.ctrl.polymorphic_base remaining ts →
      Sequence.Realizes current.ctrl.polymorphic_base current.vals (ts ++ form.args ins))
    (hbase : base.val = current.ctrl.value_stack_base.val + remaining.length)
    (hctrls : st'.core.ctrls.val = st.core.ctrls.val ++ [(Saved.fresh base form bt ins outs).ctrl])
    (hblocks : st'.blocks.val = st.blocks.val ++ [bt])
    (hvals : st'.core.vals.val = st.core.vals.val.take current.ctrl.value_stack_base.val ++
      remaining ++ ins.map code.StackType.Val) :
    Open env root st' (parents ++ [{ current with vals := remaining }])
      (Saved.fresh base form bt ins outs) ∧
      trace (parents ++ [{ current with vals := remaining }]) (Saved.fresh base form bt ins outs) =
        trace parents current ++ form.opening bt := by
  obtain ⟨C, outer, spine, header, pbase, typed, ctrls, blocks, vals⟩ := h
  have hC := spine.context_wf hroot
  have hn : form ≠ .body := by rcases hi with rfl | rfl | rfl <;> simp
  have hp : form.params ins = ins := by rcases hi with rfl | rfl | rfl <;> rfl
  constructor
  · refine ⟨enter C current.form current.ins current.outs, outer ++ remaining,
      .push parents C outer { current with vals := remaining } form ins spine
        ⟨header.kind, header.inputs, header.outputs, header.prior, header.emits⟩
        pbase (ResumePrefix.after_pop typed hpop) hn, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨rfl, hin, hout, ?_, .nil⟩
      rcases hi with rfl | rfl | rfl <;> trivial
    · simpa [Saved.fresh, pbase] using hbase
    · exact TypedPrefix.start _ (enter_wf _ (enter_wf C hC _ _ _) _ _ _) _
    · simpa [ctrls, List.append_assoc] using hctrls
    · simpa [blocks, Saved.fresh, List.append_assoc] using hblocks
    · simpa [vals, pbase, Saved.fresh, hp, List.append_assoc] using hvals
  · simp [trace, Saved.trace, Saved.fresh, List.flatMap_append, List.append_assoc]

/-- The state with a single fresh body frame satisfies `Open`. -/
theorem Open.start (env : metadata.Env) (root : context) (hroot : wf_context root)
    (st : code.BodyState) (bt : signature.BlockType) (ins outs : List wasm_types.ValueType)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (hctrls : st.core.ctrls.val = [(Saved.fresh 0#usize .body bt ins outs).ctrl])
    (hblocks : st.blocks.val = [bt]) (hvals : st.core.vals.val = []) :
    Open env root st [] (Saved.fresh 0#usize .body bt ins outs) := by
  refine ⟨root, [], .root _, ⟨rfl, hin, hout, trivial, .nil⟩, rfl,
    TypedPrefix.start _ (enter_wf root hroot _ _ _) [], hctrls, hblocks, hvals⟩

theorem Spine.body {env root parents C outer ins}
    (h : Spine env root parents C outer .body ins) :
    parents = [] ∧ C = root ∧ outer = [] := by
  cases h with
  | root => exact ⟨rfl, rfl, rfl⟩
  | push _ _ _ _ _ _ _ _ _ _ notBody => exact False.elim (notBody rfl)

/-- A body frame whose operands realize the result type is the only frame, its tokens form a
body, and its instructions are typed by `Instrs_ok`. -/
theorem Open.finish_body {env root st parents current}
    (h : Open env root st parents current) (hform : current.form = .body)
    (hresults : Sequence.Realizes current.ctrl.polymorphic_base current.vals
      (current.outs.map Translate.valueType)) :
    parents = [] ∧ BodyTokens (trace parents current ++ [.end_]) current.ops ∧
      Instrs_ok (enter root .body current.ins current.outs) current.ops
        (.mk_functype (.mk_list []) (.mk_list (current.outs.map Translate.valueType))) := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := h
  rw [hform] at spine
  obtain ⟨rfl, rfl, rfl⟩ := spine.body
  refine ⟨rfl, ⟨current.tokens, ?_, header.emits⟩, ?_⟩
  · simp [trace, Saved.trace, hform, Form.opening]
  · simpa [hform, Form.params] using typed.typed _ hresults

theorem Spine.bounds {env root parents C outer form ins}
    (h : Spine env root parents C outer form ins) :
    (parents.map Saved.ctrl).Pairwise (fun c d => c.value_stack_base.val ≤ d.value_stack_base.val) ∧
      ∀ c ∈ parents.map Saved.ctrl, c.value_stack_base.val ≤ outer.length := by
  induction h with
  | root => simp
  | push parents C outer parent child ins spine header base resume notBody ih =>
    constructor
    · simp only [List.map_append, List.map_singleton, List.pairwise_append]
      exact ⟨ih.1, by simp, by simpa [base] using ih.2⟩
    · intro c hc
      simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · have := ih.2 c hc
        simp only [List.length_append]
        omega
      · simp [base]

/-- `Open` implies the structural `Shape` invariant of the body state. -/
theorem Open.shape {env root st parents current} (h : Open env root st parents current) :
    Shape st := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := h
  obtain ⟨ordered, bounded⟩ := spine.bounds
  refine ⟨⟨?_, ?_⟩, by simp [blocks, ctrls]⟩
  · rw [ctrls, List.pairwise_append]
    exact ⟨ordered, by simp, by simpa [base] using bounded⟩
  · intro c hc
    rw [ctrls] at hc
    rcases List.mem_append.mp hc with hc | hc
    · have := bounded c hc
      simp only [vals, List.length_append]
      omega
    · have heq : c = current.ctrl := by simpa using hc
      simp [heq, base, vals]

theorem Spine.headers {env root parents C outer form ins}
    (h : Spine env root parents C outer form ins) :
    ∀ f ∈ parents, ∃ D, Header env D f := by
  induction h with
  | root => simp
  | push parents C outer parent child ins spine header base resume notBody ih =>
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact ih f hf
    · have he : f = parent := by simpa using hf
      subst f
      exact ⟨C, header⟩

/-- Physical reverse-depth lookup resolves to exactly the generated label
vector, including loop parameters and invalid depths. -/
theorem resolved_labelAt (env : metadata.Env) (st : code.BodyState) (frames : List Saved)
    (hc : st.core.ctrls.val = frames.map Saved.ctrl)
    (hb : st.blocks.val = frames.map Saved.bt)
    (hh : ∀ f ∈ frames, ∃ C, Header env C f) (depth : Nat) :
    ((labelAt st depth).bind (resolve env)).map
      (fun ts => list.mk_list (ts.map Translate.valueType)) = (labels frames)[depth]? := by
  by_cases hd : depth < frames.length
  · have hi : frames.length - 1 - depth < frames.length := by omega
    obtain ⟨C, header⟩ := hh _ (List.getElem_mem hi)
    simp only [labelAt, hb, List.length_map, hd, ↓reduceIte, hc,
      List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some]
    change (resolve env (target frames[frames.length - 1 - depth].ctrl.kind
      frames[frames.length - 1 - depth].bt)).map _ = _
    rw [header.target]
    simp only [Option.map_some, labels, List.getElem?_map, List.getElem?_reverse hd,
      List.getElem?_eq_getElem (by omega : frames.length - 1 - depth < frames.length),
      Option.map_some, Form.label]
  · have hout : (labels frames).length ≤ depth := by simp [labels]; omega
    simp [labelAt, hb, hd, List.getElem?_eq_none hout]

/-- Resolving a branch depth in the body state gives the label types of the zipper's frames. -/
theorem Open.labels {env root st parents current}
    (h : Open env root st parents current) (depth : Nat) :
    ((labelAt st depth).bind (resolve env)).map
      (fun ts => list.mk_list (ts.map Translate.valueType)) =
        (labels (parents ++ [current]))[depth]? := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := h
  apply resolved_labelAt env st (parents ++ [current])
    (by simpa using ctrls) (by simpa using blocks) _ depth
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · exact spine.headers f hf
  · have he : f = current := by simpa using hf
    subst f
    exact ⟨C, header⟩

theorem Spine.matches {env root parents C outer form ins ctx}
    (h : Spine env root parents C outer form ins) (hr : EnvTranslation.Matches env ctx root) :
    EnvTranslation.Matches env ctx C := by
  induction h with
  | root => exact hr
  | push _ _ _ _ _ _ _ _ _ _ _ ih => exact ih.enter _

/-- The outermost descriptor stays fixed while nested frames are opened,
advanced, switched to else, and closed. -/
def bodyType (parents : List Saved) (current : Saved) : Option signature.BlockType :=
  ((parents ++ [current]).head?).map Saved.bt

@[simp]
theorem bodyType_root (current : Saved) : bodyType [] current = some current.bt := rfl

/-- The frame after one more instruction, with the given operand stack and polymorphism flag. -/
def Saved.advance (current : Saved) (token : Token) (op : instr)
    (poly : Bool) (vals : List code.StackType) : Saved :=
  { current with
    ctrl := { current.ctrl with polymorphic_base := poly }
    ops := current.ops ++ [op]
    vals := vals
    tokens := current.tokens ++ [token] }

theorem bodyType_advance (parents : List Saved) (current : Saved) (token : Token)
    (op : instr) (poly : Bool) (vals : List code.StackType) :
    bodyType parents (current.advance token op poly vals) = bodyType parents current := by
  cases parents <;> rfl

theorem bodyType_else (parents : List Saved) (current : Saved) :
    bodyType parents current.nextElse = bodyType parents current := by
  cases parents <;> rfl

theorem bodyType_enter (parents : List Saved) (current child : Saved) (remaining) :
    bodyType (parents ++ [{ current with vals := remaining }]) child = bodyType parents current := by
  cases parents <;> rfl

theorem bodyType_close (grandparents : List Saved) (parent current : Saved) (op : instr) :
    bodyType grandparents { parent with
      ops := parent.ops ++ [op], vals := parent.vals ++ current.outs.map code.StackType.Val,
      tokens := parent.tokens ++ current.trace ++ [.end_] } =
        bodyType (grandparents ++ [parent]) current := by
  cases grandparents <;> rfl

/-- `Open` does not depend on the byte cursor. -/
theorem Open.with_pos {env root st parents current} (h : Open env root st parents current)
    (pos : Usize) : Open env root { st with core := { st.core with pos := pos } } parents current := h

end Itasca.Wasm2.Frames

end

/-! ## Invariant -/

section

/-!
# Body loop invariant

The invariant of the extracted body loop. `State` says that the loop state is a running typed
frame zipper (`Frames.Open`) or a completed typed body, with exact provenance for the consumed
bytes. `Pending` is the state just after an opcode byte is read, and `Pending.After` is the postcondition that every
per-opcode handler proves. `Pending.finish_body` and `Pending.append_result` are the shared steps
for closing the body and appending results.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Implementation limits on the body size, the byte cursor and the number of open frames. -/
structure Bounds (data : Slice U8) (st : code.BodyState) : Prop where
  size : data.length ≤ limits.MAX_FUNCTION_BYTES.val
  pos : st.core.pos.val ≤ data.length
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

theorem State.bounds {data env locals index st} (h : State data env locals index st) :
    Bounds data st := by cases h <;> assumption

theorem State.shape {data env locals index st} (h : State data env locals index st) :
    Shape st := by
  cases h with
  | running ft parents current hi bounds ho hb hc hd => exact ho.shape
  | closed _ _ _ _ _ hc hb _ _ _ _ =>
    exact ⟨⟨by simp [hc], by simp [hc]⟩, by simp [hc, hb]⟩

theorem State.finished {data env locals index st}
    (h : State data env locals index st)
    (hblocks : st.blocks.val = []) (hpos : st.core.pos.val = data.length) :
    Validated data env locals index := by
  cases h with
  | running ft parents current _ _ ho _ _ _ =>
    obtain ⟨_, _, _, _, _, _, _, hb, _⟩ := ho
    simp [hblocks] at hb
  | closed ft ops tokens hi _ _ _ ht htyped hc hd =>
    exact ⟨ft, ops, hi, ⟨tokens, st.core.pos, hc, hpos, ht⟩, htyped, (ht.declared_iff _).mp hd⟩

/-- The loop's initial body state: one body frame for the function type at `index`. -/
def initial (index : U32) : code.BodyState :=
  { core := ⟨alloc.vec.Vec.new _,
      alloc.vec.Vec.from [⟨.Body, .TypeIndex index, 0#usize, false⟩] (by scalar_tac), 0#usize⟩ }

/-- The initial state satisfies `State` for a body within the size limit. -/
theorem State.start (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType)
    (index : U32) (ft : wasm_types.FuncType) (hi : env.types.val[index.val]? = some ft)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val) :
    State data env locals index (initial index) := by
  apply State.running (initial index) ft []
    (Frames.Saved.fresh 0#usize .body (.TypeIndex index) ft.params.val ft.results.val) hi
  · constructor <;> simp [initial, hsize]
  · apply Frames.Open.start env _ (EnvTranslation.context_wf env ⟨locals, ft.results⟩)
    · simp [resolve, inputs, hi]
    · simp [resolve, outputs, hi]
    · rfl
    · rfl
    · rfl
  · rfl
  · simpa [Frames.trace, Frames.Saved.trace, Frames.Saved.fresh, Frames.Form.opening, initial]
      using Consumed.nil (data := data) 0#usize (by simp)
  · simp [Frames.trace, Frames.Saved.trace, Frames.Saved.fresh, Frames.Form.opening]

/-- The opcode has been consumed and passed the profile's opcode filter, but its immediate is
still arbitrary. -/
structure Pending (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (st : code.BodyState) where
  start : Usize
  ft : wasm_types.FuncType
  parents : List Frames.Saved
  current : Frames.Saved
  signature : env.types.val[index.val]? = some ft
  size : data.length ≤ limits.MAX_FUNCTION_BYTES.val
  opened : Frames.Open env (bodyContext env locals ft) st parents current
  bodyType : Frames.bodyType parents current = some (.TypeIndex index)
  consumed : Consumed data 0#usize (Frames.trace parents current) start
  declared : TokensDeclared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) (Frames.trace parents current)
  inbounds : start.val < data.length
  pos : st.core.pos.val = start.val + 1
  ctrls : st.blocks.val.length ≤ start.val + 1

/-- A running state with bytes left yields a `Pending` after reading one opcode byte that passes
the profile's opcode filter. -/
theorem State.pending {data env locals index st}
    (h : State data env locals index st)
    (hblocks : st.blocks.val ≠ []) (hpos : st.core.pos.val < data.length)
    (next : Usize) (hnext : next.val = st.core.pos.val + 1) :
    ∃ p : Pending data env locals index { st with core := { st.core with pos := next } },
      p.start = st.core.pos := by
  cases h with
  | closed _ _ _ _ _ _ hb _ _ _ _ => exact False.elim (hblocks hb)
  | running ft parents current hi bounds ho hbody hc hd =>
    exact ⟨⟨st.core.pos, ft, parents, current, hi, bounds.size, ho.with_pos next, hbody,
      hc, hd, hpos, hnext, bounds.ctrls⟩, rfl⟩

/-- The postcondition of one opcode step: the resulting state satisfies `State` and its cursor has
advanced within the data. -/
def Pending.After {data env locals index st} (_ : Pending data env locals index st)
    (s : code.BodyState) : Prop :=
  State data env locals index s ∧ st.core.pos.val ≤ s.core.pos.val ∧
    s.core.pos.val ≤ data.length

theorem Pending.running_after {data env locals index st}
    (p : Pending data env locals index st)
    (s : code.BodyState) (parents : List Frames.Saved) (current : Frames.Saved)
    (token : Token) (encoded : At data p.start token s.core.pos)
    (ho : Frames.Open env (bodyContext env locals p.ft) s parents current)
    (hb : Frames.bodyType parents current = some (.TypeIndex index))
    (ht : Frames.trace parents current = Frames.trace p.parents p.current ++ [token])
    (hc : s.blocks.val.length ≤ st.blocks.val.length + 1)
    (hd : token.Declared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) := by
      simp [Token.Declared, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) : p.After s := by
  have hs := encoded.span
  have hp := p.pos
  have hbnd := p.ctrls
  refine ⟨.running s p.ft parents current p.signature
    ⟨p.size, hs.2, by omega⟩ ho hb ?_ ?_, by omega, hs.2⟩
  · rw [ht]
    exact .snoc p.consumed encoded
  · rw [ht, tokensDeclared_append, tokensDeclared_singleton]
    exact ⟨p.declared, hd⟩

theorem Pending.closed_after {data env locals index st}
    (p : Pending data env locals index st)
    (s : code.BodyState) (ops : List instr) (encoded : At data p.start .end_ s.core.pos)
    (hc : s.core.ctrls.val = []) (hb : s.blocks.val = [])
    (ht : BodyTokens (Frames.trace p.parents p.current ++ [.end_]) ops)
    (htyped : FunctionTyped env locals p.ft ops) : p.After s := by
  have hs := encoded.span
  have hp := p.pos
  exact ⟨.closed s p.ft ops _ p.signature ⟨p.size, hs.2, by simp [hb]⟩ hc hb ht htyped
    (.snoc p.consumed encoded) (by simpa [Token.Declared] using p.declared), by omega, hs.2⟩

/-- Closing the root frame recovers the result vector selected by the actual
function type index, without treating function parameters as operands. -/
theorem Pending.finish_body {data env locals index st}
    (p : Pending data env locals index st)
    (s : code.BodyState) (encoded : At data p.start .end_ s.core.pos)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0B#u8)
    (hform : p.current.form = .body)
    (hresults : Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals
      (p.current.outs.map Translate.valueType))
    (hc : s.core.ctrls.val = []) (hb : s.blocks.val = []) : p.After s := by
  obtain ⟨hparents, htokens, htyped⟩ := p.opened.finish_body hform hresults
  have hbt : p.current.bt = .TypeIndex index := by simpa [hparents] using p.bodyType
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have hr : p.current.outs = p.ft.results.val := by
    have ho := header.outputs
    simpa [hbt, outputs, resolve, p.signature] using ho.symm
  apply p.closed_after s p.current.ops encoded hc hb htokens
  · simpa [FunctionTyped, functionContext, Frames.enter, Frames.Form.label, hr] using htyped

/-- Shared leaf preservation uses arbitrary frame inputs, while retaining the
same descriptor and exact byte provenance. Calls may append multiple values. -/
theorem Pending.append_result {data env locals index st}
    (p : Pending data env locals index st)
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer
      p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (s : code.BodyState) (op : instr) (poly : Bool) (newVals : List code.StackType)
    (hwf : wf_instr op) (encoded : At data p.start (.plain op) s.core.pos)
    (typed : TypedPrefix (Frames.enter C p.current.form p.current.ins p.current.outs)
      ((p.current.form.params p.current.ins).map Translate.valueType)
      (p.current.ops ++ [op]) poly newVals)
    (hc : s.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++
      [{ p.current.ctrl with polymorphic_base := poly }])
    (hb : s.blocks.val = p.parents.map Frames.Saved.bt ++ [p.current.bt])
    (hv : s.core.vals.val = outer ++ newVals)
    (hdecl : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) op := by
      simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) : p.After s := by
  refine p.running_after s p.parents (p.current.advance (.plain op) op poly newVals)
    (.plain op) encoded ?_ ?_ ?_ ?_ hdecl
  · exact ⟨C, outer, spine, ⟨header.kind, header.inputs, header.outputs,
      header.prior, .simple header.emits (.plain op hwf)⟩, base, typed, hc, hb, hv⟩
  · simpa [Frames.bodyType_advance] using p.bodyType
  · simp [Frames.trace, Frames.Saved.trace, Frames.Saved.advance, List.append_assoc]
  · obtain ⟨_, _, _, _, _, _, _, hblocks, _⟩ := p.opened
    simp [hb, hblocks]

end Itasca.Wasm2

namespace Itasca

/-- `Wasm2.initial` is exactly the state `code.push_frame` builds for the body frame. -/
theorem code.push_frame.initial (index : U32) :
    code.push_frame
      { core := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _, 0#usize⟩ } .Body (.TypeIndex index) =
      .ok (Wasm2.initial index) := by
  simp [code.push_frame, Wasm2.initial, alloc.vec.Vec.push, U32.max, U32.numBits]
  rfl

end Itasca

end

/-! ## LoopDispatch -/

section

/-!
# Opcode dispatch in the body loop

Proof-side view of one iteration of the extracted body loop with the empty visitor. `step` is
the dispatch on one opcode, `loopBody` the whole iteration, and `loopBody_eq` unfolds the
iteration into the end-of-body check, `reader.read_byte` and `step`.
-/

open Aeneas Aeneas.Std Result

namespace Itasca.Wasm2

/-- The return arm of the extracted loop, with its state exposed for proofs. -/
def returnStep (st : code.BodyState) (env : metadata.Env) (index : U32) :
    Result (core.result.Result Unit error.OpError × code.BodyState) := do
  let (r, ois) ← code.pop_results st.core env (.Type index .Results)
  match r with
  | .Err e => .ok (.Err e, { st with core := ois })
  | .Ok () =>
    let ois ← code.mark_unreachable ois
    .ok (.Ok (), { st with core := ois })

/-- Proof adapter for one opcode of the extracted body loop . Its
exact factorization is checked by `loopBody_eq`; it is not a separate validity judgment. -/
def step (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (opcode : U8) :
    Result (core.result.Result Unit error.OpError × code.BodyState) :=
  match opcode with
  | 2#uscalar => code.enter st data env .Block
  | 3#uscalar => code.enter st data env .Loop
  | 4#uscalar => code.enter st data env .Then
  | 5#uscalar => code.end_frame st env true
  | 11#uscalar => code.end_frame st env false
  | 12#uscalar => code.branch st data env false
  | 13#uscalar => code.branch st data env true
  | 14#uscalar => code.branch_table st data env
  | 15#uscalar => returnStep st env index
  | 16#uscalar => code.call st data env false
  | 17#uscalar => code.call st data env true
  | _ =>
    if alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX then
      .ok (.Err .StackTooLarge, st)
    else do
      let (r, ois, _) ← code.step_wasm2 code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
        st.core data env ctx opcode ()
      .ok (r, { st with core := ois })

/-- The extracted body loop with the empty visitor. -/
abbrev run (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (st : code.BodyState) :=
  Wasm2.emptyVisitorLoop data env index st ctx.locals ctx.results ()

/-- One iteration of `run`. -/
abbrev loopBody (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (st : code.BodyState) :=
  Wasm2.emptyVisitorLoop.body data env index ctx.locals ctx.results st ()

/-- The loop control flow after one opcode: continue on success and stop with the error otherwise. -/
def continueStep (r : core.result.Result Unit error.OpError × code.BodyState) :
    ControlFlow (code.BodyState × code.EmptyOpVisitor) (core.result.Result Unit error.OpError) :=
  match r.1 with
  | .Ok () => .cont (r.2, ())
  | .Err e => .done (.Err e)

/-- One loop iteration stops at the end of the body (with `TrailingBytes` if bytes remain) and
otherwise reads an opcode and runs `step`. -/
theorem loopBody_eq (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (st : code.BodyState) :
    loopBody data env ctx index st =
      if st.blocks.val = [] then
        .ok (.done (if st.core.pos = Slice.len data then .Ok () else .Err .TrailingBytes))
      else (do
        let r ← reader.read_byte data st.core.pos
        match r with
        | .Err e => .ok (.done (.Err e))
        | .Ok (opcode, pos) =>
          let r ← step { st with core := { st.core with pos := pos } } data env ctx index opcode
          .ok (continueStep r)) := by
  unfold loopBody Wasm2.emptyVisitorLoop.body
  simp only [alloc.vec.Vec.is_empty, bind_ok, List.isEmpty_iff]
  split
  · by_cases hp : st.core.pos = Slice.len data
    · simp [hp]
    · simp [hp]
  · rename_i hn
    congr 1
    funext r
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨op, pos⟩ := pair
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.bind_assoc]
      unfold step
      split
      all_goals first
        | (congr 1; funext pair; obtain ⟨r, s⟩ := pair; cases r <;> simp [continueStep,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual])
        | skip
      · unfold returnStep
        simp only [Std.bind_assoc]
        congr 1
        funext pair
        obtain ⟨r, s⟩ := pair
        cases r <;> simp [continueStep,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · split
        · simp [continueStep]
        · simp only [Std.bind_assoc]
          congr 1
          funext pair
          obtain ⟨r, s, v⟩ := pair
          cases v
          cases r <;> simp [continueStep,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Wasm2

end
