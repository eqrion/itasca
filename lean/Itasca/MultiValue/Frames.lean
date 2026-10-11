import Itasca.MultiValue.Binary
import Itasca.MultiValue.Control
import Itasca.MultiValue.Prefix

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.Frames

inductive Form where
  | body | block | loop | then_
  | else_ (thenTokens : List Token) (thenOps : List instr)

def Form.kind : Form → code.LabelKind
  | .body => .Body
  | .block => .Block
  | .loop => .Loop
  | .then_ => .Then
  | .else_ _ _ => .Else

/-- Function parameters live in locals; all nested constructs start with
their declared block parameters on the operand stack. -/
def Form.params (form : Form) (ins : List types.ValueType) : List types.ValueType :=
  match form with
  | .body => []
  | _ => ins

def Form.args (form : Form) (ins : List types.ValueType) : List valtype :=
  ins.map Translate.valueType ++ match form with
  | .then_ | .else_ _ _ => [.I32]
  | _ => []

def Form.label (form : Form) (ins outs : List types.ValueType) : List valtype :=
  (match form with | .loop => ins | _ => outs).map Translate.valueType

def enter (C : context) (form : Form) (ins outs : List types.ValueType) : context :=
  Control.labelContext (form.label ins outs) ++ C

def Form.Valid (C : context) (ins outs : List types.ValueType) : Form → Prop
  | .else_ tokens ops => Emits tokens ops ∧
      Instrs_ok (enter C (.else_ tokens ops) ins outs) ops
        (.mk_functype (.mk_list (ins.map Translate.valueType))
          (.mk_list (outs.map Translate.valueType)))
  | _ => True

structure Saved where
  ctrl : code.Ctrl
  bt : signature.BlockType
  ins : List types.ValueType
  outs : List types.ValueType
  form : Form
  ops : List instr
  vals : List code.StackType
  tokens : List Token

structure Header (env : module.Env) (C : context) (f : Saved) : Prop where
  kind : f.ctrl.kind = f.form.kind
  placeholder : f.ctrl.block_type = .Empty
  inputs : resolve env (MultiValue.inputs f.bt) = some f.ins
  outputs : resolve env (MultiValue.outputs f.bt) = some f.outs
  prior : f.form.Valid C f.ins f.outs
  emits : Emits f.tokens f.ops

/-- Suspended frames retain typing from their own input vector and remember
the child arguments removed from the concrete operand stack. -/
inductive Spine (env : module.Env) (root : context) :
    List Saved → context → List code.StackType → Form → List types.ValueType → Prop where
  | root (ins) : Spine env root [] root [] .body ins
  | push (parents : List Saved) (C : context) (outer : List code.StackType)
      (parent : Saved) (child : Form) (ins : List types.ValueType)
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
def Open (env : module.Env) (root : context) (st : code.BodyState)
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
  cases hf : f.form <;> simp only [Form.kind, MultiValue.target]
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

def Form.opening (form : Form) (bt : signature.BlockType) : List Token :=
  match form with
  | .body => []
  | .block => [.block bt]
  | .loop => [.loop bt]
  | .then_ => [.if_ bt]
  | .else_ tokens _ => [.if_ bt] ++ tokens ++ [.else_]

def Saved.trace (f : Saved) : List Token := f.form.opening f.bt ++ f.tokens

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
      · exact ⟨pheader.kind, pheader.placeholder, pheader.inputs, pheader.outputs,
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
    · exact ⟨rfl, header.placeholder, header.inputs, header.outputs,
        ⟨header.emits, by
          simpa [hform, Saved.nextElse, enter, Form.label, Form.params]
            using typed.typed _ hresults⟩, .nil⟩
    · exact TypedPrefix.start _ (enter_wf C hC _ _ _) current.ins
    · simpa [hblocks, Saved.nextElse] using blocks
    · simpa [vals, base, Saved.nextElse] using hvals
  · simp [trace, Saved.trace, Saved.nextElse, hform, Form.opening, List.append_assoc]

def Saved.fresh (base : Usize) (form : Form) (bt : signature.BlockType)
    (ins outs : List types.ValueType) : Saved :=
  { ctrl := ⟨form.kind, .Empty, bt, base, false⟩, bt, ins, outs, form,
    ops := [], vals := (form.params ins).map code.StackType.Val, tokens := [] }

def Form.Initial (form : Form) : Prop := form = .block ∨ form = .loop ∨ form = .then_

theorem Open.enter_child {env root st st' parents current}
    (h : Open env root st parents current) (hroot : wf_context root)
    (form : Form) (bt : signature.BlockType) (ins outs : List types.ValueType)
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
        ⟨header.kind, header.placeholder, header.inputs, header.outputs, header.prior, header.emits⟩
        pbase (ResumePrefix.after_pop typed hpop) hn, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨rfl, rfl, hin, hout, ?_, .nil⟩
      rcases hi with rfl | rfl | rfl <;> trivial
    · simpa [Saved.fresh, pbase] using hbase
    · exact TypedPrefix.start _ (enter_wf _ (enter_wf C hC _ _ _) _ _ _) _
    · simpa [ctrls, List.append_assoc] using hctrls
    · simpa [blocks, Saved.fresh, List.append_assoc] using hblocks
    · simpa [vals, pbase, Saved.fresh, hp, List.append_assoc] using hvals
  · simp [trace, Saved.trace, Saved.fresh, List.flatMap_append, List.append_assoc]

theorem Open.start (env : module.Env) (root : context) (hroot : wf_context root)
    (st : code.BodyState) (bt : signature.BlockType) (ins outs : List types.ValueType)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (hctrls : st.core.ctrls.val = [(Saved.fresh 0#usize .body bt ins outs).ctrl])
    (hblocks : st.blocks.val = [bt]) (hvals : st.core.vals.val = []) :
    Open env root st [] (Saved.fresh 0#usize .body bt ins outs) := by
  refine ⟨root, [], .root _, ⟨rfl, rfl, hin, hout, trivial, .nil⟩, rfl,
    TypedPrefix.start _ (enter_wf root hroot _ _ _) [], hctrls, hblocks, hvals⟩

theorem Spine.body {env root parents C outer ins}
    (h : Spine env root parents C outer .body ins) :
    parents = [] ∧ C = root ∧ outer = [] := by
  cases h with
  | root => exact ⟨rfl, rfl, rfl⟩
  | push _ _ _ _ _ _ _ _ _ _ notBody => exact False.elim (notBody rfl)

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
theorem resolved_labelAt (env : module.Env) (st : code.BodyState) (frames : List Saved)
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

theorem Open.with_pos {env root st parents current} (h : Open env root st parents current)
    (pos : Usize) : Open env root { st with core := { st.core with pos := pos } } parents current := h

end Itasca.MultiValue.Frames
