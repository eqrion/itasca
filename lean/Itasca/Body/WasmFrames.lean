import Itasca.Body.Wasm1ProfileTransport
import Itasca.Body.Sequence
import Itasca.Binary.WasmSyntax

open Aeneas Aeneas.Std

namespace Itasca.WasmFrames

private theorem accepts_concrete (rs : List types.ValueType) (ts : List valtype) :
    List.Forall₂ Sequence.Accepts (rs.map code.StackType.Val) ts ↔
      ts = rs.map Translate.valueType := by
  induction rs generalizing ts with
  | nil => simp
  | cons r rs ih =>
    cases ts <;> simp [Sequence.Accepts, ih]

/-- Appended concrete operands have a unique suffix in every stack realization. -/
theorem realizes_append_concrete (poly : Bool) (vals : List code.StackType)
    (rs : List types.ValueType) (ts : List valtype) :
    Sequence.Realizes poly (vals ++ rs.map code.StackType.Val) ts ↔
      ∃ pre, Sequence.Realizes poly vals pre ∧ ts = pre ++ rs.map Translate.valueType := by
  constructor
  · rintro ⟨front, suffix, hf, hs, rfl⟩
    have ht := List.forall₂_take vals.length hs
    have hd := List.forall₂_drop vals.length hs
    simp only [List.take_left, List.drop_left] at ht hd
    have heq := (accepts_concrete rs _).mp hd
    refine ⟨front ++ suffix.take vals.length, ⟨front, _, hf, ht, rfl⟩, ?_⟩
    rw [← heq, List.append_assoc, List.take_append_drop]
  · rintro ⟨pre, ⟨front, suffix, hf, hs, rfl⟩, rfl⟩
    exact ⟨front, suffix ++ rs.map Translate.valueType, hf,
      List.rel_append hs ((accepts_concrete rs _).mpr rfl), List.append_assoc ..⟩

/-- A suspended prefix retains the arguments consumed when its child was entered.
For an if these are `[I32]`; blocks and loops have no input arguments in Wasm 1.0. -/
structure ResumePrefix (C : context) (ops : List instr) (poly : Bool)
    (vals : List code.StackType) (inputs : List valtype) : Prop where
  wellFormed : Forall wf_instr ops
  typed : ∀ ts, Sequence.Realizes poly vals ts →
    Instrs_ok C ops (.mk_functype (.mk_list []) (.mk_list (ts ++ inputs)))

theorem ResumePrefix.of_prefix {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : Sequence.TypedPrefix C ops poly vals) :
    ResumePrefix C ops poly vals [] := by
  exact ⟨h.wellFormed, by simpa using h.typed⟩

theorem ResumePrefix.after_pop {C : context} {ops : List instr} {poly : Bool}
    {before after : List code.StackType} {inputs : List valtype}
    (h : Sequence.TypedPrefix C ops poly before)
    (hpop : ∀ ts, Sequence.Realizes poly after ts →
      Sequence.Realizes poly before (ts ++ inputs)) :
    ResumePrefix C ops poly after inputs :=
  ⟨h.wellFormed, fun ts ht => h.typed _ (hpop ts ht)⟩

/-- Completing a child restores its result operands and resumes its parent prefix. -/
theorem ResumePrefix.finish {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} {inputs : List valtype}
    (h : ResumePrefix C ops poly vals inputs) (hC : wf_context C)
    (op : instr) (rs : List types.ValueType) (hwf : wf_instr op)
    (hop : Instr_ok C op
      (.mk_functype (.mk_list inputs) (.mk_list (rs.map Translate.valueType)))) :
    Sequence.TypedPrefix C (ops ++ [op]) poly (vals ++ rs.map code.StackType.Val) := by
  constructor
  · simpa [Forall, or_imp, forall_and] using And.intro h.wellFormed hwf
  · intro ts ht
    obtain ⟨pre, hp, rfl⟩ := (realizes_append_concrete poly vals rs ts).mp ht
    exact .seq C ops [op] [] (pre ++ rs.map Translate.valueType) (pre ++ inputs)
      (h.typed pre hp)
      (.frame C [op] pre inputs (rs.map Translate.valueType)
        (.instr C op inputs _ hop hC hwf) hC (by simpa [Forall] using hwf))
      hC h.wellFormed (by simpa [Forall] using hwf)

/-- The pending structured construct, including the saved first arm of an if. -/
inductive Form where
  | body
  | block
  | loop
  | then_
  | else_ (thenTokens : List Wasm.Token) (thenOps : List instr)

def Form.kind : Form → code.LabelKind
  | .body => .Body
  | .block => .Block
  | .loop => .Loop
  | .then_ => .Then
  | .else_ _ _ => .Else

def Form.inputs : Form → List valtype
  | .then_ | .else_ _ _ => [.I32]
  | _ => []

def Form.label (form : Form) (bt : code.BlockType) : List valtype :=
  match form with
  | .loop => []
  | _ => Control.resultTypes bt

def enter (C : context) (form : Form) (bt : code.BlockType) : context :=
  Control.labelContext (form.label bt) ++ C

/-- An else frame carries the completed typing derivation for its then arm. -/
def Form.Valid (C : context) (bt : code.BlockType) : Form → Prop
  | .else_ thenTokens thenOps => Wasm.Emits thenTokens thenOps ∧
      Instrs_ok (enter C (.else_ thenTokens thenOps) bt) thenOps
        (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bt)))
  | _ => True

/-- Profile of the already checked then arm while the else arm is active. -/
def Form.Profile (C : context) (bt : code.BlockType) : Form → Prop
  | .else_ _ thenOps => Wasm1.Instructions (enter C (.else_ [] thenOps) bt) thenOps
  | _ => True

structure Saved where
  ctrl : code.Ctrl
  form : Form
  ops : List instr
  vals : List code.StackType
  tokens : List Wasm.Token

structure Header (C : context) (f : Saved) : Prop where
  kind : f.ctrl.kind = f.form.kind
  prior : f.form.Valid C f.ctrl.block_type
  emits : Wasm.Emits f.tokens f.ops
  profile : Wasm1.Instructions (enter C f.form f.ctrl.block_type) f.ops
  priorProfile : f.form.Profile C f.ctrl.block_type

/-- Suspended frames run from outermost to innermost, matching the Rust control vector. -/
inductive Spine (root : context) : List Saved → context → List code.StackType → Form → Prop where
  | root : Spine root [] root [] .body
  | push (parents : List Saved) (parentC : context) (outer : List code.StackType)
      (parent : Saved) (child : Form)
      (spine : Spine root parents parentC outer parent.form)
      (header : Header parentC parent)
      (base : parent.ctrl.value_stack_base.val = outer.length)
      (resume : ResumePrefix (enter parentC parent.form parent.ctrl.block_type)
        parent.ops parent.ctrl.polymorphic_base parent.vals child.inputs)
      (notBody : child ≠ .body) :
      Spine root (parents ++ [parent]) (enter parentC parent.form parent.ctrl.block_type)
        (outer ++ parent.vals) child

/-- The ghost zipper links every open frame to the concrete operand and control stacks. -/
def Open (root : context) (st : code.OpIterState) (parents : List Saved) (current : Saved) : Prop :=
  ∃ C outer, Spine root parents C outer current.form ∧ Header C current ∧
    current.ctrl.value_stack_base.val = outer.length ∧
    Sequence.TypedPrefix (enter C current.form current.ctrl.block_type)
      current.ops current.ctrl.polymorphic_base current.vals ∧
    st.ctrls.val = parents.map Saved.ctrl ++ [current.ctrl] ∧
    st.vals.val = outer ++ current.vals

theorem enter_wf (C : context) (hC : wf_context C) (form : Form) (bt : code.BlockType) :
    wf_context (enter C form bt) := Control.enter_context_wf C hC _

theorem Spine.context_wf {root : context} {parents : List Saved} {C : context}
    {outer : List code.StackType} {form : Form}
    (h : Spine root parents C outer form) (hroot : wf_context root) : wf_context C := by
  induction h with
  | root => exact hroot
  | push _ _ _ _ _ _ _ _ _ _ ih => exact enter_wf _ ih _ _

theorem Header.label {C : context} {f : Saved} (h : Header C f) :
    f.form.label f.ctrl.block_type = (Control.targetTypes f.ctrl).map Translate.valueType := by
  rw [Control.targetTypes, Control.targetBlockType, h.kind]
  cases hf : f.form <;> simp [Form.kind, Form.label, Control.resultTypes, Control.results]

theorem Spine.labels {root : context} {parents : List Saved} {C : context}
    {outer : List code.StackType} {form : Form} (h : Spine root parents C outer form) :
    C.LABELS = Control.labels (parents.map Saved.ctrl) ++ root.LABELS := by
  induction h with
  | root => simp [Control.labels]
  | push parents parentC outer parent child spine header base resume notBody ih =>
    simp [enter, Control.labelContext_labels, List.map_append,
      Control.labels_push, header.label, ih]

/-- A closing delimiter determines exactly one structured instruction. -/
inductive Closed : Form → code.BlockType → List instr → instr → Prop where
  | block (bt : code.BlockType) (ops : List instr) :
      Closed .block bt ops (.BLOCK (Control.blockType bt) ops)
  | loop (bt : code.BlockType) (ops : List instr) :
      Closed .loop bt ops (.LOOP (Control.blockType bt) ops)
  | then_ (ops : List instr) :
      Closed .then_ .Empty ops (.IFELSE (Control.blockType .Empty) ops [])
  | else_ (bt : code.BlockType) (thenTokens : List Wasm.Token) (thenOps ops : List instr) :
      Closed (.else_ thenTokens thenOps) bt ops (.IFELSE (Control.blockType bt) thenOps ops)

theorem Closed.wf {form : Form} {bt : code.BlockType} {ops : List instr} {op : instr}
    (closed : Closed form bt ops op) (C : context) (hprior : form.Valid C bt)
    (hops : Forall wf_instr ops) : wf_instr op := by
  cases closed with
  | block => exact .instr_case_4 _ _ (Control.blockType_wf _) hops
  | loop => exact .instr_case_5 _ _ (Control.blockType_wf _) hops
  | then_ => exact .instr_case_6 _ _ _ (Control.blockType_wf _) hops (by simp [Forall])
  | else_ => exact .instr_case_6 _ _ _ (Control.blockType_wf _) hprior.1.wellFormed hops

theorem Closed.typed {C : context} {form : Form} {bt : code.BlockType}
    {ops : List instr} {op : instr} {poly : Bool} {vals : List code.StackType}
    (closed : Closed form bt ops op) (hC : wf_context C) (hprior : form.Valid C bt)
    (htyped : Sequence.TypedPrefix (enter C form bt) ops poly vals)
    (hresults : Sequence.Realizes poly vals (Control.resultTypes bt)) :
    Instr_ok C op (.mk_functype (.mk_list form.inputs) (.mk_list (Control.resultTypes bt))) := by
  cases closed with
  | block => exact htyped.close_block hC _ hresults
  | loop => exact htyped.close_loop hC _ hresults
  | then_ =>
    exact .if C _ _ [] [] [] (Control.blockType_ok C hC .Empty)
      (htyped.typed [] hresults) (.empty _ (enter_wf C hC .then_ .Empty)) hC
      (.instr_case_6 _ _ [] (Control.blockType_wf _) htyped.wellFormed (by simp [Forall]))
      (Control.labelContext_wf [])
  | else_ bt thenTokens thenOps ops =>
    exact .if C _ _ _ [] _ (Control.blockType_ok C hC bt) hprior.2
      (htyped.typed _ hresults) hC
      (.instr_case_6 _ _ _ (Control.blockType_wf _) hprior.1.wellFormed htyped.wellFormed)
      (Control.labelContext_wf _)

theorem Closed.profile {C : context} {form : Form} {bt : code.BlockType}
    {ops : List instr} {op : instr} (closed : Closed form bt ops op)
    (hprior : form.Profile C bt) (hops : Wasm1.Instructions (enter C form bt) ops) :
    Wasm1.Instruction C op := by
  cases closed with
  | block => exact .block C _ _ hops
  | loop => exact .loop C _ _ hops
  | then_ => exact .ifElse C _ _ _ hops (.nil _)
  | else_ => exact .ifElse C _ _ _ hprior hops

def Form.opening (form : Form) (bt : code.BlockType) : List Wasm.Token :=
  match form with
  | .body => []
  | .block => [.block bt]
  | .loop => [.loop bt]
  | .then_ => [.if_ bt]
  | .else_ thenTokens _ => [.if_ bt] ++ thenTokens ++ [.else_]

def Saved.trace (f : Saved) : List Wasm.Token := f.form.opening f.ctrl.block_type ++ f.tokens

def trace (parents : List Saved) (current : Saved) : List Wasm.Token :=
  parents.flatMap Saved.trace ++ current.trace

theorem Closed.not_body {form : Form} {bt : code.BlockType} {ops : List instr} {op : instr}
    (closed : Closed form bt ops op) : form ≠ .body := by
  cases closed <;> simp

theorem Closed.emits {form : Form} {bt : code.BlockType} {ops : List instr} {op : instr}
    {tokens : List Wasm.Token} (closed : Closed form bt ops op)
    (C : context) (hprior : form.Valid C bt) (hemits : Wasm.Emits tokens ops) :
    Wasm.Emits (form.opening bt ++ tokens ++ [.end_]) [op] := by
  cases closed with
  | block => simpa [Form.opening] using Wasm.Emits.block bt .nil hemits
  | loop => simpa [Form.opening] using Wasm.Emits.loop bt .nil hemits
  | then_ => simpa [Form.opening] using Wasm.Emits.ifEnd .Empty .nil hemits
  | else_ => simpa [Form.opening] using Wasm.Emits.ifElse bt .nil hprior.1 hemits

/-- Closing a nested frame resumes its suspended parent and records the closing token. -/
theorem Open.close {root : context} {st st' : code.OpIterState}
    {parents : List Saved} {current : Saved} (h : Open root st parents current)
    (hroot : wf_context root) (op : instr)
    (closed : Closed current.form current.ctrl.block_type current.ops op)
    (hresults : Sequence.Realizes current.ctrl.polymorphic_base current.vals
      (Control.resultTypes current.ctrl.block_type))
    (hctrls : st'.ctrls.val = parents.map Saved.ctrl)
    (hvals : st'.vals.val = st.vals.val.take current.ctrl.value_stack_base.val ++
      (Control.results current.ctrl.block_type).map code.StackType.Val) :
    ∃ grandparents parent, parents = grandparents ++ [parent] ∧
      let resumed := { parent with
        ops := parent.ops ++ [op]
        vals := parent.vals ++ (Control.results current.ctrl.block_type).map code.StackType.Val
        tokens := parent.tokens ++ current.trace ++ [.end_] }
      Open root st' grandparents resumed ∧
        trace grandparents resumed = trace parents current ++ [.end_] := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := h
  have hC := spine.context_wf hroot
  have hop := closed.typed hC header.prior typed hresults
  have hwf := closed.wf C header.prior typed.wellFormed
  have hemit := closed.emits C header.prior header.emits
  have hprofile := closed.profile header.priorProfile header.profile
  generalize hform : current.form = form at spine
  cases spine with
  | root => exact False.elim (closed.not_body hform)
  | push gps parentC outer parent child spine pheader pbase resume notBody =>
    refine ⟨gps, parent, rfl, ?_, ?_⟩
    · refine ⟨parentC, outer, spine, ?_, pbase,
        resume.finish hC op (Control.results current.ctrl.block_type) hwf
          (by simpa [hform, Control.resultTypes] using hop), ?_, ?_⟩
      · exact ⟨pheader.kind, pheader.prior, by
          simpa [Saved.trace, List.append_assoc] using pheader.emits.append hemit,
          pheader.profile.append (.cons hprofile (.nil _)), pheader.priorProfile⟩
      · simpa using hctrls
      · have htake : st.vals.val.take current.ctrl.value_stack_base.val = outer ++ parent.vals := by
          rw [vals, base, List.take_left]
        simpa [htake, List.append_assoc] using hvals
    · simp [trace, Saved.trace, List.flatMap_append, List.append_assoc]

theorem Spine.change_form {root : context} {parents : List Saved} {C : context}
    {outer : List code.StackType} {before after : Form}
    (h : Spine root parents C outer before) (hinputs : before.inputs = after.inputs)
    (hbody : before = .body ↔ after = .body) : Spine root parents C outer after := by
  cases h with
  | root => rw [hbody.mp rfl]; exact .root
  | push ps pc out parent child spine header base resume notBody =>
    exact .push ps pc out parent after spine header base
      (by simpa [hinputs] using resume) (fun heq => notBody (hbody.mpr heq))

def Saved.nextElse (current : Saved) : Saved :=
  { ctrl := { current.ctrl with kind := .Else, polymorphic_base := false }
    form := .else_ current.tokens current.ops
    ops := [], vals := [], tokens := [] }

theorem Open.else_ {root : context} {st st' : code.OpIterState}
    {parents : List Saved} {current : Saved} (h : Open root st parents current)
    (hroot : wf_context root) (hform : current.form = .then_)
    (hresults : Sequence.Realizes current.ctrl.polymorphic_base current.vals
      (Control.resultTypes current.ctrl.block_type))
    (hctrls : st'.ctrls.val = parents.map Saved.ctrl ++ [current.nextElse.ctrl])
    (hvals : st'.vals.val = st.vals.val.take current.ctrl.value_stack_base.val) :
    Open root st' parents current.nextElse ∧
      trace parents current.nextElse = trace parents current ++ [.else_] := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := h
  have hC := spine.context_wf hroot
  constructor
  · refine ⟨C, outer, spine.change_form (by simp [hform, Saved.nextElse, Form.inputs])
      (by simp [hform, Saved.nextElse]), ?_, base, ?_, hctrls, ?_⟩
    · exact ⟨rfl, ⟨header.emits, by
        simpa [hform, Saved.nextElse, enter, Form.label] using typed.typed _ hresults⟩, .nil,
        .nil _, by simpa [Saved.nextElse, Form.Profile, hform, enter, Form.label] using header.profile⟩
    · exact Sequence.TypedPrefix.empty _ (enter_wf C hC _ _)
    · simpa [vals, base, Saved.nextElse] using hvals
  · simp [trace, Saved.trace, Saved.nextElse, hform, Form.opening, List.append_assoc]

def Saved.advance (current : Saved) (token : Wasm.Token) (op : instr)
    (poly : Bool) (vals : List code.StackType) : Saved :=
  { current with
    ctrl := { current.ctrl with polymorphic_base := poly }
    ops := current.ops ++ [op]
    vals := vals
    tokens := current.tokens ++ [token] }


def Saved.fresh (st : code.OpIterState) (form : Form) (bt : code.BlockType) : Saved :=
  { ctrl := Control.frame st form.kind bt, form := form, ops := [], vals := [], tokens := [] }

/-- Entering a child suspends the parent with its consumed argument types still recorded. -/
def Form.Initial (form : Form) : Prop := form = .block ∨ form = .loop ∨ form = .then_

theorem Open.enter_child {root : context} {st st' : code.OpIterState}
    {parents : List Saved} {current : Saved} (h : Open root st parents current)
    (hroot : wf_context root) (form : Form) (bt : code.BlockType) (hi : form.Initial)
    (remaining : List code.StackType)
    (hpop : ∀ ts, Sequence.Realizes current.ctrl.polymorphic_base remaining ts →
      Sequence.Realizes current.ctrl.polymorphic_base current.vals (ts ++ form.inputs))
    (hctrls : st'.ctrls.val = st.ctrls.val ++ [(Saved.fresh st' form bt).ctrl])
    (hvals : st'.vals.val = st.vals.val.take current.ctrl.value_stack_base.val ++ remaining) :
    Open root st' (parents ++ [{ current with vals := remaining }]) (Saved.fresh st' form bt) ∧
      trace (parents ++ [{ current with vals := remaining }]) (Saved.fresh st' form bt) =
        trace parents current ++ form.opening bt := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := h
  have hC := spine.context_wf hroot
  have hrest : st'.vals.val = outer ++ remaining := by simpa [vals, base] using hvals
  have hn : form ≠ .body := by rcases hi with rfl | rfl | rfl <;> simp
  constructor
  · refine ⟨enter C current.form current.ctrl.block_type, outer ++ remaining,
      .push parents C outer { current with vals := remaining } form spine
        ⟨header.kind, header.prior, header.emits, header.profile, header.priorProfile⟩ base
        (ResumePrefix.after_pop typed hpop) hn, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨rfl, ?_, .nil, .nil _, ?_⟩
      all_goals rcases hi with rfl | rfl | rfl <;> trivial
    · simpa [Saved.fresh, Control.frame] using congrArg List.length hrest
    · exact Sequence.TypedPrefix.empty _ (enter_wf _ (enter_wf C hC _ _) _ _)
    · simpa [ctrls, List.append_assoc] using hctrls
    · simpa [Saved.fresh] using hrest
  · simp [trace, Saved.trace, Saved.fresh, Control.frame, List.append_assoc]

theorem Open.start (root : context) (hroot : wf_context root) (st : code.OpIterState)
    (bt : code.BlockType) (hctrls : st.ctrls.val = [(Control.frame st .Body bt)])
    (hvals : st.vals.val = []) :
    Open root st [] (Saved.fresh st .body bt) := by
  refine ⟨root, [], .root, ⟨rfl, trivial, .nil, .nil _, trivial⟩, ?_,
    Sequence.TypedPrefix.empty _ (enter_wf root hroot _ _), ?_, ?_⟩
  · simp [Saved.fresh, Control.frame, hvals]
  · exact hctrls
  · exact hvals

/-- Only the outermost frame can be a function body. -/
theorem Spine.body {root : context} {parents : List Saved} {C : context}
    {outer : List code.StackType} (h : Spine root parents C outer .body) :
    parents = [] ∧ C = root ∧ outer = [] := by
  cases h with
  | root => exact ⟨rfl, rfl, rfl⟩
  | push _ _ _ _ _ _ _ _ _ notBody => exact False.elim (notBody rfl)

theorem Open.finish_body {root : context} {st : code.OpIterState}
    {parents : List Saved} {current : Saved} (h : Open root st parents current)
    (hform : current.form = .body)
    (hresults : Sequence.Realizes current.ctrl.polymorphic_base current.vals
      (Control.resultTypes current.ctrl.block_type)) :
    parents = [] ∧
      Wasm.BodyTokens (trace parents current ++ [.end_]) current.ops ∧
      Instrs_ok (enter root .body current.ctrl.block_type) current.ops
        (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes current.ctrl.block_type))) ∧
      Wasm1.Instructions (enter root .body current.ctrl.block_type) current.ops := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := h
  rw [hform] at spine
  obtain ⟨rfl, rfl, rfl⟩ := spine.body
  refine ⟨rfl, ⟨current.tokens, ?_, header.emits⟩, ?_, ?_⟩
  · simp [trace, Saved.trace, hform, Form.opening]
  · simpa [hform] using typed.typed _ hresults
  · simpa [hform] using header.profile

@[simp]
theorem enter_return (C : context) (form : Form) (bt : code.BlockType) :
    (enter C form bt).RETURN = C.RETURN := rfl

theorem Spine.returns {root : context} {parents : List Saved} {C : context}
    {outer : List code.StackType} {form : Form} (h : Spine root parents C outer form) :
    C.RETURN = root.RETURN := by
  induction h with
  | root => rfl
  | push _ _ _ _ _ _ _ _ _ _ ih => simpa using ih

theorem Open.context {root : context} {st : code.OpIterState}
    {parents : List Saved} {current : Saved} (h : Open root st parents current)
    (hroot : wf_context root) :
    ∃ C outer, Spine root parents C outer current.form ∧ Header C current ∧
      current.ctrl.value_stack_base.val = outer.length ∧
      Sequence.TypedPrefix (enter C current.form current.ctrl.block_type)
        current.ops current.ctrl.polymorphic_base current.vals ∧
      st.ctrls.val = parents.map Saved.ctrl ++ [current.ctrl] ∧ st.vals.val = outer ++ current.vals ∧
      wf_context (enter C current.form current.ctrl.block_type) ∧
      (enter C current.form current.ctrl.block_type).LABELS = Control.labels st.ctrls.val ++ root.LABELS ∧
      (enter C current.form current.ctrl.block_type).RETURN = root.RETURN := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := h
  refine ⟨C, outer, spine, header, base, typed, ctrls, vals,
    enter_wf C (spine.context_wf hroot) _ _, ?_, ?_⟩
  · simp [enter, ctrls, Control.labels_push, header.label, spine.labels]
  · exact spine.returns

/-- The function result is stored in the outermost physical frame. -/
def bodyType (parents : List Saved) (current : Saved) : Option code.BlockType :=
  ((parents ++ [current]).head?).map (fun f => f.ctrl.block_type)

@[simp]
theorem bodyType_root (current : Saved) : bodyType [] current = some current.ctrl.block_type := rfl

theorem bodyType_advance (parents : List Saved) (current : Saved) (token : Wasm.Token)
    (op : instr) (poly : Bool) (vals : List code.StackType) :
    bodyType parents (current.advance token op poly vals) = bodyType parents current := by
  cases parents <;> rfl

theorem bodyType_else (parents : List Saved) (current : Saved) :
    bodyType parents current.nextElse = bodyType parents current := by
  cases parents <;> rfl

theorem bodyType_enter (parents : List Saved) (current child : Saved) (remaining : List code.StackType) :
    bodyType (parents ++ [{ current with vals := remaining }]) child = bodyType parents current := by
  cases parents <;> rfl

theorem bodyType_close (grandparents : List Saved) (parent current : Saved) (op : instr) :
    bodyType grandparents { parent with
      ops := parent.ops ++ [op]
      vals := parent.vals ++ (Control.results current.ctrl.block_type).map code.StackType.Val
      tokens := parent.tokens ++ current.trace ++ [.end_] } =
        bodyType (grandparents ++ [parent]) current := by
  cases grandparents <;> rfl

/-- A running zipper or its completed function body, with the original result type retained. -/
def Status (root : context) (bodyBt : code.BlockType) (st : code.OpIterState)
    (tokens : List Wasm.Token) : Prop :=
  (∃ parents current, Open root st parents current ∧ trace parents current = tokens ∧
      bodyType parents current = some bodyBt) ∨
  (st.ctrls.val = [] ∧ ∃ ops,
    Wasm.BodyTokens tokens ops ∧
    Instrs_ok (enter root .body bodyBt) ops
      (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bodyBt))) ∧
    Wasm1.Instructions (enter root .body bodyBt) ops)

theorem Status.completed {root : context} {bodyBt : code.BlockType}
    {st : code.OpIterState} {tokens : List Wasm.Token} (h : Status root bodyBt st tokens)
    (hctrls : st.ctrls.val = []) :
    ∃ ops, Wasm.BodyTokens tokens ops ∧
      Instrs_ok (enter root .body bodyBt) ops
        (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bodyBt))) ∧
      Wasm1.Instructions (enter root .body bodyBt) ops := by
  rcases h with ⟨parents, current, ⟨C, outer, spine, header, base, typed, hc, hv⟩, trace, bt⟩ | ⟨_, h⟩
  · simp [hctrls] at hc
  · exact h

theorem Spine.bounds {root : context} {parents : List Saved} {C : context}
    {outer : List code.StackType} {form : Form} (h : Spine root parents C outer form) :
    (parents.map Saved.ctrl).Pairwise (fun c d => c.value_stack_base.val ≤ d.value_stack_base.val) ∧
      ∀ c ∈ parents.map Saved.ctrl, c.value_stack_base.val ≤ outer.length := by
  induction h with
  | root => simp
  | push parents C outer parent child spine header base resume notBody ih =>
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

theorem Open.shape {root : _root_.context} {st : code.OpIterState}
    {parents : List Saved} {current : Saved} (h : Open root st parents current) : Control.Shape st := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := h
  obtain ⟨ordered, bounded⟩ := spine.bounds
  constructor
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

end Itasca.WasmFrames
