import Itasca.Body.Branch

open Aeneas Aeneas.Std

namespace Itasca.Sequence

/-- A concrete operand has its translated type; a polymorphic operand can have any type. -/
def Accepts : code.StackType → valtype → Prop
  | .Val t, t' => t' = Translate.valueType t
  | .Bot, _ => True

/-- Operand lists retain their order: SpecTec writes the top of the stack on the right. -/
def stackTypes : List code.StackType → List valtype :=
  List.map (fun t => match t with | .Val v => Translate.valueType v | .Bot => .BOT)

/-- Unreachable frames may have an arbitrary prefix below their known operands. -/
def Realizes (polymorphic : Bool) (vals : List code.StackType) (ts : List valtype) : Prop :=
  ∃ front suffix, (polymorphic = false → front = []) ∧
    List.Forall₂ Accepts vals suffix ∧ ts = front ++ suffix

theorem realizes_default (poly : Bool) (vals : List code.StackType) :
    Realizes poly vals (stackTypes vals) := by
  refine ⟨[], stackTypes vals, by simp, ?_, by simp⟩
  induction vals with
  | nil => exact .nil
  | cons t ts ih =>
    apply List.Forall₂.cons _ ih
    cases t <;> simp [Accepts]

theorem realizes_empty (ts : List valtype) : Realizes false [] ts ↔ ts = [] := by
  simp [Realizes]

theorem realizes_polymorphic_empty (ts : List valtype) : Realizes true [] ts := by
  exact ⟨ts, [], by simp, .nil, by simp⟩

theorem Realizes.snoc {poly : Bool} {vals : List code.StackType} {ts : List valtype}
    (h : Realizes poly vals ts) (t : code.StackType) (u : valtype) (ht : Accepts t u) :
    Realizes poly (vals ++ [t]) (ts ++ [u]) := by
  obtain ⟨front, suffix, hf, hs, rfl⟩ := h
  exact ⟨front, suffix ++ [u], hf, List.rel_append hs (.cons ht .nil), List.append_assoc ..⟩

/-- A ghost instruction prefix can produce every stack represented by the validator frame.
This is a per-frame invariant; connecting all open frames and pending if-conditions is separate. -/
structure TypedPrefix (C : context) (ops : List instr) (poly : Bool)
    (vals : List code.StackType) : Prop where
  wellFormed : Forall wf_instr ops
  typed : ∀ ts, Realizes poly vals ts →
    Instrs_ok C ops (.mk_functype (.mk_list []) (.mk_list ts))

theorem TypedPrefix.empty (C : context) (hC : wf_context C) : TypedPrefix C [] false [] := by
  constructor
  · simp [Forall]
  · intro ts ht
    have hnil := (realizes_empty ts).mp ht
    subst ts
    exact .empty C hC

/-- Composition uses the generated declarative sequence rule directly. -/
theorem TypedPrefix.append {C : context} {ops : List instr} {poly poly' : Bool}
    {vals vals' : List code.StackType} (h : TypedPrefix C ops poly vals)
    (hC : wf_context C) (op : instr) (hwf : wf_instr op)
    (hstep : ∀ out, Realizes poly' vals' out → ∃ input, Realizes poly vals input ∧
      Instrs_ok C [op] (.mk_functype (.mk_list input) (.mk_list out))) :
    TypedPrefix C (ops ++ [op]) poly' vals' := by
  constructor
  · simpa [Forall, or_imp, forall_and] using And.intro h.wellFormed hwf
  · intro out hout
    obtain ⟨input, hin, hop⟩ := hstep out hout
    exact .seq C ops [op] [] out input (h.typed input hin) hop hC
      h.wellFormed (by simpa [Forall] using hwf)

theorem TypedPrefix.nop {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C ops poly vals) (hC : wf_context C) :
    TypedPrefix C (ops ++ [.NOP]) poly vals := by
  apply h.append hC .NOP .instr_case_0
  intro ts ht
  refine ⟨ts, ht, ?_⟩
  simpa using Instrs_ok.frame C [.NOP] ts [] []
    (.instr C .NOP [] [] (.nop C hC .instr_case_0) hC .instr_case_0)
    hC (by simp [Forall]; exact .instr_case_0)

theorem TypedPrefix.unreachable {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C ops poly vals) (hC : wf_context C) :
    TypedPrefix C (ops ++ [.UNREACHABLE]) true [] := by
  apply h.append hC .UNREACHABLE .instr_case_1
  intro ts _
  exact ⟨stackTypes vals, realizes_default poly vals,
    .instr C .UNREACHABLE (stackTypes vals) ts
      (.unreachable C _ ts hC .instr_case_1) hC .instr_case_1⟩

/-- An accepted branch supplies the target's arguments and makes the current frame polymorphic. -/
theorem TypedPrefix.branch {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C ops poly vals) (hC : wf_context C)
    (cs : List code.Ctrl) (hlabels : C.LABELS = Control.labels cs)
    (depth : U32) (hdepth : depth.val < cs.length) (front : List valtype)
    (hargs : Realizes poly vals (front ++
      (Control.targetTypes (cs[cs.length - 1 - depth.val]'(by omega))).map Translate.valueType)) :
    TypedPrefix C (ops ++ [.BR (.mk_uN depth.val)]) true [] := by
  have hwf : wf_instr (.BR (.mk_uN depth.val)) := by
    apply wf_instr.instr_case_7
    apply wf_uN.uN_case_0
    have hd := depth.hmax
    norm_num at hd ⊢
    omega
  apply h.append hC _ hwf
  intro ts _
  refine ⟨_, hargs, ?_⟩
  exact .instr C _ _ ts (Control.branch_typed C hC cs hlabels depth hdepth front ts) hC hwf

theorem TypedPrefix.close_block {C : context} (hC : wf_context C) (bt : code.BlockType)
    {ops : List instr} {poly : Bool} {vals : List code.StackType}
    (h : TypedPrefix (Control.labelContext (Control.resultTypes bt) ++ C) ops poly vals)
    (hresults : Realizes poly vals (Control.resultTypes bt)) :
    Instr_ok C (.BLOCK (Control.blockType bt) ops)
      (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bt))) :=
  Control.block_typed C hC bt ops h.wellFormed (h.typed _ hresults)

theorem TypedPrefix.close_loop {C : context} (hC : wf_context C) (bt : code.BlockType)
    {ops : List instr} {poly : Bool} {vals : List code.StackType}
    (h : TypedPrefix (Control.labelContext [] ++ C) ops poly vals)
    (hresults : Realizes poly vals (Control.resultTypes bt)) :
    Instr_ok C (.LOOP (Control.blockType bt) ops)
      (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bt))) :=
  Control.loop_typed C hC bt ops h.wellFormed (h.typed _ hresults)

end Itasca.Sequence

namespace Itasca

/-- The extracted unreachable handler preserves the declarative prefix invariant
for the current frame while retaining the operand prefix owned by outer frames. -/
theorem code.read_unreachable.prefix (st : code.OpIterState) (C : context)
    (hC : wf_context C) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType) (ops : List instr)
    (hctrls : st.ctrls.val = cs ++ [c]) (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (htyped : Sequence.TypedPrefix C ops c.polymorphic_base segment) :
    ∃ st', code.read_unreachable st = .ok (.Ok (), st') ∧
      st'.vals.val = outer ∧
      st'.ctrls.val = cs ++ [{ c with polymorphic_base := true }] ∧
      st'.pos = st.pos ∧ Sequence.TypedPrefix C (ops ++ [.UNREACHABLE]) true [] := by
  obtain ⟨st', hr, hv, _, hc, hp⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec st cs c hctrls (by simp [hbase, hvals]))
  refine ⟨st', ?_, ?_, hc, hp, htyped.unreachable hC⟩
  · simp [code.read_unreachable, hr]
  · simpa [hvals, hbase] using hv

end Itasca
