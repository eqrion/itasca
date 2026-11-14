import Itasca.Handler.EnvReaders
import Itasca.Binary.Leb128
import Itasca.Binary.Wasm1.BlockType
import Itasca.Spec.TypingInversion

/-!
Sections, each formerly its own module: Block, Sequence, Stack, StackSemantics, StackComplete, ResumePrefix, SimplePrefix.
-/

/-! ## Block -/

section

/-!
# Block and loop handlers

Lemmas about `code.read_block_type`, `code.read_block` and `code.read_loop` for Wasm 1.0 scalar
block types: byte-level specifications, and `code.read_block.context` and `code.read_loop.context`,
which show the label context extends with the generated `Blocktype_ok`. `Control.block_typed` and
`Control.loop_typed` give the generated `block` and `loop` rules.
-/

open Aeneas Aeneas.Std

namespace Itasca.Control

end Itasca.Control

namespace Itasca

end Itasca

end

/-! ## Sequence -/

section

/-!
# Typed prefixes and realized stacks

Relates the validator's operand stack (`code.StackType`, with `Bot` for unreachable code) to
declarative stacks. `Sequence.Realizes` says a declarative stack is a possible reading of a
validator stack, and `Sequence.TypedPrefix` says the instructions read so far type at every
realized stack. `TypedPrefix.append` extends a prefix with generated `Instr_ok` rules, and
`DeclarativeComplete.head_realizes` is the inverse used by completeness proofs.
-/

open Aeneas Aeneas.Std

namespace Itasca.Sequence

/-- A concrete operand has its translated type, and a `Bot` operand has any type. -/
def Accepts : code.StackType → valtype → Prop
  | .Val t, t' => t' = Translate.valueType t
  | .Bot, _ => True

/-- The SpecTec value types of a validator stack, with `Bot` as `BOT`. The top of the stack is on
the right, as in SpecTec. -/
def stackTypes : List code.StackType → List valtype :=
  List.map (fun t => match t with | .Val v => Translate.valueType v | .Bot => .BOT)

/-- A declarative stack `ts` realizes the validator stack `vals` of a frame. If the frame is
polymorphic (unreachable), `ts` may have an arbitrary prefix below the known operands. -/
def Realizes (polymorphic : Bool) (vals : List code.StackType) (ts : List valtype) : Prop :=
  ∃ front suffix, (polymorphic = false → front = []) ∧
    List.Forall₂ Accepts vals suffix ∧ ts = front ++ suffix

/-- A validator stack realizes its own translation. -/
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

/-- Pushing an accepted operand preserves `Realizes`. -/
theorem Realizes.snoc {poly : Bool} {vals : List code.StackType} {ts : List valtype}
    (h : Realizes poly vals ts) (t : code.StackType) (u : valtype) (ht : Accepts t u) :
    Realizes poly (vals ++ [t]) (ts ++ [u]) := by
  obtain ⟨front, suffix, hf, hs, rfl⟩ := h
  exact ⟨front, suffix ++ [u], hf, List.rel_append hs (.cons ht .nil), List.append_assoc ..⟩

/-- The instructions `ops` read so far in a frame are well-formed and have type `[] -> ts` for every
`ts` that realizes the frame's stack `vals`. This is a per-frame invariant. -/
structure TypedPrefix (C : context) (ops : List instr) (poly : Bool)
    (vals : List code.StackType) : Prop where
  wellFormed : Forall wf_instr ops
  typed : ∀ ts, Realizes poly vals ts →
    Instrs_ok C ops (.mk_functype (.mk_list []) (.mk_list ts))

/-- The empty prefix types the empty stack. -/
theorem TypedPrefix.empty (C : context) (hC : wf_context C) : TypedPrefix C [] false [] := by
  constructor
  · simp [Forall]
  · intro ts ht
    have hnil := (realizes_empty ts).mp ht
    subst ts
    exact .empty C hC

/-- Appends one instruction to a typed prefix using the generated `seq` rule, given that each
realized output stack has a realized input stack on which the instruction is typed. -/
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

end Itasca.Sequence

namespace Itasca

end Itasca

namespace Itasca.DeclarativeComplete

/-- `Accepts` is preserved by widening the declarative type. -/
theorem accepts_mono {t : code.StackType} {a b : valtype}
    (h : Sequence.Accepts t a) (hs : Valtype_sub a b) : Sequence.Accepts t b := by
  cases t with
  | Bot => trivial
  | Val t =>
    cases hs with
    | refl => exact h
    | bot => cases t <;> simp [Sequence.Accepts, Translate.valueType] at h

/-- Pointwise `Accepts` is preserved by widening the declarative types. -/
theorem accepts_list_mono {vals : List code.StackType} {a b : List valtype}
    (h : List.Forall₂ Sequence.Accepts vals a) (hs : List.Forall₂ Valtype_sub a b) :
    List.Forall₂ Sequence.Accepts vals b := by
  induction h generalizing b with
  | nil => cases hs; exact .nil
  | cons h ht ih =>
    cases hs with
    | cons hs ht' => exact .cons (accepts_mono h hs) (ih ht')

/-- Widening a declarative stack preserves `Realizes`. -/
theorem realizes_mono {poly : Bool} {vals : List code.StackType} {a b : List valtype}
    (h : Sequence.Realizes poly vals a)
    (hs : Resulttype_sub (.mk_list a) (.mk_list b)) : Sequence.Realizes poly vals b := by
  obtain ⟨front, suffix, hf, hv, rfl⟩ := h
  have hs := result_sub_iff.mp hs
  have hf' := List.forall₂_take front.length hs
  have ht' := List.forall₂_drop front.length hs
  simp only [List.take_left, List.drop_left] at hf' ht'
  refine ⟨b.take front.length, b.drop front.length, ?_, ?_, (List.take_append_drop _ _).symm⟩
  · intro hp
    simp [hf hp]
  · exact accepts_list_mono hv ht'

/-- If a stack realizing `vals` is the input of a typed non-empty sequence, then it realizes the
framed input of the head's primitive rule, and the framed output types the tail. -/
theorem head_realizes {C : context} {op : instr} {ops : List instr}
    {poly : Bool} {vals : List code.StackType} {a b : List valtype}
    (hr : Sequence.Realizes poly vals a)
    (h : Instrs_ok C (op :: ops) (.mk_functype (.mk_list a) (.mk_list b))) :
    ∃ front ins outs,
      Instr_ok C op (.mk_functype (.mk_list ins) (.mk_list outs)) ∧
      Sequence.Realizes poly vals (front ++ ins) ∧
      Instrs_ok C ops (.mk_functype (.mk_list (front ++ outs)) (.mk_list b)) := by
  obtain ⟨front, ins, outs, hop, hin, hrest⟩ := head_normal h
  exact ⟨front, ins, outs, hop, realizes_mono hr hin, hrest⟩

/-- If a stack realizing `vals` is the input of a typed empty sequence, the output realizes `vals`
too. -/
theorem empty_realizes {C : context} {poly : Bool} {vals : List code.StackType}
    {a b : List valtype} (hr : Sequence.Realizes poly vals a)
    (h : Instrs_ok C [] (.mk_functype (.mk_list a) (.mk_list b))) :
    Sequence.Realizes poly vals b := realizes_mono hr (empty_sub h)

end Itasca.DeclarativeComplete

end

/-! ## Stack -/

section

/-!
# Operand stack primitives

Specifications of the extracted stack helpers used by every instruction handler: `code.push_val`,
`code.pop_stack_type`, `code.pop_with_type`, `code.pop_types` and `code.push_types`. They describe
the effect on `st.vals` at concrete operands, and in polymorphic frames, where popping never
consumes operands or fails.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `code.push_val` appends one operand. -/
@[step]
theorem code.push_val.spec (st : code.OpIterState) (t : code.StackType)
    (hsize : st.vals.val.length < Usize.max) :
    code.push_val st t ⦃ st' =>
      st'.vals.val = st.vals.val ++ [t] ∧ st'.ctrls = st.ctrls ∧ st'.pos = st.pos ⦄ := by
  unfold code.push_val
  step*

/-- A pop with the last operand above the current frame base returns that operand and removes it. -/
@[step]
theorem code.pop_stack_type.above_base (st : code.OpIterState)
    (pre : List code.StackType) (t : code.StackType)
    (hvals : st.vals.val = pre ++ [t])
    (hbase : (Control.base st).val ≤ pre.length) :
    code.pop_stack_type st ⦃ r =>
      r.1 = .Ok t ∧ r.2.vals.val = pre ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  obtain ⟨_, hb, rfl⟩ := WP.spec_imp_exists (code.cur_base.spec st)
  have hne : alloc.vec.Vec.len st.vals ≠ Control.base st := by scalar_tac
  simp only [code.pop_stack_type, hb, bind_ok, hne, ↓reduceIte]
  simp [alloc.vec.Vec.pop, hvals]

/-- `code.push_types_loop` appends the remaining types in order. -/
@[step]
theorem code.push_types_loop.spec (st : code.OpIterState)
    (ts : Slice wasm_types.ValueType) (i : Usize)
    (hi : i.val ≤ ts.val.length)
    (hsize : st.vals.val.length + (ts.val.length - i.val) ≤ Usize.max) :
    code.push_types_loop st ts i ⦃ st' =>
      st'.vals.val = st.vals.val ++ (ts.val.drop i.val).map code.StackType.Val ∧
      st'.ctrls = st.ctrls ∧ st'.pos = st.pos ⦄ := by
  unfold code.push_types_loop
  apply loop.spec_decr_nat (fun p => ts.val.length - p.2.val)
    (fun p => i.val ≤ p.2.val ∧ p.2.val ≤ ts.val.length ∧
      p.1.vals.val ++ (ts.val.drop p.2.val).map code.StackType.Val =
        st.vals.val ++ (ts.val.drop i.val).map code.StackType.Val ∧
      p.1.vals.val.length + (ts.val.length - p.2.val) ≤ Usize.max ∧
      p.1.ctrls = st.ctrls ∧ p.1.pos = st.pos)
  · rintro ⟨s, j⟩ ⟨hij, hj, hv, hb, hc, hp⟩
    dsimp only at hij hj hv hb hc hp
    unfold code.push_types_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : j.val = ts.val.length := by scalar_tac
      simp [heq] at hv
      simp [hv, hc, hp]
    · rename_i hmore
      have hlt : j.val < ts.val.length := by scalar_tac
      have hcapacity : s.vals.val.length < Usize.max := by omega
      step
      step
      step
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try scalar_tac
      rw [st1_post, i2_post, vt_post, ← hv]
      simp only [List.append_assoc, List.singleton_append]
      rw [List.drop_eq_getElem_cons hlt, List.map_cons]
  · exact ⟨Nat.le_refl _, hi, rfl, hsize, rfl, rfl⟩

/-- `code.push_types` appends all the types in order. -/
@[step]
theorem code.push_types.spec (st : code.OpIterState) (ts : Slice wasm_types.ValueType)
    (hsize : st.vals.val.length + ts.val.length ≤ Usize.max) :
    code.push_types st ts ⦃ st' =>
      st'.vals.val = st.vals.val ++ ts.val.map code.StackType.Val ∧
      st'.ctrls = st.ctrls ∧ st'.pos = st.pos ⦄ := by
  simpa using code.push_types_loop.spec st ts 0#usize (by simp) (by simpa using hsize)

end Itasca

end

/-! ## StackSemantics -/

section

/-!
# Stack operation semantics

Describes the observable outcome of the extracted pops on a frame's operand segment
(`StackSemantics.Popped`, `PopResult`, `TypedPopResult`). `code.pop_stack_type.segment`,
`code.pop_with_type.segment`, `code.pop_with_type.realizes` and `code.pop_types.realizes` state
the outcome for the current frame and relate it to `Sequence.Realizes`, and the `.total` theorems
show that the pops terminate and keep `Control.Shape` for every outcome.
-/

open Aeneas Aeneas.Std

namespace Itasca.Sequence

/-- Inverts `Realizes.snoc`: a realization of a stack with a pushed operand splits into a
realization of the rest and the type of the operand. -/
theorem Realizes.snoc_inv {poly : Bool} {vals : List code.StackType}
    {t : code.StackType} {ts : List valtype} (h : Realizes poly (vals ++ [t]) ts) :
    ∃ front u, ts = front ++ [u] ∧ Realizes poly vals front ∧ Accepts t u := by
  obtain ⟨front, suffix, hf, hs, rfl⟩ := h
  rcases List.eq_nil_or_concat' suffix with hnil | ⟨rest, u, hsnoc⟩
  · have hlen := hs.length_eq
    simp [hnil] at hlen
  · subst suffix
    have hr : List.Forall₂ Accepts (t :: vals.reverse) (u :: rest.reverse) := by
      simpa using List.rel_reverse hs
    cases hr with
    | cons ht htail =>
      exact ⟨front ++ rest, u, (List.append_assoc ..).symm,
        ⟨front, rest, hf, List.forall₂_reverse_iff.mp htail, rfl⟩, ht⟩

end Itasca.Sequence

namespace Itasca.Control

/-- Every control frame's value stack base is at most the current frame base. -/
theorem Shape.frame_base_le {st : code.OpIterState} (h : Shape st)
    (c : code.Ctrl) (hc : c ∈ st.ctrls.val) :
    c.value_stack_base.val ≤ (base st).val := by
  rcases List.eq_nil_or_concat' st.ctrls.val with hnil | ⟨cs, last, hlast⟩
  · simp [hnil] at hc
  · have hord := h.ordered
    rw [hlast, List.pairwise_append] at hord
    simp only [base, hlast, List.getLast?_concat]
    rw [hlast, List.mem_append] at hc
    rcases hc with hc | hc
    · exact hord.2.2 c hc last (by simp)
    · have heq : c = last := by simpa using hc
      simp [heq]

/-- Replacing the operands preserves `Shape` when the current frame base is still within them. -/
theorem Shape.replace_operands {st st' : code.OpIterState} (h : Shape st)
    (hctrls : st'.ctrls = st.ctrls)
    (hbase : (base st).val ≤ st'.vals.val.length) : Shape st' := by
  constructor
  · simpa [hctrls] using h.ordered
  · intro c hc
    exact Nat.le_trans (h.frame_base_le c (by simpa [hctrls] using hc)) hbase

end Itasca.Control

namespace Itasca.StackSemantics

/-- A successful pop either removes an explicit operand or, in a polymorphic frame with no
operands, yields `Bot`. -/
inductive Popped : Bool → List code.StackType → code.StackType → List code.StackType → Prop
  | explicit (poly : Bool) (rest : List code.StackType) (t : code.StackType) :
      Popped poly (rest ++ [t]) t rest
  | implicit : Popped true [] .Bot []

theorem Popped.length {poly before t after} (h : Popped poly before t after) :
    after.length ≤ before.length := by
  cases h <;> simp

theorem Popped.realizes {poly before t after} (h : Popped poly before t after)
    (ts : List valtype) (u : valtype) (ht : Sequence.Accepts t u)
    (hs : Sequence.Realizes poly after ts) :
    Sequence.Realizes poly before (ts ++ [u]) := by
  cases h with
  | explicit => exact hs.snoc _ _ ht
  | implicit => exact Sequence.realizes_polymorphic_empty _

/-- The outcome of the untyped pop: a `Popped` step on success, and `EmptyStack` only for an empty
reachable frame. -/
def PopResult (poly : Bool) (before : List code.StackType)
    (r : core.result.Result code.StackType error.OpError) (after : List code.StackType) : Prop :=
  match r with
  | .Ok t => Popped poly before t after
  | .Err e => e = .EmptyStack ∧ poly = false ∧ before = [] ∧ after = []

theorem PopResult.length {poly before r after} (h : PopResult poly before r after) :
    after.length ≤ before.length := by
  cases r with
  | Ok t => exact Popped.length h
  | Err e => rcases h with ⟨_, _, rfl, rfl⟩; simp

/-- The outcome of the typed pop: it rejects only an empty reachable frame (`EmptyStack`) or an
incompatible operand (`TypeMismatch`). -/
def TypedPopResult (poly : Bool) (before : List code.StackType) (expected : wasm_types.ValueType)
    (r : core.result.Result code.StackType error.OpError) (after : List code.StackType) : Prop :=
  match r with
  | .Ok t => Popped poly before t after ∧ Sequence.Accepts t (Translate.valueType expected)
  | .Err e =>
      (e = .EmptyStack ∧ poly = false ∧ before = [] ∧ after = []) ∨
      (e = .TypeMismatch ∧ ∃ t, Popped poly before t after ∧
        ¬ Sequence.Accepts t (Translate.valueType expected))

theorem TypedPopResult.length {poly before expected r after}
    (h : TypedPopResult poly before expected r after) : after.length ≤ before.length := by
  cases r with
  | Ok t => exact h.1.length
  | Err e =>
    rcases h with ⟨_, _, rfl, rfl⟩ | ⟨_, t, hp, _⟩
    · simp
    · exact hp.length

/-- A successful typed pop turns a realization of the remaining stack into one of the original
stack with the expected type pushed. -/
theorem TypedPopResult.realizes {poly before expected t after}
    (h : TypedPopResult poly before expected (.Ok t) after)
    (ts : List valtype) (hs : Sequence.Realizes poly after ts) :
    Sequence.Realizes poly before (ts ++ [Translate.valueType expected]) :=
  h.1.realizes ts _ h.2 hs

end Itasca.StackSemantics

namespace Itasca

/-- `code.pop_stack_type` on the current frame's operand segment has a `PopResult` outcome, for any
mix of concrete and `Bot` operands. -/
@[step]
theorem code.pop_stack_type.segment (st : code.OpIterState)
    (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length) :
    code.pop_stack_type st ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧
        StackSemantics.PopResult (Control.polymorphic st) segment r.1 rest ⦄ := by
  rcases List.eq_nil_or_concat' segment with hnil | ⟨rest, t, hsnoc⟩
  · subst segment
    have hb : alloc.vec.Vec.len st.vals = Control.base st := by scalar_tac
    rw [code.pop_stack_type.at_base st hb]
    cases hp : Control.polymorphic st
    · simp only [WP.spec_ok]
      exact ⟨rfl, rfl, [], hvals, rfl, rfl, rfl, rfl⟩
    · simp only [↓reduceIte, WP.spec_ok]
      exact ⟨trivial, trivial, [], hvals, .implicit⟩
  · have hv : st.vals.val = (outer ++ rest) ++ [t] := by
      simpa [hsnoc, List.append_assoc] using hvals
    obtain ⟨⟨res, st'⟩, hr, hok, hv', hc, hp⟩ :=
      WP.spec_imp_exists (code.pop_stack_type.above_base st (outer ++ rest) t hv
        (by simp [hbase]))
    dsimp only at hok hv' hc hp
    rw [hr, WP.spec_ok]
    exact ⟨hc, hp, rest, hv', by simpa [hok, hsnoc, StackSemantics.PopResult] using
      StackSemantics.Popped.explicit (Control.polymorphic st) rest t⟩

/-- `code.pop_with_type` on the current frame's operand segment has a `TypedPopResult` outcome. -/
@[step]
theorem code.pop_with_type.segment (st : code.OpIterState)
    (outer segment : List code.StackType) (expected : wasm_types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length) :
    code.pop_with_type st expected ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧
        StackSemantics.TypedPopResult (Control.polymorphic st) segment expected r.1 rest ⦄ := by
  obtain ⟨⟨res, st'⟩, hr, hc, hp, rest, hv, hout⟩ :=
    WP.spec_imp_exists (code.pop_stack_type.segment st outer segment hvals hbase)
  dsimp only at hc hp hv hout
  cases res with
  | Err e =>
    simp only [StackSemantics.PopResult] at hout
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err e, st'), ?_, hc, hp, rest, hv, Or.inl hout⟩
    simp [code.pop_with_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok t =>
    cases t with
    | Bot =>
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok .Bot, st'), ?_, hc, hp, rest, hv, hout, trivial⟩
      simp [code.pop_with_type, hr, core.result.Result.Insts.CoreOpsTry.branch]
    | Val actual =>
      by_cases heq : Translate.valueType actual = Translate.valueType expected
      · rw [WP.spec_equiv_exists]
        refine ⟨(.Ok (.Val actual), st'), ?_, hc, hp, rest, hv, hout, heq.symm⟩
        simp [code.pop_with_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
          Translate.valueType_eq, heq]
      · rw [WP.spec_equiv_exists]
        refine ⟨(.Err .TypeMismatch, st'), ?_, hc, hp, rest, hv,
          Or.inr ⟨rfl, .Val actual, hout, ?_⟩⟩
        · simp [code.pop_with_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
            Translate.valueType_eq, heq]
        · exact fun h => heq h.symm

/-- `code.pop_with_type` shrinks the segment, and on success its operand is accepted and
realizations of the remainder extend to the original segment. Errors are `EmptyStack` or
`TypeMismatch`. -/
theorem code.pop_with_type.realizes (st : code.OpIterState)
    (outer segment : List code.StackType) (expected : wasm_types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length) :
    code.pop_with_type st expected ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
        match r.1 with
        | .Ok t => Sequence.Accepts t (Translate.valueType expected) ∧
          ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
            Sequence.Realizes (Control.polymorphic st) segment (ts ++ [Translate.valueType expected])
        | .Err e => e = .EmptyStack ∨ e = .TypeMismatch ⦄ := by
  obtain ⟨⟨res, st'⟩, hr, hc, hp, rest, hv, hout⟩ :=
    WP.spec_imp_exists (code.pop_with_type.segment st outer segment expected hvals hbase)
  dsimp only at hc hp hv hout
  rw [hr, WP.spec_ok]
  refine ⟨hc, hp, rest, hv, hout.length, ?_⟩
  cases res with
  | Ok t => exact ⟨hout.2, fun ts hs => hout.realizes ts hs⟩
  | Err e =>
    rcases hout with h | h
    · exact .inl h.1
    · exact .inr h.1

/-- `code.pop_types` shrinks the segment, and on success realizations of the remainder extend to
the original segment with the expected types appended. Errors are `EmptyStack` or
`TypeMismatch`. -/
theorem code.pop_types.realizes (st : code.OpIterState)
    (outer segment : List code.StackType) (expected : Slice wasm_types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length) :
    code.pop_types st expected ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
        match r.1 with
        | .Ok _ => ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
            Sequence.Realizes (Control.polymorphic st) segment
              (ts ++ expected.val.map Translate.valueType)
        | .Err e => e = .EmptyStack ∨ e = .TypeMismatch ⦄ := by
  unfold code.pop_types code.pop_types_loop
  apply loop.spec_decr_nat (fun p => p.2.val)
    (fun p => p.2.val ≤ expected.val.length ∧ p.1.ctrls = st.ctrls ∧ p.1.pos = st.pos ∧
      ∃ current, p.1.vals.val = outer ++ current ∧ current.length ≤ segment.length ∧
        ∀ ts, Sequence.Realizes (Control.polymorphic st) current ts →
          Sequence.Realizes (Control.polymorphic st) segment
            (ts ++ (expected.val.drop p.2.val).map Translate.valueType))
  · rintro ⟨s, j⟩ ⟨hj, hc, hp, current, hv, hlen, htransfer⟩
    dsimp only at hj hc hp hv hlen htransfer
    unfold code.pop_types_loop.body
    dsimp only
    split
    · rename_i hzero
      simp only [WP.spec_ok]
      refine ⟨hc, hp, current, hv, hlen, ?_⟩
      simpa [hzero] using htransfer
    · rename_i hnz
      step
      have hidx : i1.val < expected.val.length := by scalar_tac
      step
      have hb : (Control.base s).val = outer.length := by
        simpa [Control.base, hc] using hbase
      have hpoly : Control.polymorphic s = Control.polymorphic st := by
        simp [Control.polymorphic, hc]
      obtain ⟨⟨res, s'⟩, hr, hcout, hpout, rest, hvout, hlenout, hresult⟩ :=
        WP.spec_imp_exists (code.pop_with_type.realizes s outer current vt hv hb)
      dsimp only at hcout hpout hvout hlenout hresult
      rw [hpoly] at hresult
      cases res with
      | Err e =>
        rw [WP.spec_equiv_exists]
        refine ⟨.done (.Err e, s'), ?_, hcout.trans hc, hpout.trans hp,
          rest, hvout, Nat.le_trans hlenout hlen, hresult⟩
        simp [hr, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok t =>
        rw [WP.spec_equiv_exists]
        refine ⟨.cont (s', i1), ?_, ?_⟩
        · simp [hr, core.result.Result.Insts.CoreOpsTry.branch]
        dsimp only
        refine ⟨?_, hcout.trans hc, hpout.trans hp, ⟨rest, hvout,
          Nat.le_trans hlenout hlen, ?_⟩, ?_⟩
        · scalar_tac
        · intro ts hs
          have hs' := htransfer (ts ++ [Translate.valueType vt]) (hresult.2 ts hs)
          have hsucc : j.val = i1.val + 1 := by scalar_tac
          rw [List.drop_eq_getElem_cons hidx, List.map_cons, ← hsucc]
          simpa only [List.append_assoc, List.singleton_append, vt_post] using hs'
        · scalar_tac
  · refine ⟨by simp, rfl, rfl, segment, hvals, Nat.le_refl _, ?_⟩
    intro ts hs
    simpa using hs

/-- `code.pop_stack_type` terminates and preserves `Control.Shape`, and fails only with
`EmptyStack`. -/
theorem code.pop_stack_type.total (st : code.OpIterState) (hshape : Control.Shape st) :
    code.pop_stack_type st ⦃ r =>
      Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      r.2.vals.val.length ≤ st.vals.val.length ∧
      (∀ e, r.1 = .Err e → e = .EmptyStack) ⦄ := by
  let n := (Control.base st).val
  have hn : n ≤ st.vals.val.length := hshape.base_le
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hout⟩ :=
    WP.spec_imp_exists (code.pop_stack_type.segment st (st.vals.val.take n) (st.vals.val.drop n)
      (List.take_append_drop ..).symm (by simp [n, Nat.min_eq_left hn]))
  dsimp only at hc hp hv hout
  have hb : (Control.base st).val ≤ s.vals.val.length := by simp [hv, n, Nat.min_eq_left hn]
  have hlen := hout.length
  rw [hr, WP.spec_ok]
  refine ⟨hshape.replace_operands hc hb, hc, hp, ?_, ?_⟩
  · simp only [hv, List.length_append, List.length_take, List.length_drop] at *
    omega
  · intro e he
    cases res with
    | Ok t => simp at he
    | Err e' => cases he; exact hout.1

/-- `code.pop_with_type` terminates and preserves `Control.Shape`, including for `Bot` and
mismatched operands. -/
theorem code.pop_with_type.total (st : code.OpIterState) (expected : wasm_types.ValueType)
    (hshape : Control.Shape st) :
    code.pop_with_type st expected ⦃ r =>
      Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      r.2.vals.val.length ≤ st.vals.val.length ∧
      (∀ e, r.1 = .Err e → e = .EmptyStack ∨ e = .TypeMismatch) ⦄ := by
  let n := (Control.base st).val
  have hn : n ≤ st.vals.val.length := hshape.base_le
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hlen, hout⟩ :=
    WP.spec_imp_exists (code.pop_with_type.realizes st (st.vals.val.take n) (st.vals.val.drop n)
      expected (List.take_append_drop ..).symm (by simp [n, Nat.min_eq_left hn]))
  dsimp only at hc hp hv hlen hout
  have hb : (Control.base st).val ≤ s.vals.val.length := by simp [hv, n, Nat.min_eq_left hn]
  rw [hr, WP.spec_ok]
  refine ⟨hshape.replace_operands hc hb, hc, hp, ?_, ?_⟩
  · simp only [hv, List.length_append, List.length_take, List.length_drop] at *
    omega
  · intro e he
    cases res with
    | Ok t => simp at he
    | Err e' => cases he; exact hout

/-- `code.pop_types` terminates and preserves `Control.Shape` on acceptance and rejection. -/
theorem code.pop_types.total (st : code.OpIterState) (expected : Slice wasm_types.ValueType)
    (hshape : Control.Shape st) :
    code.pop_types st expected ⦃ r =>
      Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      r.2.vals.val.length ≤ st.vals.val.length ∧
      (∀ e, r.1 = .Err e → e = .EmptyStack ∨ e = .TypeMismatch) ⦄ := by
  let n := (Control.base st).val
  have hn : n ≤ st.vals.val.length := hshape.base_le
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hlen, hout⟩ :=
    WP.spec_imp_exists (code.pop_types.realizes st (st.vals.val.take n) (st.vals.val.drop n)
      expected (List.take_append_drop ..).symm (by simp [n, Nat.min_eq_left hn]))
  dsimp only at hc hp hv hlen hout
  have hb : (Control.base st).val ≤ s.vals.val.length := by simp [hv, n, Nat.min_eq_left hn]
  rw [hr, WP.spec_ok]
  refine ⟨hshape.replace_operands hc hb, hc, hp, ?_, ?_⟩
  · simp only [hv, List.length_append, List.length_take, List.length_drop] at *
    omega
  · intro e he
    cases res with
    | Ok t => simp at he
    | Err e' => cases he; exact hout

end Itasca

end

/-! ## StackComplete -/

section

/-!
# Stack operation completeness

Completeness of the extracted pops: if the validator stack realizes a declarative stack with the
expected types on top, then `code.pop_stack_type.complete`, `code.pop_with_type.complete` and
`code.pop_types.complete` show that the pop succeeds and the remainder realizes the rest.
-/

open Aeneas Aeneas.Std

set_option maxRecDepth 2048

namespace Itasca.StackSemantics

/-- A pop from a stack that realizes a non-empty declarative stack accepts its last type, and the
remainder realizes the rest. -/
theorem Popped.complete {poly before t after} (h : Popped poly before t after)
    {ts : List valtype} {u : valtype}
    (hr : Sequence.Realizes poly before (ts ++ [u])) :
    Sequence.Accepts t u ∧ Sequence.Realizes poly after ts := by
  cases h with
  | explicit poly rest t =>
    obtain ⟨front, last, he, hf, ht⟩ := Sequence.Realizes.snoc_inv hr
    have hs : ts = front ∧ u = last := by simpa using he
    rcases hs with ⟨rfl, rfl⟩
    exact ⟨ht, hf⟩
  | implicit => exact ⟨trivial, Sequence.realizes_polymorphic_empty ts⟩

/-- An empty reachable frame realizes no non-empty declarative stack. -/
theorem realizes_nonempty {ts : List valtype} {u : valtype} :
    ¬ Sequence.Realizes false [] (ts ++ [u]) := by
  intro h
  have he := (Sequence.realizes_empty _).mp h
  simp at he

end Itasca.StackSemantics

namespace Itasca

/-- If the segment realizes a stack ending in `u`, `code.pop_stack_type` succeeds, with an implicit
`Bot` at the base of a polymorphic frame, and the remainder realizes the rest. -/
theorem code.pop_stack_type.complete (st : code.OpIterState)
    (outer segment : List code.StackType) (ts : List valtype) (u : valtype)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (ht : Sequence.Realizes (Control.polymorphic st) segment (ts ++ [u])) :
    ∃ t s rest, code.pop_stack_type st = .ok (.Ok t, s) ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ s.vals.val = outer ++ rest ∧
      rest.length ≤ segment.length ∧ Sequence.Accepts t u ∧
      Sequence.Realizes (Control.polymorphic st) rest ts := by
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hout⟩ :=
    WP.spec_imp_exists (code.pop_stack_type.segment st outer segment hvals hbase)
  dsimp only at hc hp hv hout
  cases res with
  | Ok t =>
    obtain ⟨ha, ht'⟩ := hout.complete ht
    exact ⟨t, s, rest, hr, hc, hp, hv, hout.length, ha, ht'⟩
  | Err e =>
    obtain ⟨_, hpoly, hnil, _⟩ := hout
    rw [hpoly, hnil] at ht
    exact (StackSemantics.realizes_nonempty ht).elim

/-- If the segment realizes a stack ending in the translation of `u`, `code.pop_with_type`
succeeds, and the remainder realizes the rest. -/
theorem code.pop_with_type.complete (st : code.OpIterState)
    (outer segment : List code.StackType) (ts : List valtype) (u : wasm_types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (ht : Sequence.Realizes (Control.polymorphic st) segment
      (ts ++ [Translate.valueType u])) :
    ∃ t s rest, code.pop_with_type st u = .ok (.Ok t, s) ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ s.vals.val = outer ++ rest ∧
      rest.length ≤ segment.length ∧ Sequence.Accepts t (Translate.valueType u) ∧
      Sequence.Realizes (Control.polymorphic st) rest ts := by
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hout⟩ :=
    WP.spec_imp_exists (code.pop_with_type.segment st outer segment u hvals hbase)
  dsimp only at hc hp hv hout
  cases res with
  | Ok t =>
    obtain ⟨ha, ht'⟩ := hout.1.complete ht
    exact ⟨t, s, rest, hr, hc, hp, hv, hout.length, ha, ht'⟩
  | Err e =>
    rcases hout with ⟨_, hpoly, hnil, _⟩ | ⟨_, t, hpop, hbad⟩
    · rw [hpoly, hnil] at ht
      exact (StackSemantics.realizes_nonempty ht).elim
    · exact (hbad (hpop.complete ht).1).elim

/-- If the segment realizes a stack ending in the translation of `expected`, `code.pop_types`
succeeds, and the remainder realizes the rest. -/
theorem code.pop_types.complete (st : code.OpIterState)
    (outer segment : List code.StackType) (ts : List valtype)
    (expected : Slice wasm_types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (ht : Sequence.Realizes (Control.polymorphic st) segment
      (ts ++ expected.val.map Translate.valueType)) :
    code.pop_types st expected ⦃ r => r.1 = .Ok () ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
        Sequence.Realizes (Control.polymorphic st) rest ts ⦄ := by
  unfold code.pop_types code.pop_types_loop
  apply loop.spec_decr_nat (fun p => p.2.val)
    (fun p => p.2.val ≤ expected.val.length ∧ p.1.ctrls = st.ctrls ∧ p.1.pos = st.pos ∧
      ∃ current, p.1.vals.val = outer ++ current ∧ current.length ≤ segment.length ∧
        Sequence.Realizes (Control.polymorphic st) current
          (ts ++ (expected.val.take p.2.val).map Translate.valueType))
  · rintro ⟨s, j⟩ ⟨hj, hc, hp, current, hv, hlen, htypes⟩
    dsimp only at hj hc hp hv hlen htypes
    unfold code.pop_types_loop.body
    dsimp only
    split
    · rename_i hzero
      simp only [WP.spec_ok]
      exact ⟨trivial, hc, hp, current, hv, hlen, by simpa [hzero] using htypes⟩
    · rename_i hnz
      step
      have hidx : i1.val < expected.val.length := by scalar_tac
      step
      have hb : (Control.base s).val = outer.length := by
        simpa [Control.base, hc] using hbase
      have hpoly : Control.polymorphic s = Control.polymorphic st := by
        simp [Control.polymorphic, hc]
      have hsucc : j.val = i1.val + 1 := by scalar_tac
      have htake : expected.val.take j.val = expected.val.take i1.val ++ [vt] := by
        rw [hsucc, List.take_succ_eq_append_getElem hidx, vt_post]
      have hpop : Sequence.Realizes (Control.polymorphic s) current
          ((ts ++ (expected.val.take i1.val).map Translate.valueType) ++
            [Translate.valueType vt]) := by
        simpa [hpoly, htake, List.map_append, List.append_assoc] using htypes
      obtain ⟨t, s', rest, hr, hc', hp', hv', hlen', haccept, ht'⟩ :=
        code.pop_with_type.complete s outer current _ vt hv hb hpop
      rw [WP.spec_equiv_exists]
      refine ⟨.cont (s', i1), ?_, ?_⟩
      · simp [hr, core.result.Result.Insts.CoreOpsTry.branch]
      dsimp only
      refine ⟨?_, hc'.trans hc, hp'.trans hp, ⟨rest, hv', hlen'.trans hlen, ?_⟩, ?_⟩
      · exact Nat.le_trans (Nat.le_of_lt hidx) (Nat.le_refl _)
      · rw [hpoly] at ht'; exact ht'
      · omega
  · exact ⟨by simp, rfl, rfl, segment, hvals, Nat.le_refl _, by simpa using ht⟩

end Itasca

end

/-! ## ResumePrefix -/

section

/-!
# Suspended prefixes

`realizes_append_concrete` characterizes realizations of a stack with concrete operands
appended, as when a child block resumes its parent's typed prefix.
-/

open Aeneas Aeneas.Std

namespace Itasca.Sequence

private theorem accepts_concrete (rs : List wasm_types.ValueType) (ts : List valtype) :
    List.Forall₂ Sequence.Accepts (rs.map code.StackType.Val) ts ↔
      ts = rs.map Translate.valueType := by
  induction rs generalizing ts with
  | nil => simp
  | cons r rs ih =>
    cases ts <;> simp [Sequence.Accepts, ih]

/-- A realization of a stack with concrete operands appended is a realization of the stack
followed by those operands' types. -/
theorem realizes_append_concrete (poly : Bool) (vals : List code.StackType)
    (rs : List wasm_types.ValueType) (ts : List valtype) :
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

end Itasca.Sequence

end

/-! ## SimplePrefix -/

section

/-!
# Prefixes for simple instructions

`StackSemantics.NumericEffect` gives the shared stack interpretation of a checked numeric
operation, and `code.read_conversion.segment` and `code.read_binary.segment` describe the operand
handlers on arbitrary frame segments.
-/

open Aeneas Aeneas.Std

namespace Itasca.StackSemantics

/-- The effect of a checked numeric operation: the result is pushed, and a stack realizing the
remainder extends to one with the input types on top. -/
def NumericEffect (poly : Bool) (before : List code.StackType)
    (inputs : List wasm_types.ValueType) (output : wasm_types.ValueType)
    (after : List code.StackType) : Prop :=
  ∃ rest, after = rest ++ [.Val output] ∧
    ∀ ts, Sequence.Realizes poly rest ts →
      Sequence.Realizes poly before (ts ++ inputs.map Translate.valueType)

end Itasca.StackSemantics

namespace Itasca

/-- `code.read_conversion` on an arbitrary frame segment has a `NumericEffect` outcome, or rejects
with `EmptyStack` or `TypeMismatch`. -/
theorem code.read_conversion.segment (st : code.OpIterState)
    (outer segment : List code.StackType) (input output : wasm_types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_conversion st input output ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
        match r.1 with
        | .Ok _ => StackSemantics.NumericEffect (Control.polymorphic st) segment [input] output rest
        | .Err e => e = .EmptyStack ∨ e = .TypeMismatch ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hlen, hout⟩ :=
    WP.spec_imp_exists (code.pop_with_type.realizes st outer segment input hvals hbase)
  dsimp only at hc hp hv hlen hout
  cases res with
  | Err e =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err e, s), ?_, hc, hp, rest, hv, by omega, hout⟩
    simp [code.read_conversion, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok t =>
    have hcap : s.vals.val.length < Usize.max := by
      simp only [hvals, List.length_append] at hsize
      simp only [hv, List.length_append]
      omega
    obtain ⟨s', hpush, hv', hc', hp'⟩ :=
      WP.spec_imp_exists (code.push_val.spec s (.Val output) hcap)
    rw [WP.spec_equiv_exists]
    refine ⟨(.Ok (), s'), ?_, hc'.trans hc, hp'.trans hp, rest ++ [.Val output],
      ?_, by simpa using hlen, rest, rfl, ?_⟩
    · simp [code.read_conversion, hr, core.result.Result.Insts.CoreOpsTry.branch, hpush]
    · simpa [List.append_assoc, hv] using hv'
    · simpa using hout.2

/-- `code.read_binary` on an arbitrary frame segment, with any mix of explicit and polymorphic
operands, has a `NumericEffect` outcome, or rejects with `EmptyStack` or `TypeMismatch`. -/
theorem code.read_binary.segment (st : code.OpIterState)
    (outer segment : List code.StackType) (input output : wasm_types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_binary st input output ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
        match r.1 with
        | .Ok _ => StackSemantics.NumericEffect (Control.polymorphic st) segment [input, input] output rest
        | .Err e => e = .EmptyStack ∨ e = .TypeMismatch ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hc, hp, middle, hv, hlen, hout⟩ :=
    WP.spec_imp_exists (code.pop_with_type.realizes st outer segment input hvals hbase)
  dsimp only at hc hp hv hlen hout
  cases res with
  | Err e =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err e, s), ?_, hc, hp, middle, hv, by omega, hout⟩
    simp [code.read_binary, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok t =>
    have hb : (Control.base s).val = outer.length := by simpa [Control.base, hc] using hbase
    have hpoly : Control.polymorphic s = Control.polymorphic st := by simp [Control.polymorphic, hc]
    obtain ⟨⟨res', s'⟩, hr', hc', hp', rest, hv', hlen', hout'⟩ :=
      WP.spec_imp_exists (code.pop_with_type.realizes s outer middle input hv hb)
    dsimp only at hc' hp' hv' hlen' hout'
    rw [hpoly] at hout'
    cases res' with
    | Err e =>
      rw [WP.spec_equiv_exists]
      refine ⟨(.Err e, s'), ?_, hc'.trans hc, hp'.trans hp, rest, hv', by omega, hout'⟩
      simp [code.read_binary, hr, hr', core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok t' =>
      have hcap : s'.vals.val.length < Usize.max := by
        simp only [hvals, List.length_append] at hsize
        simp only [hv', List.length_append]
        omega
      obtain ⟨s'', hpush, hv'', hc'', hp''⟩ :=
        WP.spec_imp_exists (code.push_val.spec s' (.Val output) hcap)
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok (), s''), ?_, hc''.trans (hc'.trans hc), hp''.trans (hp'.trans hp),
        rest ++ [.Val output], ?_, ?_, rest, rfl, ?_⟩
      · simp [code.read_binary, hr, hr', core.result.Result.Insts.CoreOpsTry.branch, hpush]
      · simpa [List.append_assoc, hv'] using hv''
      · simp only [List.length_append, List.length_singleton]; omega
      · intro ts hs
        simpa [List.append_assoc] using hout.2 _ (hout'.2 ts hs)

end Itasca

end
