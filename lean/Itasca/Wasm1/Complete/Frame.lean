import Itasca.Wasm1.ProfileSyntax
import Itasca.Spec.TypingInversion
import Itasca.Handler.StackComplete
import Itasca.Binary.Wasm1.EncodingComplete

/-!
# Concrete frames for forward execution

`Frame st` decomposes the control and value stacks of an extracted `code.OpIterState` into
parent frames, the current frame, the outer operands and the current frame's operands.
`Frame.Output` states what a frame may become after executing instructions, and `StepResult`
is the common conclusion of the per-instruction completeness theorems in `Wasm1/Complete/`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1.Completeness

/-- The concrete current-frame decomposition used in forward execution proofs. -/
structure Frame (st : code.OpIterState) where
  parents : List code.Ctrl
  current : code.Ctrl
  outer : List code.StackType
  operands : List code.StackType
  ctrls : st.ctrls.val = parents ++ [current]
  vals : st.vals.val = outer ++ operands
  base : current.value_stack_base.val = outer.length

theorem Frame.base_eq {st} (f : Frame st) : (Control.base st).val = f.outer.length := by
  simp [Control.base, f.ctrls, f.base]

theorem Frame.poly_eq {st} (f : Frame st) :
    Control.polymorphic st = f.current.polymorphic_base := by
  simp [Control.polymorphic, f.ctrls]

/-- Executing an instruction list in one frame may change its polymorphism,
but preserves all parent frames and the current frame's fixed fields. -/
def Frame.Output {st} (f : Frame st) (out : List valtype) (s : code.OpIterState) : Prop :=
  ∃ poly operands,
    s.ctrls.val = f.parents ++ [{f.current with polymorphic_base := poly}] ∧
    s.vals.val = f.outer ++ operands ∧ Sequence.Realizes poly operands out

theorem Frame.output_of_same_ctrls {st} (f : Frame st) {out : List valtype}
    {s : code.OpIterState} {operands : List code.StackType}
    (hc : s.ctrls = st.ctrls) (hv : s.vals.val = f.outer ++ operands)
    (ht : Sequence.Realizes (Control.polymorphic st) operands out) : f.Output out s := by
  refine ⟨f.current.polymorphic_base, operands, ?_, hv, ?_⟩
  · simpa [hc] using f.ctrls
  · simpa [f.poly_eq] using ht

theorem Frame.output_self {st} (f : Frame st) {out : List valtype}
    (ht : Sequence.Realizes f.current.polymorphic_base f.operands out) : f.Output out st := by
  exact ⟨f.current.polymorphic_base, f.operands, by simpa using f.ctrls, f.vals, ht⟩

/-- A state satisfying `Frame.Output` has a concrete frame of its own with the same parents,
outer operands and fixed fields, ready for the next typing derivation. -/
theorem Frame.Output.next {st} {f : Frame st} {out : List valtype} {s : code.OpIterState}
    (h : f.Output out s) :
    ∃ g : Frame s, g.parents = f.parents ∧ g.outer = f.outer ∧
      g.current.kind = f.current.kind ∧ g.current.signature = f.current.signature ∧
      g.current.value_stack_base = f.current.value_stack_base ∧
      Sequence.Realizes g.current.polymorphic_base g.operands out := by
  obtain ⟨poly, operands, hc, hv, ht⟩ := h
  exact ⟨⟨f.parents, {f.current with polymorphic_base := poly}, f.outer, operands,
    hc, hv, f.base⟩, rfl, rfl, rfl, rfl, rfl, ht⟩

theorem Frame.Output.transfer {st s t} {f : Frame st} {g : Frame s}
    {out : List valtype} (h : g.Output out t)
    (hp : g.parents = f.parents) (ho : g.outer = f.outer)
    (hk : g.current.kind = f.current.kind)
    (hsig : g.current.signature = f.current.signature)
    (hbase : g.current.value_stack_base = f.current.value_stack_base) : f.Output out t := by
  obtain ⟨poly, operands, hc, hv, ht⟩ := h
  have he : {g.current with polymorphic_base := poly} =
      {f.current with polymorphic_base := poly} := by
    cases hg : g.current
    cases hf : f.current
    simp only [hg, hf] at hk hsig hbase
    simp_all
  exact ⟨poly, operands, by simpa [hp, he] using hc, by simpa [ho] using hv, ht⟩

/-- Common conclusion of a leaf dispatch after its opcode has been read: `code.step` returns
`Ok` at the cursor `next` and the resulting state realizes the output types. -/
def StepResult {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (opcode : U8) (next : Usize) (out : List valtype) : Prop :=
  ∃ s, code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx opcode () =
      .ok (.Ok (), s, ()) ∧ s.pos = next ∧ f.Output out s ∧
    s.vals.val.length ≤ st.vals.val.length + 1

end Itasca.Wasm1.Completeness
