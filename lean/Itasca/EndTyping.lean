import Itasca.Sequence
import Itasca.End

open Aeneas Aeneas.Std

namespace Itasca

/-- Compose two extracted handlers with the current frame's declarative prefix proof.
The ghost prefix is a hypothesis; this is not a proof of whole-body decoding. -/
theorem code.read_unreachable_and_end_block_typed (st : code.OpIterState)
    (C : context) (hC : wf_context C) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer segment : List code.StackType) (ops : List instr)
    (hshape : Control.Shape st) (hctrls : st.ctrls.val = cs ++ [c])
    (hkind : c.kind = .Block) (hlabels : C.LABELS = Control.labels cs)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : c.value_stack_base.val = outer.length)
    (htyped : Sequence.TypedPrefix
      (Control.labelContext (Control.resultTypes c.block_type) ++ C)
      ops c.polymorphic_base segment)
    (hsize : outer.length + (Control.results c.block_type).length ≤ Usize.max) :
    ∃ unreachable finished,
      code.read_unreachable st = .ok (.Ok (), unreachable) ∧
      code.read_end unreachable = .ok (.Ok (.Block, c.block_type), finished) ∧
      finished.ctrls.val = cs ∧
      finished.vals.val = outer ++ (Control.results c.block_type).map code.StackType.Val ∧
      finished.pos = st.pos ∧ Control.Shape finished ∧
      C.LABELS = Control.labels finished.ctrls.val ∧
      Instr_ok C (.BLOCK (Control.blockType c.block_type) (ops ++ [.UNREACHABLE]))
        (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes c.block_type))) := by
  obtain ⟨unreachable, hu, hvu, hcu, hpu, htu⟩ := code.read_unreachable.prefix st
    (Control.labelContext (Control.resultTypes c.block_type) ++ C)
    (Control.enter_context_wf C hC _) cs c outer segment ops hctrls hvals hbase htyped
  have hsu : Control.Shape unreachable :=
    Control.Shape.unreachable hshape cs c hctrls hcu (by rw [hvu, hbase])
  obtain ⟨finished, he, hce, hve, hpe, hse, _⟩ :=
    code.read_end.polymorphic_context unreachable cs { c with polymorphic_base := true }
      hsu hcu (by simpa [hvu] using hbase.symm) rfl
      (by simp [hkind]) (by simpa [hvu] using hsize)
  refine ⟨unreachable, finished, hu, ?_, hce, ?_, hpe.trans hpu, hse, ?_, ?_⟩
  · simpa [hkind] using he
  · simpa [hvu] using hve
  · simpa [hce] using hlabels
  · exact htu.close_block hC c.block_type (Sequence.realizes_polymorphic_empty _)

/-- Closing a frame with concrete results discharges its block typing obligation. -/
theorem code.read_end.block_typed (st : code.OpIterState) (C : context)
    (hC : wf_context C) (cs : List code.Ctrl) (c : code.Ctrl)
    (outer : List code.StackType) (ops : List instr)
    (hshape : Control.Shape st) (hctrls : st.ctrls.val = cs ++ [c])
    (hkind : c.kind = .Block) (hlabels : C.LABELS = Control.labels cs)
    (hvals : st.vals.val = outer ++ (Control.results c.block_type).map code.StackType.Val)
    (hbase : c.value_stack_base.val = outer.length)
    (htyped : Sequence.TypedPrefix
      (Control.labelContext (Control.resultTypes c.block_type) ++ C)
      ops c.polymorphic_base ((Control.results c.block_type).map code.StackType.Val)) :
    ∃ finished, code.read_end st = .ok (.Ok (.Block, c.block_type), finished) ∧
      finished.ctrls.val = cs ∧ finished.vals = st.vals ∧ finished.pos = st.pos ∧
      Control.Shape finished ∧ C.LABELS = Control.labels finished.ctrls.val ∧
      Instr_ok C (.BLOCK (Control.blockType c.block_type) ops)
        (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes c.block_type))) := by
  obtain ⟨finished, he, hc, hv, hp, hs, _⟩ :=
    code.read_end.concrete_context st cs c outer hshape hctrls hvals hbase.symm (by simp [hkind])
  refine ⟨finished, ?_, hc, hv, hp, hs, ?_, ?_⟩
  · simpa [hkind] using he
  · simpa [hc] using hlabels
  · apply htyped.close_block hC c.block_type
    simpa [Sequence.stackTypes, Control.resultTypes, List.map_map, Function.comp_def] using
      Sequence.realizes_default c.polymorphic_base
        ((Control.results c.block_type).map code.StackType.Val)

end Itasca
