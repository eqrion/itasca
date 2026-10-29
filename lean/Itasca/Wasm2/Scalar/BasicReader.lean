import Itasca.Wasm2.Scalar.ReaderPost
import Itasca.Handler.ScalarConst
import Itasca.Wasm2.Scalar.Prefix
import Itasca.Binary.Wasm1.DeclaredReferences

/-!
Reader facts for constants and terminal scalar instructions, shared by validator
preservation and compiler inversion. Each successful read retains the exact byte
encoding, stack effect, and advancement of the original source prefix. These
results make no assumption about visitor callbacks.
-/

namespace Itasca.Wasm2
open Aeneas Aeneas.Std Itasca

/-- NOP records its opcode while preserving the precise source stack. -/
theorem Pending.nop_reader {data env profile locals index st}
    (p : Pending data env profile locals index st)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_NOP) :
    ReaderPost p st.core .NOP p.current.ctrl.polymorphic_base p.current.vals := by
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain .NOP) st.core.pos :=
    .no_immediate p.inbounds (by simpa [global_simps] using byte) p.pos .nop
  apply p.append_reader st.core .NOP p.current.ctrl.polymorphic_base p.current.vals .instr_case_0
    (.plain encoded) (fun C wf priorTyped => priorTyped.nop wf) ?_ ?_ ?_ ?_
  · simpa using controls
  · simp [vals, base]
  · simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]
  · intro _ C
    exact ⟨encoded, encoded.leaf p.inbounds (by rw [byte]; simp [global_simps]) C⟩

/-- A successful i32 constant read retains its exact source prefix and stack effect. -/
theorem Pending.read_i32_const {data env profile locals index st}
    (p : Pending data env profile locals index st)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST) :
    code.read_i32_const st.core data ⦃ r => ∀ value, r.1 = .Ok value →
      r.2.vals.val = st.core.vals.val ++ [.Val .I32] ∧
      ReaderPost p r.2 (Spec.i32Const value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .I32]) ⦄ := by
  apply WP.spec_mono (code.read_i32_const.spec st.core data capacity)
  rintro ⟨res, out⟩ ⟨controls, effect⟩ value accepted
  dsimp only at controls effect accepted ⊢
  subst res
  obtain ⟨decoded, values⟩ := effect
  refine ⟨values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain (Spec.i32Const value)) out.pos :=
    .of_s32 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  refine p.append_reader out (Spec.i32Const value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [.Val .I32]) (Spec.i32Const_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.i32Const wf value) ?_ ?_ ?_
    (fun _ C => ⟨encoded, encoded.leaf p.inbounds (by rw [byte]; simp [global_simps]) C⟩)
  · simpa [controls] using ctrls
  · simpa [vals, base, List.append_assoc] using values
  · exact encoded.declared _

/-- A successful i64 constant read retains its exact source prefix and stack effect. -/
theorem Pending.read_i64_const {data env profile locals index st}
    (p : Pending data env profile locals index st)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST) :
    code.read_i64_const st.core data ⦃ r => ∀ value, r.1 = .Ok value →
      r.2.vals.val = st.core.vals.val ++ [.Val .I64] ∧
      ReaderPost p r.2 (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .I64]) ⦄ := by
  apply WP.spec_mono (code.read_i64_const.spec st.core data capacity)
  rintro ⟨res, out⟩ ⟨controls, effect⟩ value accepted
  dsimp only at controls effect accepted ⊢
  subst res
  obtain ⟨decoded, values⟩ := effect
  refine ⟨values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain (ScalarConst.i64 value)) out.pos :=
    .of_s64 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  refine p.append_reader out (ScalarConst.i64 value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [.Val .I64]) (ScalarConst.i64_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.i64Const wf value) ?_ ?_ ?_
    (fun _ C => ⟨encoded, encoded.leaf p.inbounds (by rw [byte]; simp [global_simps]) C⟩)
  · simpa [controls] using ctrls
  · simpa [vals, base, List.append_assoc] using values
  · exact encoded.declared _

/-- A successful f32 constant read retains its exact source prefix and stack effect. -/
theorem Pending.read_f32_const {data env profile locals index st}
    (p : Pending data env profile locals index st)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST) :
    code.read_f32_const st.core data ⦃ r => ∀ value, r.1 = .Ok value →
      r.2.vals.val = st.core.vals.val ++ [.Val .F32] ∧
      ReaderPost p r.2 (ScalarConst.f32 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .F32]) ⦄ := by
  apply WP.spec_mono (code.read_f32_const.spec st.core data capacity)
  rintro ⟨res, out⟩ ⟨controls, effect⟩ value accepted
  dsimp only at controls effect accepted ⊢
  subst res
  obtain ⟨decoded, values⟩ := effect
  refine ⟨values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain (ScalarConst.f32 value)) out.pos :=
    .of_f32 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  refine p.append_reader out (ScalarConst.f32 value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [.Val .F32]) (ScalarConst.f32_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.f32Const wf value) ?_ ?_ ?_
    (fun _ C => ⟨encoded, encoded.leaf p.inbounds (by rw [byte]; simp [global_simps]) C⟩)
  · simpa [controls] using ctrls
  · simpa [vals, base, List.append_assoc] using values
  · exact encoded.declared _

/-- A successful f64 constant read retains its exact source prefix and stack effect. -/
theorem Pending.read_f64_const {data env profile locals index st}
    (p : Pending data env profile locals index st)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST) :
    code.read_f64_const st.core data ⦃ r => ∀ value, r.1 = .Ok value →
      r.2.vals.val = st.core.vals.val ++ [.Val .F64] ∧
      ReaderPost p r.2 (ScalarConst.f64 value) p.current.ctrl.polymorphic_base
        (p.current.vals ++ [.Val .F64]) ⦄ := by
  apply WP.spec_mono (code.read_f64_const.spec st.core data capacity)
  rintro ⟨res, out⟩ ⟨controls, effect⟩ value accepted
  dsimp only at controls effect accepted ⊢
  subst res
  obtain ⟨decoded, values⟩ := effect
  refine ⟨values, ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have encoded : Wasm1.At data p.start (.plain (ScalarConst.f64 value)) out.pos :=
    .of_f64 value p.inbounds (by simpa [global_simps] using byte) p.pos decoded
  refine p.append_reader out (ScalarConst.f64 value) p.current.ctrl.polymorphic_base
    (p.current.vals ++ [.Val .F64]) (ScalarConst.f64_wf value) (.plain encoded)
    (fun C wf priorTyped => priorTyped.f64Const wf value) ?_ ?_ ?_
    (fun _ C => ⟨encoded, encoded.leaf p.inbounds (by rw [byte]; simp [global_simps]) C⟩)
  · simpa [controls] using ctrls
  · simpa [vals, base, List.append_assoc] using values
  · exact encoded.declared _

/-- Unreachable trims the operand stack and advances the same source prefix. -/
theorem Pending.read_unreachable {data env profile locals index st}
    (p : Pending data env profile locals index st)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE) :
    code.read_unreachable st.core ⦃ r => r.1 = .Ok () ∧
      r.2.vals.val = st.core.vals.val.take p.current.ctrl.value_stack_base.val ∧
      ReaderPost p r.2 .UNREACHABLE true [] ⦄ := by
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  obtain ⟨marked, markedEq, markedVals, _, markedControls, markedPos⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec st.core (p.parents.map Frames.Saved.ctrl) p.current.ctrl controls
      (by simp [base, vals]))
  simp only [code.read_unreachable, markedEq, bind_ok, WP.spec_ok]
  refine ⟨trivial, markedVals, ?_⟩
  have encoded : Wasm1.At data p.start (.plain .UNREACHABLE) marked.pos :=
    .no_immediate p.inbounds (by simpa [global_simps] using byte)
      (by simpa [markedPos] using p.pos) .unreachable
  refine p.append_reader marked .UNREACHABLE true [] .instr_case_1 (.plain encoded)
    (fun C wf priorTyped => priorTyped.unreachable wf) markedControls ?_ ?_
    (fun _ C => ⟨encoded, encoded.leaf p.inbounds (by rw [byte]; simp [global_simps]) C⟩)
  · simpa using markedVals
  · exact encoded.declared _

end Itasca.Wasm2
