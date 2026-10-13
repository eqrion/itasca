import Itasca.Handler.Control
import Itasca.Binary.ReadByte
import Itasca.Binary.Wasm1.BlockType

/-!
# Block and loop handlers

Lemmas about `code.read_block_type`, `code.read_block` and `code.read_loop` for Wasm 1.0 scalar
block types: byte-level specifications, and `code.read_block.context` and `code.read_loop.context`,
which show the label context extends with the generated `Blocktype_ok`. `Control.block_typed` and
`Control.loop_typed` give the generated `block` and `loop` rules.
-/

open Aeneas Aeneas.Std

namespace Itasca.Control

/-- A well-formed block body typed under the extended label context gives a typed `block`. -/
theorem block_typed (C : context) (hC : wf_context C) (bt : code.BlockType)
    (body : List instr) (hwf : Forall wf_instr body)
    (hbody : Instrs_ok (labelContext (resultTypes bt) ++ C) body
      (.mk_functype (.mk_list []) (.mk_list (resultTypes bt)))) :
    Instr_ok C (.BLOCK (blockType bt) body)
      (.mk_functype (.mk_list []) (.mk_list (resultTypes bt))) := by
  exact .block C _ body [] _ (blockType_ok C hC bt) hbody hC
    (.instr_case_4 _ body (blockType_wf bt) hwf) (labelContext_wf _)

/-- A well-formed loop body typed with an empty-label context gives a typed `loop`. -/
theorem loop_typed (C : context) (hC : wf_context C) (bt : code.BlockType)
    (body : List instr) (hwf : Forall wf_instr body)
    (hbody : Instrs_ok (labelContext [] ++ C) body
      (.mk_functype (.mk_list []) (.mk_list (resultTypes bt)))) :
    Instr_ok C (.LOOP (blockType bt) body)
      (.mk_functype (.mk_list []) (.mk_list (resultTypes bt))) := by
  exact .loop C _ body [] _ (blockType_ok C hC bt) hbody hC
    (.instr_case_5 _ body (blockType_wf bt) hwf) (labelContext_wf _)

end Itasca.Control

namespace Itasca

/-- `code.read_block_type` decodes the single byte of a scalar block type. -/
@[step]
theorem code.read_block_type.spec (data : Slice U8) (pos : Usize) (bt : code.BlockType)
    (h : pos.val < data.length) (hbyte : data.val[pos.val] = Control.blockByte bt)
    (hbt : Control.ScalarBlockType bt) :
    code.read_block_type data pos ⦃ r =>
      ∃ next, r = .Ok (bt, next) ∧ next.val = pos.val + 1 ⦄ := by
  obtain ⟨r, hr, next, rfl, hnext⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos h)
  rw [code.read_block_type, hr, hbyte]
  cases bt with
  | Empty => simp [Control.blockByte, core.result.Result.Insts.CoreOpsTry.branch, hnext]
  | Value t => cases t <;> simp_all [Control.ScalarBlockType, Control.blockByte, core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.read_block_type` at the end of the data returns `UnexpectedEof`. -/
theorem code.read_block_type.eof (data : Slice U8) (pos : Usize) (h : data.length ≤ pos.val) :
    code.read_block_type data pos = .ok (.Err .UnexpectedEof) := by
  simp [code.read_block_type, reader.read_byte.eof data pos h,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `code.read_block_type` on a byte that is no scalar block type returns `InvalidBlockType`. -/
theorem code.read_block_type.invalid (data : Slice U8) (pos : Usize)
    (h : pos.val < data.length)
    (hbyte : ∀ bt, Control.ScalarBlockType bt → data.val[pos.val] ≠ Control.blockByte bt) :
    code.read_block_type data pos = .ok (.Err .InvalidBlockType) := by
  obtain ⟨r, hr, next, rfl, _⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos h)
  have h0 := hbyte .Empty trivial
  have h1 := hbyte (.Value .I32) trivial
  have h2 := hbyte (.Value .I64) trivial
  have h3 := hbyte (.Value .F32) trivial
  have h4 := hbyte (.Value .F64) trivial
  simp only [Control.blockByte] at h0 h1 h2 h3 h4
  simp [code.read_block_type, hr, core.result.Result.Insts.CoreOpsTry.branch]
  split <;> simp_all [U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]

/-- `code.read_block` consumes the block type byte and pushes a `Block` frame. -/
@[step]
theorem code.read_block.spec (st : code.OpIterState) (data : Slice U8) (bt : code.BlockType)
    (h : st.pos.val < data.length) (hbyte : data.val[st.pos.val] = Control.blockByte bt)
    (hsize : st.ctrls.val.length < Usize.max) (hbt : Control.ScalarBlockType bt) :
    code.read_block st data ⦃ r =>
      r.1 = .Ok bt ∧ r.2.pos.val = st.pos.val + 1 ∧ r.2.vals = st.vals ∧
      r.2.ctrls.val = st.ctrls.val ++ [Control.frame st .Block bt] ⦄ := by
  obtain ⟨_, hr, next, rfl, hnext⟩ :=
    WP.spec_imp_exists (code.read_block_type.spec data st.pos bt h hbyte hbt)
  rw [code.read_block, hr]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*
  simp_all [Control.frame]

/-- `code.read_loop` consumes the block type byte and pushes a `Loop` frame. -/
@[step]
theorem code.read_loop.spec (st : code.OpIterState) (data : Slice U8) (bt : code.BlockType)
    (h : st.pos.val < data.length) (hbyte : data.val[st.pos.val] = Control.blockByte bt)
    (hsize : st.ctrls.val.length < Usize.max) (hbt : Control.ScalarBlockType bt) :
    code.read_loop st data ⦃ r =>
      r.1 = .Ok bt ∧ r.2.pos.val = st.pos.val + 1 ∧ r.2.vals = st.vals ∧
      r.2.ctrls.val = st.ctrls.val ++ [Control.frame st .Loop bt] ⦄ := by
  obtain ⟨_, hr, next, rfl, hnext⟩ :=
    WP.spec_imp_exists (code.read_block_type.spec data st.pos bt h hbyte hbt)
  rw [code.read_loop, hr]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*
  simp_all [Control.frame]

/-- `code.read_block` preserves `Control.Shape`, extends the label context to match the new control
stack, and gives the block type `Blocktype_ok`. -/
theorem code.read_block.context (st : code.OpIterState) (data : Slice U8) (bt : code.BlockType)
    (C : context) (hC : wf_context C) (hlabels : C.LABELS = Control.labels st.ctrls.val)
    (hshape : Control.Shape st) (h : st.pos.val < data.length)
    (hbyte : data.val[st.pos.val] = Control.blockByte bt)
    (hsize : st.ctrls.val.length < Usize.max) (hbt : Control.ScalarBlockType bt) :
    ∃ st', code.read_block st data = .ok (.Ok bt, st') ∧
      st'.pos.val = st.pos.val + 1 ∧ st'.vals = st.vals ∧ Control.Shape st' ∧
      (Control.labelContext (Control.resultTypes bt) ++ C).LABELS = Control.labels st'.ctrls.val ∧
      Blocktype_ok C (Control.blockType bt)
        (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bt))) := by
  obtain ⟨⟨_, st'⟩, hr, rfl, hnext, hvals, hctrls⟩ :=
    WP.spec_imp_exists (code.read_block.spec st data bt h hbyte hsize hbt)
  refine ⟨st', hr, hnext, hvals, Control.Shape.push hshape .Block bt hctrls hvals,
    ?_, Control.blockType_ok C hC bt⟩
  simp [hctrls, Control.labels_push, Control.frame, Control.targetTypes,
    Control.targetBlockType, Control.resultTypes, hlabels]

/-- `code.read_loop` preserves `Control.Shape`, extends the label context to match the new control
stack, and gives the block type `Blocktype_ok`. Even a loop with a result has an empty branch
target type. -/
theorem code.read_loop.context (st : code.OpIterState) (data : Slice U8) (bt : code.BlockType)
    (C : context) (hC : wf_context C) (hlabels : C.LABELS = Control.labels st.ctrls.val)
    (hshape : Control.Shape st) (h : st.pos.val < data.length)
    (hbyte : data.val[st.pos.val] = Control.blockByte bt)
    (hsize : st.ctrls.val.length < Usize.max) (hbt : Control.ScalarBlockType bt) :
    ∃ st', code.read_loop st data = .ok (.Ok bt, st') ∧
      st'.pos.val = st.pos.val + 1 ∧ st'.vals = st.vals ∧ Control.Shape st' ∧
      (Control.labelContext [] ++ C).LABELS = Control.labels st'.ctrls.val ∧
      Blocktype_ok C (Control.blockType bt)
        (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bt))) := by
  obtain ⟨⟨_, st'⟩, hr, rfl, hnext, hvals, hctrls⟩ :=
    WP.spec_imp_exists (code.read_loop.spec st data bt h hbyte hsize hbt)
  refine ⟨st', hr, hnext, hvals, Control.Shape.push hshape .Loop bt hctrls hvals,
    ?_, Control.blockType_ok C hC bt⟩
  simp [hctrls, Control.labels_push, Control.frame, Control.targetTypes,
    Control.targetBlockType, Control.results, hlabels]

end Itasca
