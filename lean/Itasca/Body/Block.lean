import Itasca.Body.Control
import Itasca.Binary.ReadByte

open Aeneas Aeneas.Std

namespace Itasca.Control

/-- The five single-byte block type encodings supported by Wasm 1.0. -/
def blockByte : code.BlockType → U8
  | .Empty => 64#u8
  | .Value .I32 => 127#u8
  | .Value .I64 => 126#u8
  | .Value .F32 => 125#u8
  | .Value .F64 => 124#u8

def labelContext (ts : List valtype) : context :=
  ⟨[], [], [], [], [], [], [], [], [.mk_list ts], none⟩

@[simp]
theorem labelContext_labels (C : context) (ts : List valtype) :
    (labelContext ts ++ C).LABELS = .mk_list ts :: C.LABELS := rfl

theorem labelContext_wf (ts : List valtype) : wf_context (labelContext ts) := by
  constructor <;> simp [Forall]

theorem enter_context_wf (C : context) (hC : wf_context C) (ts : List valtype) :
    wf_context (labelContext ts ++ C) := by
  cases hC
  constructor <;> assumption

theorem block_typed (C : context) (hC : wf_context C) (bt : code.BlockType)
    (body : List instr) (hwf : Forall wf_instr body)
    (hbody : Instrs_ok (labelContext (resultTypes bt) ++ C) body
      (.mk_functype (.mk_list []) (.mk_list (resultTypes bt)))) :
    Instr_ok C (.BLOCK (blockType bt) body)
      (.mk_functype (.mk_list []) (.mk_list (resultTypes bt))) := by
  exact .block C _ body [] _ (blockType_ok C hC bt) hbody hC
    (.instr_case_4 _ body (blockType_wf bt) hwf) (labelContext_wf _)

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

@[step]
theorem code.read_block_type.spec (data : Slice U8) (pos : Usize) (bt : code.BlockType)
    (h : pos.val < data.length) (hbyte : data.val[pos.val] = Control.blockByte bt) :
    code.read_block_type data pos ⦃ r =>
      ∃ next, r = .Ok (bt, next) ∧ next.val = pos.val + 1 ⦄ := by
  obtain ⟨r, hr, next, rfl, hnext⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos h)
  rw [code.read_block_type, hr, hbyte]
  cases bt with
  | Empty => simp [Control.blockByte, core.result.Result.Insts.CoreOpsTry.branch, hnext]
  | Value t => cases t <;> simp [Control.blockByte, core.result.Result.Insts.CoreOpsTry.branch, hnext]

theorem code.read_block_type.eof (data : Slice U8) (pos : Usize) (h : data.length ≤ pos.val) :
    code.read_block_type data pos = .ok (.Err .UnexpectedEof) := by
  simp [code.read_block_type, reader.read_byte.eof data pos h,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem code.read_block_type.invalid (data : Slice U8) (pos : Usize)
    (h : pos.val < data.length)
    (hbyte : ∀ bt, data.val[pos.val] ≠ Control.blockByte bt) :
    code.read_block_type data pos = .ok (.Err .InvalidBlockType) := by
  obtain ⟨r, hr, next, rfl, _⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos h)
  have h0 := hbyte .Empty
  have h1 := hbyte (.Value .I32)
  have h2 := hbyte (.Value .I64)
  have h3 := hbyte (.Value .F32)
  have h4 := hbyte (.Value .F64)
  simp only [Control.blockByte] at h0 h1 h2 h3 h4
  simp [code.read_block_type, hr, core.result.Result.Insts.CoreOpsTry.branch]
  split <;> simp_all [U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]

@[step]
theorem code.read_block.spec (st : code.OpIterState) (data : Slice U8) (bt : code.BlockType)
    (h : st.pos.val < data.length) (hbyte : data.val[st.pos.val] = Control.blockByte bt)
    (hsize : st.ctrls.val.length < Usize.max) :
    code.read_block st data ⦃ r =>
      r.1 = .Ok bt ∧ r.2.pos.val = st.pos.val + 1 ∧ r.2.vals = st.vals ∧
      r.2.ctrls.val = st.ctrls.val ++ [Control.frame st .Block bt] ⦄ := by
  obtain ⟨_, hr, next, rfl, hnext⟩ :=
    WP.spec_imp_exists (code.read_block_type.spec data st.pos bt h hbyte)
  rw [code.read_block, hr]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*
  simp_all [Control.frame]

@[step]
theorem code.read_loop.spec (st : code.OpIterState) (data : Slice U8) (bt : code.BlockType)
    (h : st.pos.val < data.length) (hbyte : data.val[st.pos.val] = Control.blockByte bt)
    (hsize : st.ctrls.val.length < Usize.max) :
    code.read_loop st data ⦃ r =>
      r.1 = .Ok bt ∧ r.2.pos.val = st.pos.val + 1 ∧ r.2.vals = st.vals ∧
      r.2.ctrls.val = st.ctrls.val ++ [Control.frame st .Loop bt] ⦄ := by
  obtain ⟨_, hr, next, rfl, hnext⟩ :=
    WP.spec_imp_exists (code.read_block_type.spec data st.pos bt h hbyte)
  rw [code.read_loop, hr]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*
  simp_all [Control.frame]

/-- Decoding block entry preserves stack bounds and extends the declarative label context. -/
theorem code.read_block.context (st : code.OpIterState) (data : Slice U8) (bt : code.BlockType)
    (C : context) (hC : wf_context C) (hlabels : C.LABELS = Control.labels st.ctrls.val)
    (hshape : Control.Shape st) (h : st.pos.val < data.length)
    (hbyte : data.val[st.pos.val] = Control.blockByte bt)
    (hsize : st.ctrls.val.length < Usize.max) :
    ∃ st', code.read_block st data = .ok (.Ok bt, st') ∧
      st'.pos.val = st.pos.val + 1 ∧ st'.vals = st.vals ∧ Control.Shape st' ∧
      (Control.labelContext (Control.resultTypes bt) ++ C).LABELS = Control.labels st'.ctrls.val ∧
      Blocktype_ok C (Control.blockType bt)
        (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bt))) := by
  obtain ⟨⟨_, st'⟩, hr, rfl, hnext, hvals, hctrls⟩ :=
    WP.spec_imp_exists (code.read_block.spec st data bt h hbyte hsize)
  refine ⟨st', hr, hnext, hvals, Control.Shape.push hshape .Block bt hctrls hvals,
    ?_, Control.blockType_ok C hC bt⟩
  simp [hctrls, Control.labels_push, Control.frame, Control.targetTypes,
    Control.targetBlockType, Control.resultTypes, hlabels]

/-- Even a result-producing Wasm 1.0 loop has an empty branch target type. -/
theorem code.read_loop.context (st : code.OpIterState) (data : Slice U8) (bt : code.BlockType)
    (C : context) (hC : wf_context C) (hlabels : C.LABELS = Control.labels st.ctrls.val)
    (hshape : Control.Shape st) (h : st.pos.val < data.length)
    (hbyte : data.val[st.pos.val] = Control.blockByte bt)
    (hsize : st.ctrls.val.length < Usize.max) :
    ∃ st', code.read_loop st data = .ok (.Ok bt, st') ∧
      st'.pos.val = st.pos.val + 1 ∧ st'.vals = st.vals ∧ Control.Shape st' ∧
      (Control.labelContext [] ++ C).LABELS = Control.labels st'.ctrls.val ∧
      Blocktype_ok C (Control.blockType bt)
        (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bt))) := by
  obtain ⟨⟨_, st'⟩, hr, rfl, hnext, hvals, hctrls⟩ :=
    WP.spec_imp_exists (code.read_loop.spec st data bt h hbyte hsize)
  refine ⟨st', hr, hnext, hvals, Control.Shape.push hshape .Loop bt hctrls hvals,
    ?_, Control.blockType_ok C hC bt⟩
  simp [hctrls, Control.labels_push, Control.frame, Control.targetTypes,
    Control.targetBlockType, Control.results, hlabels]

end Itasca
