import Itasca.Wasm1.Soundness
import Itasca.Wasm1.Profile

open Aeneas Aeneas.Std

namespace Itasca.Examples.Wasm1ProfileBoundary

/-- MVP-shaped bytes whose branch table uses Wasm 2.0's common-bottom rule. -/
def bytes : Slice U8 := alloc.vec.Vec.deref (alloc.vec.Vec.from
  [0x02#u8, 0x7E#u8, 0x00#u8, 0x0E#u8, 0x01#u8, 0x00#u8,
   0x01#u8, 0x0B#u8, 0x1A#u8, 0x00#u8, 0x0B#u8] (by scalar_tac))

def ctx : code.Context :=
  ⟨alloc.vec.Vec.new _, alloc.vec.Vec.from [.I32] (by scalar_tac)⟩

def table : instr := BrTable.instruction [0#u32] 1#u32

def inner : List instr := [.UNREACHABLE, table]

def ops : List instr := [.BLOCK (Control.blockType (.Value .I64)) inner, .DROP, .UNREACHABLE]

private theorem table_wf : wf_instr table := BrTable.instruction_wf _ _

private theorem inner_wf : Forall wf_instr inner := by
  simp only [inner, Forall, List.mem_cons, List.not_mem_nil, or_false]
  rintro op (rfl | rfl)
  · exact .instr_case_1
  · exact table_wf

private theorem bottom_sub (t : valtype) : Resulttype_sub (.mk_list [.BOT]) (.mk_list [t]) := by
  exact .mk_Resulttype_sub _ _ rfl (by simpa [Forall₂] using Valtype_sub.bot t)

/-- The generated Wasm 2.0 rule permits a bottom payload for unlike labels. -/
theorem table_typed (C : context) (hC : wf_context C)
    (hlabels : C.LABELS = [.mk_list [.I64], .mk_list [.I32]]) :
    Instr_ok C table (.mk_functype (.mk_list [.BOT, .I32]) (.mk_list [.I64])) := by
  apply Instr_ok.br_table C [.mk_uN 0] (.mk_uN 1) [] [.BOT] [.I64]
  · simp [Forall, hlabels, proj_uN_0]
  · simpa [Forall, hlabels, proj_uN_0] using bottom_sub .I64
  · simp [hlabels, proj_uN_0]
  · simpa [hlabels, proj_uN_0] using bottom_sub .I32
  · exact hC
  · exact table_wf

/-- Declarative typing alone therefore includes this body. -/
theorem typed (env : module.Env) : Wasm1.FunctionTyped env ctx (.Value .I32) ops := by
  let C := Wasm1.Frames.enter (EnvTranslation.context env ctx) .body (.Value .I32)
  let D := Control.labelContext [.I64] ++ C
  have hC : wf_context C := Control.enter_context_wf _ (EnvTranslation.context_wf env ctx) _
  have hD : wf_context D := Control.enter_context_wf C hC _
  have hlabels : D.LABELS = [.mk_list [.I64], .mk_list [.I32]] := rfl
  have hi : Instrs_ok D inner (.mk_functype (.mk_list []) (.mk_list [.I64])) :=
    Instrs_ok.seq D [.UNREACHABLE] [table] [] [.I64] [.BOT, .I32]
      (.instr D _ _ _ (.unreachable D [] [.BOT, .I32] hD .instr_case_1) hD .instr_case_1)
      (.instr D _ _ _ (table_typed D hD hlabels) hD table_wf) hD
      (by simp [Forall, wf_instr.instr_case_1]) (by simpa [Forall] using table_wf)
  have hb : Instr_ok C (.BLOCK (Control.blockType (.Value .I64)) inner)
      (.mk_functype (.mk_list []) (.mk_list [.I64])) :=
    Control.block_typed C hC (.Value .I64) inner inner_wf hi
  have hbw : wf_instr (.BLOCK (Control.blockType (.Value .I64)) inner) :=
    .instr_case_4 _ _ (Control.blockType_wf _) inner_wf
  have hbd := Instrs_ok.seq C [.BLOCK (Control.blockType (.Value .I64)) inner] [.DROP]
      [] [] [.I64] (.instr C _ _ _ hb hC hbw)
      (.instr C _ _ _ (.drop C .I64 hC .instr_case_2) hC .instr_case_2) hC
      (by simpa [Forall] using hbw) (by simp [Forall, wf_instr.instr_case_2])
  exact Instrs_ok.seq C _ [.UNREACHABLE] [] [.I32] [] hbd
    (.instr C _ _ _ (.unreachable C [] [.I32] hC .instr_case_1) hC .instr_case_1) hC
    (by simpa [Forall] using And.intro hbw wf_instr.instr_case_2)
    (by simp [Forall, wf_instr.instr_case_1])

private theorem single_encoding (b : U8) (h : b.val < 128) : Leb128.Encoding [b] b.val := by
  exact ⟨[], b, rfl, by simp, by simp, h, by simp, by simp [Leb128.payload, Nat.mod_eq_of_lt h]⟩

/-- The counterexample has a complete independent Wasm 1.0 binary spelling. -/
theorem encoded : Wasm1.BodyEncoding bytes ops := by
  have h0 : Wasm1.At bytes 0#usize (.block (.Value .I64)) 2#usize :=
    ⟨[0x02#u8, 0x7E#u8], ⟨0x02#u8, [0x7E#u8], rfl, .block (.Value .I64) trivial⟩,
      ⟨rfl, rfl, by decide⟩⟩
  have h2 : Wasm1.At bytes 2#usize (.plain .UNREACHABLE) 3#usize :=
    ⟨[0x00#u8], ⟨0x00#u8, [], rfl, .unreachable⟩, ⟨rfl, rfl, by decide⟩⟩
  have h3 : Wasm1.At bytes 3#usize (.plain table) 7#usize :=
    ⟨[0x0E#u8, 1#u8, 0#u8, 1#u8], ⟨0x0E#u8, [1#u8, 0#u8, 1#u8], rfl,
      .brTable [0#u32] 1#u32 (single_encoding 1#u8 (by decide))
        (.cons (single_encoding 0#u8 (by decide)) .nil) (single_encoding 1#u8 (by decide))⟩,
      ⟨rfl, rfl, by decide⟩⟩
  have h7 : Wasm1.At bytes 7#usize .end_ 8#usize :=
    ⟨[0x0B#u8], ⟨0x0B#u8, [], rfl, .end_⟩, ⟨rfl, rfl, by decide⟩⟩
  have h8 : Wasm1.At bytes 8#usize (.plain .DROP) 9#usize :=
    ⟨[0x1A#u8], ⟨0x1A#u8, [], rfl, .drop⟩, ⟨rfl, rfl, by decide⟩⟩
  have h9 : Wasm1.At bytes 9#usize (.plain .UNREACHABLE) 10#usize :=
    ⟨[0x00#u8], ⟨0x00#u8, [], rfl, .unreachable⟩, ⟨rfl, rfl, by decide⟩⟩
  have h10 : Wasm1.At bytes 10#usize .end_ 11#usize :=
    ⟨[0x0B#u8], ⟨0x0B#u8, [], rfl, .end_⟩, ⟨rfl, rfl, by decide⟩⟩
  have hi := Wasm1.Emits.simple (Wasm1.Emits.simple .nil (.plain .UNREACHABLE .instr_case_1))
    (.plain table table_wf)
  have ho := Wasm1.Emits.simple (Wasm1.Emits.simple
    (Wasm1.Emits.block (.Value .I64) .nil hi) (.plain .DROP .instr_case_2))
    (.plain .UNREACHABLE .instr_case_1)
  refine ⟨_, 11#usize,
    ((((((Wasm1.Consumed.nil 0#usize (by decide)).snoc h0).snoc h2).snoc h3).snoc h7).snoc h8).snoc h9 |>.snoc h10,
    rfl, ?_⟩
  exact ⟨_, rfl, ho⟩

theorem validated (env : module.Env) : Wasm1.Validated bytes env ctx (.Value .I32) :=
  ⟨ops, encoded, typed env⟩


private theorem public_of_loop (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (result : core.result.Result Unit error.OpError)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hresults : ctx.results.val = Control.results bt)
    (hloop : code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () (Body.initial bt) = .ok (result, ())) :
    code.validate_body data env ctx = .ok result := by
  have hguard : ¬ Slice.len data > limits.MAX_FUNCTION_BYTES := by scalar_tac
  simp [code.validate_body, code.validate_body_with.eq_model, code.validate_body_with_model, hguard,
    code.start_function.spec (alloc.vec.Vec.deref ctx.results) bt
      (by simpa [alloc.vec.Vec.deref] using hresults), hloop]


private theorem loop_step (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (st decoded next : code.OpIterState) (opcode : U8) (hc : st.ctrls.val ≠ [])
    (hr : code.read_op st data = .ok (.Ok opcode, decoded))
    (hs : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor decoded data env ctx opcode () =
      .ok (.Ok (), next, ())) :
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () st =
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () next := by
  have hempty : st.ctrls.val.isEmpty = false := by simpa using hc
  unfold code.validate_body_with_loop
  conv_lhs => rw [loop]
  simp [code.validate_body_with_loop.body, code.control_stack_empty, alloc.vec.Vec.is_empty,
    hempty, hr, hs, core.result.Result.Insts.CoreOpsTry.branch]


private theorem loop_error (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (st decoded next : code.OpIterState) (opcode : U8) (e : error.OpError) (hc : st.ctrls.val ≠ [])
    (hr : code.read_op st data = .ok (.Ok opcode, decoded))
    (hs : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor decoded data env ctx opcode () =
      .ok (.Err e, next, ())) :
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () st = .ok (.Err e, ()) := by
  have hempty : st.ctrls.val.isEmpty = false := by simpa using hc
  unfold code.validate_body_with_loop
  rw [loop]
  simp [code.validate_body_with_loop.body, code.control_stack_empty, alloc.vec.Vec.is_empty,
    hempty, hr, hs, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]


private theorem read_at (data : Slice U8) (st : code.OpIterState) (next : Usize) (opcode : U8)
    (hp : st.pos.val < data.length) (hn : next.val = st.pos.val + 1)
    (hb : data.val[st.pos.val] = opcode) :
    code.read_op st data = .ok (.Ok opcode, {st with pos := next}) := by
  obtain ⟨q, hr, hq⟩ := code.read_op_success st data hp
  have heq : q = next := UScalar.eq_of_val_eq (hq.trans hn.symm)
  simpa [heq, hb] using hr


private theorem leb_at (pos next : Usize) (value : U32)
    (hp : pos.val < bytes.length)
    (hn : next.val = pos.val + 1)
    (hb : (bytes.val[pos.val]).val = value.val)
    (hv : value.val < 128) :
    reader.read_u32_leb bytes pos = .ok (.Ok (value, next)) := by
  obtain ⟨v, p, hr, hv', hp'⟩ := reader.read_u32_leb.single_byte bytes pos hp
    (by simpa [hb] using hv)
  have heq : v = value := UScalar.eq_of_val_eq (hv'.trans hb)
  have hpeq : p = next := UScalar.eq_of_val_eq (hp'.trans hn.symm)
  simpa [heq, hpeq] using hr

private theorem labels_one (st next : code.OpIterState) (target : code.Ctrl) (bt : code.BlockType)
    (hlabel : code.read_label st bytes = .ok (.Ok (0#u32, target), next))
    (htarget : code.branch_target_bt target = .ok bt) :
    code.read_table_labels code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st bytes 1#u32 () =
      .ok (.Ok (some bt), next, ()) := by
  have hmerge : code.merge_target none bt = .ok (.Ok bt) := rfl
  obtain ⟨i, hi, hiv⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := 0#u32) (y := 1#u32) (by scalar_tac))
  have hieq : i = 1#u32 := by scalar_tac
  subst i
  have hdone : code.read_table_labels_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      next bytes 1#u32 () (some bt) 1#u32 =
      .ok (.Ok (some bt), next, ()) := by
    unfold code.read_table_labels_loop
    rw [loop]
    simp [code.read_table_labels_loop.body]
  unfold code.read_table_labels code.read_table_labels_loop
  rw [loop]
  simp only [code.read_table_labels_loop.body, show (0#u32 = 1#u32) = False from by decide,
    ↓reduceIte, hlabel, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  simpa [code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor, code.OpVisitor.on_br_table_label.default,
    code.visit, htarget, hmerge, hi, core.result.Result.Insts.CoreOpsTry.branch,
    code.read_table_labels_loop, code.read_table_labels_loop.body] using hdone


/-- The actual public Wasm 1.0 validator rejects before consuming a table payload. -/
theorem rejected (env : module.Env) :
    code.validate_body bytes env ctx = .ok (.Err .TypeMismatch) := by
  let initial := Body.initial (.Value .I32)
  let first := { initial with pos := 1#usize }
  let body : code.Ctrl := ⟨.Body, .Value .I32, Control.signature (.Value .I32), 0#usize, false⟩
  let frame : code.Ctrl := ⟨.Block, .Value .I64, Control.signature (.Value .I64), 0#usize, false⟩
  let poly : code.Ctrl := { frame with polymorphic_base := true }
  obtain ⟨⟨_, opened⟩, hopen, rfl, hop, hov, hoc⟩ := WP.spec_imp_exists
    (code.read_block.spec first bytes (.Value .I64) (by decide) rfl
      (by simp [first, initial, Body.initial]; scalar_tac) trivial)
  dsimp only at hop hov hoc
  have hz : alloc.vec.Vec.len first.vals = 0#usize := by
    apply UScalar.eq_of_val_eq
    simp [first, initial, Body.initial, alloc.vec.Vec.len]
  have hf : Control.frame first .Block (.Value .I64) = frame := by
    simp only [Control.frame, hz, frame]
  have hoc' : opened.ctrls.val = [body, frame] := by
    rw [hf] at hoc
    simpa [first, initial, Body.initial, body] using hoc
  have hstep0 : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first bytes env
      ctx code.OP_BLOCK () = .ok (.Ok (), opened, ()) := by
    simp [global_simps, hopen,
      code.OpVisitor.on_block.default, code.visit, core.result.Result.Insts.CoreOpsTry.branch]
  let unreachable := { opened with pos := 3#usize }
  obtain ⟨marked, hmark, hmv, hml, hmc, hmp⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec unreachable [body] frame
      (by simp [unreachable, hoc']) (by simp [frame]))
  have hstepUnreachable : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor unreachable bytes env
      ctx code.OP_UNREACHABLE () = .ok (.Ok (), marked, ()) := by
    simp [global_simps, code.read_unreachable, hmark,
      code.OpVisitor.on_unreachable.default, code.visit, core.result.Result.Insts.CoreOpsTry.branch]
  let tableState := { marked with pos := 4#usize }
  let entry := { marked with pos := 5#usize }
  let default := { marked with pos := 6#usize }
  let afterDefault := { marked with pos := 7#usize }
  have hcount : reader.read_u32_leb bytes tableState.pos = .ok (.Ok (1#u32, 5#usize)) :=
    leb_at 4#usize 5#usize 1#u32 (by decide) rfl rfl (by decide)
  have hentryRead : reader.read_u32_leb bytes entry.pos = .ok (.Ok (0#u32, 6#usize)) :=
    leb_at 5#usize 6#usize 0#u32 (by decide) rfl rfl (by decide)
  obtain ⟨_, hentry, rfl⟩ := WP.spec_imp_exists
    (code.read_label.from_leb entry bytes 0#u32 6#usize hentryRead (by simp [entry, hmc]))
  have hentry' : code.read_label entry bytes = .ok (.Ok (0#u32, poly), default) := by
    simpa [entry, default, hmc, poly] using hentry
  have hlabels := labels_one entry default poly (.Value .I64) hentry' rfl
  have hdefaultRead : reader.read_u32_leb bytes default.pos = .ok (.Ok (1#u32, 7#usize)) :=
    leb_at 6#usize 7#usize 1#u32 (by decide) rfl rfl (by decide)
  obtain ⟨_, hdefault, rfl⟩ := WP.spec_imp_exists
    (code.read_label.from_leb default bytes 1#u32 7#usize hdefaultRead (by simp [default, hmc]))
  have hdefault' : code.read_label default bytes = .ok (.Ok (1#u32, body), afterDefault) := by
    simpa [default, afterDefault, hmc] using hdefault
  have hreadTable : code.read_br_table code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      tableState bytes () = .ok (.Err .TypeMismatch, afterDefault, ()) := by
    have hentryEq : { tableState with pos := 5#usize } = entry := rfl
    simp [code.read_br_table, hcount, hentryEq, hlabels, hdefault',
      show code.branch_target_bt body = .ok (.Value .I32) from rfl,
      code.merge_target, code.BlockType.Insts.CoreCmpPartialEqBlockType.eq,
      types.ValueType.Insts.CoreCmpPartialEqValueType.eq,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  have hstepTable : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor tableState bytes env
      ctx code.OP_BR_TABLE () = .ok (.Err .TypeMismatch, afterDefault, ()) := by
    simp [hreadTable, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  apply public_of_loop bytes env ctx (.Value .I32) (.Err .TypeMismatch)
    (by simp [bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step bytes env ctx initial first opened code.OP_BLOCK
    (by simp [initial, Body.initial])
    (read_at bytes initial 1#usize code.OP_BLOCK (by decide) rfl
      (by simp [bytes, initial, Body.initial, alloc.vec.Vec.deref, code.OP_BLOCK])) hstep0]
  rw [loop_step bytes env ctx opened unreachable marked code.OP_UNREACHABLE
    (by simp [hoc'])
    (read_at bytes opened 3#usize code.OP_UNREACHABLE
      (by simp [hop, first, bytes, alloc.vec.Vec.deref]) (by simp [hop, first])
      (by simp [hop, first, bytes, alloc.vec.Vec.deref, code.OP_UNREACHABLE])) hstepUnreachable]
  exact loop_error bytes env ctx marked tableState afterDefault code.OP_BR_TABLE .TypeMismatch
    (by simp [hmc])
    (read_at bytes marked 4#usize code.OP_BR_TABLE
      (by simp [hmp, unreachable, bytes, alloc.vec.Vec.deref]) (by simp [hmp, unreachable])
      (by simp [hmp, unreachable, bytes, alloc.vec.Vec.deref, code.OP_BR_TABLE])) hstepTable

/-- Thus the earlier soundness postcondition has no unrestricted converse. -/
theorem validated_but_rejected (env : module.Env) :
    Wasm1.Validated bytes env ctx (.Value .I32) ∧
      code.validate_body bytes env ctx = .ok (.Err .TypeMismatch) :=
  ⟨validated env, rejected env⟩

/-- The extra Wasm 1.0 branch-table restriction excludes the offending table. -/
theorem table_not_wasm1 (C : context)
    (hlabels : C.LABELS = [.mk_list [.I64], .mk_list [.I32]]) :
    ¬ Wasm1.Instruction C table := by
  intro h
  have hs := Wasm1.Instruction.br_table_iff.mp h
  have heq := hs (.mk_uN 0) (by simp)
  simp [hlabels, proj_uN_0] at heq

/-- The whole decoded instruction tree fails the recursive Wasm 1.0 profile. -/
theorem ops_not_wasm1 (env : module.Env) :
    ¬ Wasm1.Instructions
      (Wasm1.Frames.enter (EnvTranslation.context env ctx) .body (.Value .I32)) ops := by
  intro h
  cases h with
  | cons hb _ =>
    generalize heq : instr.BLOCK (Control.blockType (.Value .I64)) inner = op at hb
    cases hb with
    | leaf _ op hleaf => simp [← heq, Wasm1.Leaf] at hleaf
    | block _ bt body hi =>
      have hbteq : bt = .Value .I64 := by
        have hbt := (instr.BLOCK.inj heq).1
        cases bt with
        | Empty => simp [Control.blockType] at hbt
        | Value t => cases t <;> simp_all [Control.blockType, Translate.valueType]
      subst bt
      have hbody := (instr.BLOCK.inj heq).2
      subst body
      cases hi with
      | cons _ htail =>
        cases htail with
        | cons ht _ => exact table_not_wasm1 _ (by rfl) ht
    | loop _ _ _ _ => cases heq
    | ifElse _ _ _ _ _ _ => cases heq

end Itasca.Examples.Wasm1ProfileBoundary
