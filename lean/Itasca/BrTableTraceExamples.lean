import Itasca.VisitorControlTrace
import Itasca.VisitorLeafDispatch

open Aeneas Aeneas.Std

namespace Itasca.BrTableTraceExamples

open VisitorTrace

def emptyContext : code.Context := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _⟩

def bodyState (poly : Bool) (pos : Usize) : code.OpIterState :=
  ⟨alloc.vec.Vec.new _, alloc.vec.Vec.from [⟨.Body, .Empty, 0#usize, poly⟩] (by scalar_tac), pos⟩

private theorem state_eq (a b : code.OpIterState)
    (hv : a.vals.val = b.vals.val) (hc : a.ctrls.val = b.ctrls.val) (hp : a.pos = b.pos) : a = b := by
  have hv := alloc.vec.Vec.ext a.vals b.vals hv
  have hc := alloc.vec.Vec.ext a.ctrls b.ctrls hc
  cases a; cases b; simp_all

private theorem mark_body (poly : Bool) (pos : Usize) :
    code.mark_unreachable (bodyState poly pos) = .ok (bodyState true pos) := by
  obtain ⟨s, hr, hv, _, hc, hp⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec (bodyState poly pos) [] ⟨.Body, .Empty, 0#usize, poly⟩ rfl (by simp))
  have hs : s = bodyState true pos := state_eq _ _ (by simpa [bodyState] using hv)
    (by simpa [bodyState] using hc) hp
  simpa [hs] using hr

private theorem public_of_loop {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : module.Env) (result : BodyResult) (log : V) (v : V)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hloop : code.validate_body_with_loop visitor data env emptyContext.locals emptyContext.results
      v (bodyState false 0#usize) = .ok (result, log)) :
    code.validate_body_with visitor data env emptyContext v = .ok (result, log) := by
  have hguard : ¬ Slice.len data > limits.MAX_FUNCTION_BYTES := by scalar_tac
  have hi : Body.initial .Empty = bodyState false 0#usize := rfl
  simp [code.validate_body_with, hguard,
    code.start_function.spec (alloc.vec.Vec.deref emptyContext.results) .Empty rfl, hi, hloop]

private theorem loop_step {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (v w : V)
    (st decoded next : code.OpIterState) (opcode : U8) (hc : st.ctrls.val ≠ [])
    (hr : code.read_op st data = .ok (.Ok opcode, decoded))
    (hs : code.step visitor decoded data env ctx opcode v = .ok (.Ok (), next, w)) :
    code.validate_body_with_loop visitor data env ctx.locals ctx.results v st =
      code.validate_body_with_loop visitor data env ctx.locals ctx.results w next := by
  have hempty : st.ctrls.val.isEmpty = false := by simpa using hc
  unfold code.validate_body_with_loop
  conv_lhs => rw [loop]
  simp [code.validate_body_with_loop.body, code.control_stack_empty, alloc.vec.Vec.is_empty,
    hempty, hr, hs, core.result.Result.Insts.CoreOpsTry.branch]

private theorem loop_error {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (v w : V)
    (st decoded next : code.OpIterState) (opcode : U8) (error : error.OpError) (hc : st.ctrls.val ≠ [])
    (hr : code.read_op st data = .ok (.Ok opcode, decoded))
    (hs : code.step visitor decoded data env ctx opcode v = .ok (.Err error, next, w)) :
    code.validate_body_with_loop visitor data env ctx.locals ctx.results v st = .ok (.Err error, w) := by
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

private theorem leb_at (data : Slice U8) (pos next : Usize) (value : U32)
    (hp : pos.val < data.length) (hn : next.val = pos.val + 1)
    (hb : (data.val[pos.val]).val = value.val) (hv : value.val < 128) :
    reader.read_u32_leb data pos = .ok (.Ok (value, next)) := by
  obtain ⟨v, p, hr, hv', hp'⟩ := reader.read_u32_leb.single_byte data pos hp (by simpa [hb] using hv)
  have heq : v = value := UScalar.eq_of_val_eq (hv'.trans hb)
  have hpeq : p = next := UScalar.eq_of_val_eq (hp'.trans hn.symm)
  simpa [heq, hpeq] using hr

private theorem label_at (data : Slice U8) (pos next : Usize)
    (hr : reader.read_u32_leb data pos = .ok (.Ok (0#u32, next))) :
    code.read_label (bodyState true pos) data =
      .ok (.Ok (0#u32, ⟨.Body, .Empty, 0#usize, true⟩), bodyState true next) := by
  obtain ⟨_, hs, rfl⟩ := WP.spec_imp_exists
    (code.read_label.from_leb (bodyState true pos) data 0#u32 next hr (by simp [bodyState]))
  simpa [bodyState] using hs

private theorem labels_error {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (st next : code.OpIterState) (v : V) (count i : U32) (expect : Option code.BlockType)
    (error : error.OpError) (hi : i ≠ count)
    (hr : code.read_label st data = .ok (.Err error, next)) :
    code.read_table_labels_loop visitor st data count v expect i = .ok (.Err error, next, v) := by
  unfold code.read_table_labels_loop
  rw [loop]
  simp [code.read_table_labels_loop.body, hi, hr, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

private theorem labels_next {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (st next final : code.OpIterState) (v w z : V) (count i j depth : U32)
    (expect : Option code.BlockType) (target : code.Ctrl) (bt : code.BlockType)
    (result : core.result.Result (Option code.BlockType) error.OpError) (hi : i ≠ count)
    (hr : code.read_label st data = .ok (.Ok (depth, target), next))
    (hh : visitor.on_br_table_label v next depth = .ok (.Ok (), w))
    (ht : code.branch_target_bt target = .ok bt)
    (hm : code.merge_target expect bt = .ok (.Ok bt)) (hj : (i + 1#u32 : Result U32) = .ok j)
    (hrest : code.read_table_labels_loop visitor next data count w (some bt) j = .ok (result, final, z)) :
    code.read_table_labels_loop visitor st data count v expect i = .ok (result, final, z) := by
  unfold code.read_table_labels_loop
  rw [loop]
  simpa [code.read_table_labels_loop.body, hi, hr, hh, ht, hm, hj, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch, code.read_table_labels_loop] using hrest

private theorem add_zero : (0#u32 + 1#u32 : Result U32) = .ok 1#u32 := by
  obtain ⟨i, hi, hv⟩ := WP.spec_imp_exists (UScalar.add_spec (x := 0#u32) (y := 1#u32) (by scalar_tac))
  have he : i = 1#u32 := by scalar_tac
  simpa [he] using hi

def firstLog : List Observation := [⟨.op (bodyState true 1#usize) .unreachable, .Ok ()⟩]
def partialLog : List Observation := firstLog ++ [⟨.op (bodyState true 4#usize) (.br_table_label 0#u32), .Ok ()⟩]

private theorem partial_body (data : Slice U8) (env : module.Env) (e : error.OpError)
    (last : code.OpIterState) (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (h0 : 0 < data.length) (h1 : 1 < data.length)
    (hb0 : data.val[0]'h0 = 0#u8) (hb1 : data.val[1]'h1 = 0x0E#u8)
    (hc : reader.read_u32_leb data 2#usize = .ok (.Ok (2#u32, 3#usize)))
    (hl : reader.read_u32_leb data 3#usize = .ok (.Ok (0#u32, 4#usize)))
    (hbad : code.read_label (bodyState true 4#usize) data = .ok (.Err e, last)) :
    code.validate_body_with recorder data env emptyContext [] = .ok (.Err e, partialLog) := by
  have hlabel := label_at data 3#usize 4#usize hl
  have htail := labels_error recorder data (bodyState true 4#usize) last partialLog
    2#u32 1#u32 (some .Empty) e (by decide) hbad
  have hlabels := labels_next recorder data (bodyState true 3#usize) (bodyState true 4#usize) last
    firstLog partialLog partialLog 2#u32 0#u32 1#u32 0#u32 none ⟨.Body, .Empty, 0#usize, true⟩
    .Empty (.Err e) (by decide) hlabel (by rfl) rfl rfl add_zero htail
  have ht : code.read_br_table recorder (bodyState true 2#usize) data firstLog =
      .ok (.Err e, last, partialLog) := by
    simp [code.read_br_table, show (bodyState true 2#usize).pos = 2#usize from rfl,
      hc, show {bodyState true 2#usize with pos := 3#usize} = bodyState true 3#usize from rfl,
      code.read_table_labels, hlabels, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  have hs0 : code.step recorder (bodyState false 1#usize) data env emptyContext code.OP_UNREACHABLE [] =
      .ok (.Ok (), bodyState true 1#usize, firstLog) := by
    rw [dispatch_unreachable]
    simp [CoreVisitor.run, code.read_unreachable, mark_body, invoke, recorder, ofHandler,
      code.visit, firstLog, core.result.Result.Insts.CoreOpsTry.branch]
  have hs1 : code.step recorder (bodyState true 2#usize) data env emptyContext code.OP_BR_TABLE firstLog =
      .ok (.Err e, last, partialLog) := by
    simp [code.step_br_table.dispatch, ht, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  apply public_of_loop recorder data env (.Err e) partialLog [] hsize
  rw [loop_step recorder data env emptyContext [] firstLog (bodyState false 0#usize)
    (bodyState false 1#usize) (bodyState true 1#usize) code.OP_UNREACHABLE (by simp [bodyState])
    (read_at data _ 1#usize code.OP_UNREACHABLE h0 rfl (by simpa [global_simps, bodyState] using hb0)) hs0]
  exact loop_error recorder data env emptyContext firstLog partialLog (bodyState true 1#usize)
    (bodyState true 2#usize) last code.OP_BR_TABLE e (by simp [bodyState])
    (read_at data _ 2#usize code.OP_BR_TABLE h1 rfl (by simpa [global_simps, bodyState] using hb1)) hs1

def unknownBytes : Slice U8 := alloc.vec.Vec.deref
  (alloc.vec.Vec.from [0#u8, 0x0E#u8, 2#u8, 0#u8, 1#u8, 0#u8, 0x0B#u8] (by scalar_tac))

/-- The second depth is out of range. It consumes its immediate but creates
no callback, leaving the preceding accepted label visible in the public log. -/
theorem unknown_later_label (env : module.Env) :
    code.validate_body_with recorder unknownBytes env emptyContext [] =
      .ok (.Err .UnknownLabel, partialLog) := by
  have hr := leb_at unknownBytes 4#usize 5#usize 1#u32 (by decide) rfl rfl (by decide)
  obtain ⟨_, hb, rfl⟩ := WP.spec_imp_exists
    (code.read_label.unknown_from_leb (bodyState true 4#usize) unknownBytes 1#u32 5#usize hr
      (by simp [bodyState]))
  apply partial_body unknownBytes env .UnknownLabel (bodyState true 5#usize)
    (by simp [unknownBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) (by decide) (by decide) rfl rfl
    (leb_at unknownBytes 2#usize 3#usize 2#u32 (by decide) rfl rfl (by decide))
    (leb_at unknownBytes 3#usize 4#usize 0#u32 (by decide) rfl rfl (by decide))
  exact hb

def malformedBytes : Slice U8 := alloc.vec.Vec.deref
  (alloc.vec.Vec.from [0#u8, 0x0E#u8, 2#u8, 0#u8, 0x80#u8] (by scalar_tac))

/-- An unterminated later depth preserves the earlier callback prefix and
makes no callback for the malformed immediate. -/
theorem malformed_later_label (env : module.Env) :
    code.validate_body_with recorder malformedBytes env emptyContext [] =
      .ok (.Err .UnexpectedEof, partialLog) := by
  have hr := reader.read_u32_leb.reject_complete malformedBytes 4#usize .UnexpectedEof
    (.eof [0x80#u8] rfl (by decide) (by simp))
  have hb : code.read_label (bodyState true 4#usize) malformedBytes =
      .ok (.Err .UnexpectedEof, bodyState true 4#usize) := by
    simp [code.read_label, show (bodyState true 4#usize).pos = 4#usize from rfl, hr,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  exact partial_body malformedBytes env .UnexpectedEof (bodyState true 4#usize)
    (by simp [malformedBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) (by decide) (by decide) rfl rfl
    (leb_at malformedBytes 2#usize 3#usize 2#u32 (by decide) rfl rfl (by decide))
    (leb_at malformedBytes 3#usize 4#usize 0#u32 (by decide) rfl rfl (by decide)) hb

def tableBytes : Slice U8 := alloc.vec.Vec.deref
  (alloc.vec.Vec.from [0#u8, 0x0E#u8, 1#u8, 0#u8, 0#u8, 0x0B#u8] (by scalar_tac))

def rejectedLabelLog : List Observation := firstLog ++
  [⟨.op (bodyState true 4#usize) (.br_table_label 0#u32), .Err .OutOfMemory⟩]
def tableLog : List Observation := partialLog ++
  [⟨.op (bodyState true 5#usize) (.br_table 0#u32 .Empty), .Ok ()⟩]
def rejectedTableLog : List Observation := partialLog ++
  [⟨.op (bodyState true 5#usize) (.br_table 0#u32 .Empty), .Err .OutOfMemory⟩]

private theorem table_error_body (visitor : code.OpVisitor (List Observation))
    (env : module.Env) (e : error.OpError) (last : code.OpIterState) (log : List Observation)
    (hfirst : visitor.on_unreachable [] (bodyState true 1#usize) = .ok (.Ok (), firstLog))
    (hstep : code.step visitor (bodyState true 2#usize) tableBytes env emptyContext code.OP_BR_TABLE firstLog =
      .ok (.Err e, last, log)) :
    code.validate_body_with visitor tableBytes env emptyContext [] = .ok (.Err e, log) := by
  have hs0 : code.step visitor (bodyState false 1#usize) tableBytes env emptyContext code.OP_UNREACHABLE [] =
      .ok (.Ok (), bodyState true 1#usize, firstLog) := by
    rw [dispatch_unreachable]
    simp [CoreVisitor.run, code.read_unreachable, mark_body, invoke, hfirst,
      code.visit, core.result.Result.Insts.CoreOpsTry.branch]
  apply public_of_loop visitor tableBytes env (.Err e) log []
    (by simp [tableBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
  rw [loop_step visitor tableBytes env emptyContext [] firstLog (bodyState false 0#usize)
    (bodyState false 1#usize) (bodyState true 1#usize) code.OP_UNREACHABLE (by simp [bodyState])
    (read_at tableBytes _ 1#usize code.OP_UNREACHABLE (by decide) rfl (by simp [tableBytes, bodyState, alloc.vec.Vec.deref, global_simps])) hs0]
  exact loop_error visitor tableBytes env emptyContext firstLog log (bodyState true 1#usize)
    (bodyState true 2#usize) last code.OP_BR_TABLE e (by simp [bodyState])
    (read_at tableBytes _ 2#usize code.OP_BR_TABLE (by decide) rfl (by simp [tableBytes, bodyState, alloc.vec.Vec.deref, global_simps])) hstep

/-- A rejecting vector callback is included, and preempts reading the default
or emitting the closing table callback. -/
theorem rejected_label (env : module.Env) :
    code.validate_body_with (rejectAt 1 .OutOfMemory) tableBytes env emptyContext [] =
      .ok (.Err (.Visitor .OutOfMemory), rejectedLabelLog) := by
  let visitor := rejectAt 1 .OutOfMemory
  have hread := label_at tableBytes 3#usize 4#usize
    (leb_at tableBytes 3#usize 4#usize 0#u32 (by decide) rfl rfl (by decide))
  have hlabels : code.read_table_labels visitor (bodyState true 3#usize) tableBytes 1#u32 firstLog =
      .ok (.Err (.Visitor .OutOfMemory), bodyState true 4#usize, rejectedLabelLog) := by
    unfold code.read_table_labels code.read_table_labels_loop
    rw [loop]
    simp [code.read_table_labels_loop.body, hread, visitor, rejectAt, ofHandler, firstLog,
      code.visit, rejectedLabelLog, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  have hc := leb_at tableBytes 2#usize 3#usize 1#u32 (by decide) rfl rfl (by decide)
  have ht : code.read_br_table visitor (bodyState true 2#usize) tableBytes firstLog =
      .ok (.Err (.Visitor .OutOfMemory), bodyState true 4#usize, rejectedLabelLog) := by
    simp [code.read_br_table, show (bodyState true 2#usize).pos = 2#usize from rfl, hc,
      show {bodyState true 2#usize with pos := 3#usize} = bodyState true 3#usize from rfl,
      hlabels, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  apply table_error_body visitor env (.Visitor .OutOfMemory) (bodyState true 4#usize) rejectedLabelLog rfl
  simp [code.step_br_table.dispatch, ht, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

private theorem read_one_table {V : Type} (visitor : code.OpVisitor V) (v w : V)
    (hh : visitor.on_br_table_label v (bodyState true 4#usize) 0#u32 = .ok (.Ok (), w)) :
    code.read_br_table visitor (bodyState true 2#usize) tableBytes v =
      .ok (.Ok (0#u32, .Empty), bodyState true 5#usize, w) := by
  have hread := label_at tableBytes 3#usize 4#usize
    (leb_at tableBytes 3#usize 4#usize 0#u32 (by decide) rfl rfl (by decide))
  have hdone : code.read_table_labels_loop visitor (bodyState true 4#usize) tableBytes 1#u32 w
      (some .Empty) 1#u32 = .ok (.Ok (some .Empty), bodyState true 4#usize, w) := by
    unfold code.read_table_labels_loop
    rw [loop]
    simp [code.read_table_labels_loop.body]
  have hlabels := labels_next visitor tableBytes (bodyState true 3#usize) (bodyState true 4#usize)
    (bodyState true 4#usize) v w w 1#u32 0#u32 1#u32 0#u32 none ⟨.Body, .Empty, 0#usize, true⟩
    .Empty (.Ok (some .Empty)) (by decide) hread hh rfl rfl add_zero hdone
  have hc := leb_at tableBytes 2#usize 3#usize 1#u32 (by decide) rfl rfl (by decide)
  have hd := label_at tableBytes 4#usize 5#usize
    (leb_at tableBytes 4#usize 5#usize 0#u32 (by decide) rfl rfl (by decide))
  have hpop := code.pop_with_type.polymorphic (bodyState true 5#usize) .I32
    (by apply UScalar.eq_of_val_eq; simp [bodyState, alloc.vec.Vec.len, Control.base])
    (by simp [bodyState, Control.polymorphic])
  have hargs := code.pop_types.empty (bodyState true 5#usize)
    (alloc.vec.Vec.deref (alloc.vec.Vec.new types.ValueType)) rfl
  simp [code.read_br_table, show (bodyState true 2#usize).pos = 2#usize from rfl, hc,
    show {bodyState true 2#usize with pos := 3#usize} = bodyState true 3#usize from rfl,
    code.read_table_labels, hlabels, hd, code.branch_target_bt, code.merge_target,
    code.BlockType.Insts.CoreCmpPartialEqBlockType.eq, hpop, code.block_results, hargs,
    mark_body, core.result.Result.Insts.CoreOpsTry.branch]

/-- The closing callback is observed after the unobserved default and after
unreachability is established, even when that callback rejects. -/
theorem rejected_closing_callback (env : module.Env) :
    code.validate_body_with (rejectAt 2 .OutOfMemory) tableBytes env emptyContext [] =
      .ok (.Err (.Visitor .OutOfMemory), rejectedTableLog) := by
  let visitor := rejectAt 2 .OutOfMemory
  have ht := read_one_table visitor firstLog partialLog rfl
  apply table_error_body visitor env (.Visitor .OutOfMemory) (bodyState true 5#usize) rejectedTableLog rfl
  rw [code.step_br_table.dispatch, ht]
  simp [CoreVisitor.run, visitor, rejectAt, ofHandler,
    code.visit, firstLog, partialLog, rejectedTableLog, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

def closedState : code.OpIterState := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _, 6#usize⟩
def acceptedLog : List Observation := tableLog ++ [⟨.op closedState (.end_ .Body .Empty), .Ok ()⟩]

/-- A successful table has one vector hook, one closing hook, and no hook for
its default. The final end snapshot has an empty control stack. -/
theorem default_has_no_callback (env : module.Env) :
    code.validate_body_with recorder tableBytes env emptyContext [] = .ok (.Ok (), acceptedLog) := by
  have ht := read_one_table recorder firstLog partialLog rfl
  have hs0 : code.step recorder (bodyState false 1#usize) tableBytes env emptyContext code.OP_UNREACHABLE [] =
      .ok (.Ok (), bodyState true 1#usize, firstLog) := by
    rw [dispatch_unreachable]
    simp [CoreVisitor.run, code.read_unreachable, mark_body, invoke, recorder, ofHandler,
      code.visit, firstLog, core.result.Result.Insts.CoreOpsTry.branch]
  have hstable : code.step recorder (bodyState true 2#usize) tableBytes env emptyContext code.OP_BR_TABLE firstLog =
      .ok (.Ok (), bodyState true 5#usize, tableLog) := by
    rw [code.step_br_table.dispatch, ht]
    simp [CoreVisitor.run, recorder, ofHandler, code.visit,
      tableLog, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨⟨_, ended⟩, he, hok, hc, hv, hp⟩ := WP.spec_imp_exists
    (code.read_end.empty (bodyState true 6#usize) [] ⟨.Body, .Empty, 0#usize, true⟩ rfl rfl rfl)
  dsimp only at hok hc hv hp
  have heq : ended = closedState := state_eq _ _ (by simpa [closedState, bodyState] using congrArg alloc.vec.Vec.val hv)
    (by simpa [closedState] using hc) hp
  have hend : code.read_end (bodyState true 6#usize) = .ok (.Ok (.Body, .Empty), closedState) := by
    simpa [hok, heq] using he
  have hsEnd : code.step recorder (bodyState true 6#usize) tableBytes env emptyContext code.OP_END tableLog =
      .ok (.Ok (), closedState, acceptedLog) := by
    rw [dispatch_end]
    simp [CoreVisitor.run, hend, invoke, recorder, ofHandler, code.visit,
      acceptedLog, core.result.Result.Insts.CoreOpsTry.branch]
  apply public_of_loop recorder tableBytes env (.Ok ()) acceptedLog []
    (by simp [tableBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
  rw [loop_step recorder tableBytes env emptyContext [] firstLog (bodyState false 0#usize)
    (bodyState false 1#usize) (bodyState true 1#usize) code.OP_UNREACHABLE (by simp [bodyState])
    (read_at tableBytes _ 1#usize code.OP_UNREACHABLE (by decide) rfl (by simp [tableBytes, bodyState, alloc.vec.Vec.deref, global_simps])) hs0]
  rw [loop_step recorder tableBytes env emptyContext firstLog tableLog (bodyState true 1#usize)
    (bodyState true 2#usize) (bodyState true 5#usize) code.OP_BR_TABLE (by simp [bodyState])
    (read_at tableBytes _ 2#usize code.OP_BR_TABLE (by decide) rfl (by simp [tableBytes, bodyState, alloc.vec.Vec.deref, global_simps])) hstable]
  rw [loop_step recorder tableBytes env emptyContext tableLog acceptedLog (bodyState true 5#usize)
    (bodyState true 6#usize) closedState code.OP_END (by simp [bodyState])
    (read_at tableBytes _ 6#usize code.OP_END (by decide) rfl (by simp [tableBytes, bodyState, alloc.vec.Vec.deref, global_simps])) hsEnd]
  unfold code.validate_body_with_loop
  rw [loop]
  simp [code.validate_body_with_loop.body, code.control_stack_empty, alloc.vec.Vec.is_empty,
    closedState, show Slice.len tableBytes = 6#usize from rfl]

def nestedFrame (kind : code.LabelKind) (poly : Bool) : code.Ctrl :=
  ⟨kind, .Value .I64, 0#usize, poly⟩
def nestedState (kind : code.LabelKind) (poly : Bool) (pos : Usize) : code.OpIterState :=
  ⟨alloc.vec.Vec.new _, alloc.vec.Vec.from [⟨.Body, .Empty, 0#usize, false⟩, nestedFrame kind poly]
    (by scalar_tac), pos⟩

private theorem mark_nested (kind : code.LabelKind) (poly : Bool) (pos : Usize) :
    code.mark_unreachable (nestedState kind poly pos) = .ok (nestedState kind true pos) := by
  obtain ⟨s, hr, hv, _, hc, hp⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec (nestedState kind poly pos) [⟨.Body, .Empty, 0#usize, false⟩]
      (nestedFrame kind poly) rfl (by simp [nestedFrame]))
  have hs : s = nestedState kind true pos := state_eq _ _ (by simpa [nestedState, nestedFrame] using hv)
    (by simpa [nestedState, nestedFrame] using hc) hp
  simpa [hs] using hr

def mismatchBytes : Slice U8 := alloc.vec.Vec.deref
  (alloc.vec.Vec.from [0x02#u8, 0x7E#u8, 0#u8, 0x0E#u8, 2#u8, 0#u8, 1#u8, 0#u8] (by scalar_tac))
def nestedLog (kind : code.LabelKind) (action : Action) : List Observation :=
  [⟨.op (nestedState kind false 2#usize) action, .Ok ()⟩,
   ⟨.op (nestedState kind true 3#usize) .unreachable, .Ok ()⟩]
def mismatchLog : List Observation := nestedLog .Block (.block (.Value .I64)) ++
  [⟨.op (nestedState .Block true 6#usize) (.br_table_label 0#u32), .Ok ()⟩,
   ⟨.op (nestedState .Block true 7#usize) (.br_table_label 1#u32), .Ok ()⟩]

/-- Both valid-depth callbacks are observed before their unequal target
signatures cause rejection. The unconsumed default produces no event. -/
theorem mismatching_observed_label (env : module.Env) :
    code.validate_body_with recorder mismatchBytes env emptyContext [] =
      .ok (.Err .TypeMismatch, mismatchLog) := by
  have hfirst := leb_at mismatchBytes 5#usize 6#usize 0#u32 (by decide) rfl rfl (by decide)
  obtain ⟨_, hlabel0, rfl⟩ := WP.spec_imp_exists
    (code.read_label.from_leb (nestedState .Block true 5#usize) mismatchBytes 0#u32 6#usize hfirst
      (by simp [nestedState]))
  have hlabel0' : code.read_label (nestedState .Block true 5#usize) mismatchBytes =
      .ok (.Ok (0#u32, nestedFrame .Block true), nestedState .Block true 6#usize) := by
    simpa [nestedState] using hlabel0
  have hsecond := leb_at mismatchBytes 6#usize 7#usize 1#u32 (by decide) rfl rfl (by decide)
  obtain ⟨_, hlabel1, rfl⟩ := WP.spec_imp_exists
    (code.read_label.from_leb (nestedState .Block true 6#usize) mismatchBytes 1#u32 7#usize hsecond
      (by simp [nestedState]))
  have hlabel1' : code.read_label (nestedState .Block true 6#usize) mismatchBytes =
      .ok (.Ok (1#u32, ⟨.Body, .Empty, 0#usize, false⟩), nestedState .Block true 7#usize) := by
    simpa [nestedState] using hlabel1
  let before := nestedLog .Block (.block (.Value .I64))
  let afterFirst := before ++ [⟨.op (nestedState .Block true 6#usize) (.br_table_label 0#u32), .Ok ()⟩]
  have htail : code.read_table_labels_loop recorder (nestedState .Block true 6#usize) mismatchBytes
      2#u32 afterFirst (some (.Value .I64)) 1#u32 =
      .ok (.Err .TypeMismatch, nestedState .Block true 7#usize, mismatchLog) := by
    unfold code.read_table_labels_loop
    rw [loop]
    simp [code.read_table_labels_loop.body, hlabel1', recorder, ofHandler, code.visit,
      code.branch_target_bt, code.merge_target, code.BlockType.Insts.CoreCmpPartialEqBlockType.eq,
      before, afterFirst, mismatchLog, List.append_assoc, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  have hlabels := labels_next recorder mismatchBytes (nestedState .Block true 5#usize)
    (nestedState .Block true 6#usize) (nestedState .Block true 7#usize) before afterFirst mismatchLog
    2#u32 0#u32 1#u32 0#u32 none (nestedFrame .Block true) (.Value .I64) (.Err .TypeMismatch)
    (by decide) hlabel0' rfl rfl rfl add_zero htail
  have hc := leb_at mismatchBytes 4#usize 5#usize 2#u32 (by decide) rfl rfl (by decide)
  have ht : code.read_br_table recorder (nestedState .Block true 4#usize) mismatchBytes before =
      .ok (.Err .TypeMismatch, nestedState .Block true 7#usize, mismatchLog) := by
    simp [code.read_br_table, show (nestedState .Block true 4#usize).pos = 4#usize from rfl, hc,
      show {nestedState .Block true 4#usize with pos := 5#usize} = nestedState .Block true 5#usize from rfl,
      code.read_table_labels, hlabels, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  have hsTable : code.step recorder (nestedState .Block true 4#usize) mismatchBytes env emptyContext
      code.OP_BR_TABLE before = .ok (.Err .TypeMismatch, nestedState .Block true 7#usize, mismatchLog) := by
    rw [code.step_br_table.dispatch, ht]
    simp [CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  obtain ⟨⟨res, opened⟩, hopen, hok, hp, hv, hc⟩ := WP.spec_imp_exists
    (code.read_block.spec (bodyState false 1#usize) mismatchBytes (.Value .I64) (by decide) rfl
      (by simp [bodyState]; scalar_tac))
  dsimp only at hok hp hv hc
  have hz : alloc.vec.Vec.len (bodyState false 1#usize).vals = 0#usize := by
    apply UScalar.eq_of_val_eq
    simp [bodyState, alloc.vec.Vec.len]
  unfold Control.frame at hc
  rw [hz] at hc
  have hopenEq : opened = nestedState .Block false 2#usize := state_eq _ _
    (by simpa [nestedState, bodyState] using congrArg alloc.vec.Vec.val hv)
    (by simpa [nestedState, bodyState, nestedFrame] using hc)
    (by apply UScalar.eq_of_val_eq; simpa [bodyState, nestedState] using hp)
  have hopen' : code.read_block (bodyState false 1#usize) mismatchBytes =
      .ok (.Ok (.Value .I64), nestedState .Block false 2#usize) := by simpa [hopenEq, hok] using hopen
  let openLog : List Observation := [⟨.op (nestedState .Block false 2#usize) (.block (.Value .I64)), .Ok ()⟩]
  have hsOpen : code.step recorder (bodyState false 1#usize) mismatchBytes env emptyContext code.OP_BLOCK [] =
      .ok (.Ok (), nestedState .Block false 2#usize, openLog) := by
    rw [dispatch_block]
    simp [CoreVisitor.run, hopen', invoke, recorder, ofHandler, openLog, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch]
  have hsUnreachable : code.step recorder (nestedState .Block false 3#usize) mismatchBytes env emptyContext
      code.OP_UNREACHABLE openLog = .ok (.Ok (), nestedState .Block true 3#usize, before) := by
    rw [dispatch_unreachable]
    simp [CoreVisitor.run, code.read_unreachable, mark_nested, invoke, recorder, ofHandler,
      openLog, before, nestedLog, code.visit, core.result.Result.Insts.CoreOpsTry.branch]
  apply public_of_loop recorder mismatchBytes env (.Err .TypeMismatch) mismatchLog []
    (by simp [mismatchBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
  rw [loop_step recorder mismatchBytes env emptyContext [] openLog (bodyState false 0#usize)
    (bodyState false 1#usize) (nestedState .Block false 2#usize) code.OP_BLOCK (by simp [bodyState])
    (read_at mismatchBytes _ 1#usize code.OP_BLOCK (by decide) rfl
      (by simp [mismatchBytes, alloc.vec.Vec.deref, bodyState, global_simps])) hsOpen]
  rw [loop_step recorder mismatchBytes env emptyContext openLog before (nestedState .Block false 2#usize)
    (nestedState .Block false 3#usize) (nestedState .Block true 3#usize) code.OP_UNREACHABLE
    (by simp [nestedState]) (read_at mismatchBytes _ 3#usize code.OP_UNREACHABLE (by decide) rfl
      (by simp [mismatchBytes, alloc.vec.Vec.deref, nestedState, global_simps])) hsUnreachable]
  exact loop_error recorder mismatchBytes env emptyContext before mismatchLog (nestedState .Block true 3#usize)
    (nestedState .Block true 4#usize) (nestedState .Block true 7#usize) code.OP_BR_TABLE .TypeMismatch
    (by simp [nestedState]) (read_at mismatchBytes _ 4#usize code.OP_BR_TABLE (by decide) rfl
      (by simp [mismatchBytes, alloc.vec.Vec.deref, nestedState, global_simps])) hsTable

def loopBytes : Slice U8 := alloc.vec.Vec.deref
  (alloc.vec.Vec.from [0x03#u8, 0x7E#u8, 0#u8, 0x0C#u8, 0#u8] (by scalar_tac))
def loopLog : List Observation := nestedLog .Loop (.loop (.Value .I64)) ++
  [⟨.op (nestedState .Loop true 5#usize) (.br 0#u32 (.Value .I64)), .Ok ()⟩]

/-- A result-bearing loop's ordinary branch callback reports its raw declared
block type although its branch target signature is empty. The eventual missing
end rejects the public body after this exact three-callback prefix. -/
theorem loop_branch_raw_block_type (env : module.Env) :
    code.validate_body_with recorder loopBytes env emptyContext [] = .ok (.Err .UnexpectedEof, loopLog) ∧
      Control.targetBlockType (nestedFrame .Loop true) = .Empty := by
  refine ⟨?_, rfl⟩
  obtain ⟨branched, hbr, hv, hc, hp, _⟩ := code.read_br.loop_backedge
    (nestedState .Loop true 4#usize) loopBytes [⟨.Body, .Empty, 0#usize, false⟩]
    (nestedFrame .Loop true) rfl rfl (by simp [nestedFrame]) (by decide) rfl
  have hbrEq : branched = nestedState .Loop true 5#usize := state_eq _ _
    (by simpa [nestedState, nestedFrame] using hv)
    (by simpa [nestedState, nestedFrame] using hc)
    (by apply UScalar.eq_of_val_eq; simpa [nestedState] using hp)
  have hbr' : code.read_br (nestedState .Loop true 4#usize) loopBytes =
      .ok (.Ok (0#u32, .Value .I64), nestedState .Loop true 5#usize) := by
    simpa [hbrEq, nestedFrame] using hbr
  let before := nestedLog .Loop (.loop (.Value .I64))
  have hsBr : code.step recorder (nestedState .Loop true 4#usize) loopBytes env emptyContext code.OP_BR before =
      .ok (.Ok (), nestedState .Loop true 5#usize, loopLog) := by
    rw [dispatch_br]
    simp [CoreVisitor.run, hbr', invoke, recorder, ofHandler, before, loopLog,
      code.visit, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨⟨res, opened⟩, hopen, hok, hp, hv, hc⟩ := WP.spec_imp_exists
    (code.read_loop.spec (bodyState false 1#usize) loopBytes (.Value .I64) (by decide) rfl
      (by simp [bodyState]; scalar_tac))
  dsimp only at hok hp hv hc
  have hz : alloc.vec.Vec.len (bodyState false 1#usize).vals = 0#usize := by
    apply UScalar.eq_of_val_eq
    simp [bodyState, alloc.vec.Vec.len]
  unfold Control.frame at hc
  rw [hz] at hc
  have hopenEq : opened = nestedState .Loop false 2#usize := state_eq _ _
    (by simpa [nestedState, bodyState] using congrArg alloc.vec.Vec.val hv)
    (by simpa [nestedState, bodyState, nestedFrame] using hc)
    (by apply UScalar.eq_of_val_eq; simpa [bodyState, nestedState] using hp)
  have hopen' : code.read_loop (bodyState false 1#usize) loopBytes =
      .ok (.Ok (.Value .I64), nestedState .Loop false 2#usize) := by simpa [hopenEq, hok] using hopen
  let openLog : List Observation := [⟨.op (nestedState .Loop false 2#usize) (.loop (.Value .I64)), .Ok ()⟩]
  have hsOpen : code.step recorder (bodyState false 1#usize) loopBytes env emptyContext code.OP_LOOP [] =
      .ok (.Ok (), nestedState .Loop false 2#usize, openLog) := by
    rw [dispatch_loop]
    simp [CoreVisitor.run, hopen', invoke, recorder, ofHandler, openLog, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch]
  have hsUnreachable : code.step recorder (nestedState .Loop false 3#usize) loopBytes env emptyContext
      code.OP_UNREACHABLE openLog = .ok (.Ok (), nestedState .Loop true 3#usize, before) := by
    rw [dispatch_unreachable]
    simp [CoreVisitor.run, code.read_unreachable, mark_nested, invoke, recorder, ofHandler,
      openLog, before, nestedLog, code.visit, core.result.Result.Insts.CoreOpsTry.branch]
  apply public_of_loop recorder loopBytes env (.Err .UnexpectedEof) loopLog []
    (by simp [loopBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES])
  rw [loop_step recorder loopBytes env emptyContext [] openLog (bodyState false 0#usize)
    (bodyState false 1#usize) (nestedState .Loop false 2#usize) code.OP_LOOP (by simp [bodyState])
    (read_at loopBytes _ 1#usize code.OP_LOOP (by decide) rfl
      (by simp [loopBytes, alloc.vec.Vec.deref, bodyState, global_simps])) hsOpen]
  rw [loop_step recorder loopBytes env emptyContext openLog before (nestedState .Loop false 2#usize)
    (nestedState .Loop false 3#usize) (nestedState .Loop true 3#usize) code.OP_UNREACHABLE
    (by simp [nestedState]) (read_at loopBytes _ 3#usize code.OP_UNREACHABLE (by decide) rfl
      (by simp [loopBytes, alloc.vec.Vec.deref, nestedState, global_simps])) hsUnreachable]
  rw [loop_step recorder loopBytes env emptyContext before loopLog (nestedState .Loop true 3#usize)
    (nestedState .Loop true 4#usize) (nestedState .Loop true 5#usize) code.OP_BR
    (by simp [nestedState]) (read_at loopBytes _ 4#usize code.OP_BR (by decide) rfl
      (by simp [loopBytes, alloc.vec.Vec.deref, nestedState, global_simps])) hsBr]
  unfold code.validate_body_with_loop
  rw [loop]
  simp [code.validate_body_with_loop.body, code.control_stack_empty, alloc.vec.Vec.is_empty,
    code.read_op.eof (nestedState .Loop true 5#usize) loopBytes (by decide),
    show (nestedState .Loop true 5#usize).ctrls.val.isEmpty = false from rfl,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.BrTableTraceExamples
