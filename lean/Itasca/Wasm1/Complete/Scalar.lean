import Itasca.Support.Result
import Itasca.Spec.TypingInversion
import Itasca.Handler.SimplePrefix
import Itasca.Binary.Wasm1.EncodingComplete
import Itasca.Handler.RawControl
import Itasca.Handler.EnvDispatch
import Itasca.Binary.Wasm1.DeclaredReferences
import Itasca.Visitor.RunTrace
import Itasca.Visitor.Total

/-!
Sections, each formerly its own module: Frame, Env, Scalar.
-/

/-! ## Frame -/

section

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
def StepResult {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (opcode : U8) (next : Usize) (out : List valtype) : Prop :=
  ∃ s, code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx opcode () =
      .ok (.Ok (), s, ()) ∧ s.pos = next ∧ f.Output out s ∧
    s.vals.val.length ≤ st.vals.val.length + 1

end Itasca.Wasm1.Completeness

end

/-! ## Env -/

section

/-!
# Wasm 1.0 environment instruction completeness

For `local.get`, `local.set`, `local.tee`, `global.get`, `global.set`, `call`, `call_indirect`,
`memory.size`, `memory.grow` and the load/store rows (`memory`), the generated `Instr_ok` typing
under a matching `context` makes `code.step` accept the encoded instruction. Each result has the
`StepResult` form.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1.Completeness

private theorem finish {st : code.OpIterState} (f : Frame st)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (opcode : U8)
    (before : List valtype) (outputs : List wasm_types.ValueType) (next : Usize)
    {α : Type} (value : α) (s : code.OpIterState)
    (hp : EnvComplete.Post st f.outer f.operands before outputs next value (.Ok value, s))
    (houtputs : outputs.length ≤ 1)
    (hs : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx opcode () =
      .ok (.Ok (), s, ())) :
    StepResult f data env ctx opcode next (before ++ outputs.map Translate.valueType) := by
  obtain ⟨_, hc, hpos, rest, hv, hlen, hr⟩ := hp
  refine ⟨s, hs, hpos, f.output_of_same_ctrls hc hv hr, ?_⟩
  simp only [hv, f.vals, List.length_append]
  omega

theorem localGet {st} (f : Frame st) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (C : context) (hc : EnvTranslation.Matches env ctx C) (idx : U32)
    (bytes : List U8) (next : Usize) (he : Leb128.Encoding bytes idx.val)
    (hb : Wasm1.BytesAt data st.pos bytes next) (front ins outs : List valtype)
    (ht : Instr_ok C (.LOCAL_GET (.mk_uN idx.val)) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins))
    (hsize : st.vals.val.length < Usize.max) :
    StepResult f data env ctx 0x20#u8 next (front ++ outs) := by
  cases ht with
  | local_get _ _ t hi ht _ _ =>
    obtain ⟨v, hi, ht, hv⟩ := hc.local_lookup idx t hi ht
    obtain ⟨⟨_, s⟩, hread, hpost⟩ := WP.spec_imp_exists
      (code.read_local_get.complete st data ctx idx next v (hb.read_u32 idx he) hi ht
        f.outer f.operands front f.vals hsize (by simpa [f.poly_eq] using hr))
    obtain ⟨rfl, hp⟩ := hpost
    have result := finish f data env ctx code.OP_LOCAL_GET front [v] next idx s ⟨rfl, hp⟩
      (by simp) (by simp [hread, code.visit,
        code.OpVisitor.on_local_get.default, core.result.Result.Insts.CoreOpsTry.branch])
    simpa [code.OP_LOCAL_GET, hv] using result

theorem localSet {st} (f : Frame st) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (C : context) (hc : EnvTranslation.Matches env ctx C) (idx : U32)
    (bytes : List U8) (next : Usize) (he : Leb128.Encoding bytes idx.val)
    (hb : Wasm1.BytesAt data st.pos bytes next) (front ins outs : List valtype)
    (ht : Instr_ok C (.LOCAL_SET (.mk_uN idx.val)) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x21#u8 next (front ++ outs) := by
  cases ht with
  | local_set _ _ t hi ht _ _ =>
    obtain ⟨v, hi, ht, hv⟩ := hc.local_lookup idx t hi ht
    obtain ⟨⟨_, s⟩, hread, hpost⟩ := WP.spec_imp_exists
      (code.read_local_set.complete st data ctx idx next v (hb.read_u32 idx he) hi ht
        f.outer f.operands front f.vals f.base_eq (by simpa [f.poly_eq, hv] using hr))
    obtain ⟨rfl, hp⟩ := hpost
    have result := finish f data env ctx code.OP_LOCAL_SET front [] next idx s ⟨rfl, hp⟩
      (by simp) (by simp [hread, code.visit,
        code.OpVisitor.on_local_set.default, core.result.Result.Insts.CoreOpsTry.branch])
    simpa [code.OP_LOCAL_SET] using result

theorem localTee {st} (f : Frame st) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (C : context) (hc : EnvTranslation.Matches env ctx C) (idx : U32)
    (bytes : List U8) (next : Usize) (he : Leb128.Encoding bytes idx.val)
    (hb : Wasm1.BytesAt data st.pos bytes next) (front ins outs : List valtype)
    (ht : Instr_ok C (.LOCAL_TEE (.mk_uN idx.val)) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins))
    (hsize : st.vals.val.length < Usize.max) :
    StepResult f data env ctx 0x22#u8 next (front ++ outs) := by
  cases ht with
  | local_tee _ _ t hi ht _ _ =>
    obtain ⟨v, hi, ht, hv⟩ := hc.local_lookup idx t hi ht
    obtain ⟨⟨_, s⟩, hread, hpost⟩ := WP.spec_imp_exists
      (code.read_local_tee.complete st data ctx idx next v (hb.read_u32 idx he) hi ht
        f.outer f.operands front f.vals f.base_eq hsize (by simpa [f.poly_eq, hv] using hr))
    obtain ⟨rfl, hp⟩ := hpost
    have result := finish f data env ctx code.OP_LOCAL_TEE front [v] next idx s ⟨rfl, hp⟩
      (by simp) (by simp [hread, code.visit,
        code.OpVisitor.on_local_tee.default, core.result.Result.Insts.CoreOpsTry.branch])
    simpa [code.OP_LOCAL_TEE, hv] using result

theorem globalGet {st} (f : Frame st) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (C : context) (hc : EnvTranslation.Matches env ctx C) (idx : U32)
    (bytes : List U8) (next : Usize) (he : Leb128.Encoding bytes idx.val)
    (hb : Wasm1.BytesAt data st.pos bytes next) (front ins outs : List valtype)
    (ht : Instr_ok C (.GLOBAL_GET (.mk_uN idx.val)) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins))
    (hsize : st.vals.val.length < Usize.max) :
    StepResult f data env ctx 0x23#u8 next (front ++ outs) := by
  cases ht with
  | global_get _ _ t m hi ht _ _ =>
    obtain ⟨gt, hi, ht, hv⟩ := hc.global_lookup idx _ hi ht
    have hvt : Translate.valueType gt.valtype = t := (globaltype.mk_globaltype.inj hv).2
    obtain ⟨⟨_, s⟩, hread, hpost⟩ := WP.spec_imp_exists
      (code.read_global_get.complete st data env idx next gt (hb.read_u32 idx he) hi ht
        f.outer f.operands front f.vals hsize (by simpa [f.poly_eq] using hr))
    obtain ⟨rfl, hp⟩ := hpost
    have result := finish f data env ctx code.OP_GLOBAL_GET front [gt.valtype] next idx s ⟨rfl, hp⟩
      (by simp) (by simp [hread, code.visit,
        code.OpVisitor.on_global_get.default, core.result.Result.Insts.CoreOpsTry.branch])
    simpa [code.OP_GLOBAL_GET, hvt] using result

theorem globalSet {st} (f : Frame st) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (C : context) (hc : EnvTranslation.Matches env ctx C) (idx : U32)
    (bytes : List U8) (next : Usize) (he : Leb128.Encoding bytes idx.val)
    (hb : Wasm1.BytesAt data st.pos bytes next) (front ins outs : List valtype)
    (ht : Instr_ok C (.GLOBAL_SET (.mk_uN idx.val)) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x24#u8 next (front ++ outs) := by
  cases ht with
  | global_set _ _ t hi ht _ _ =>
    obtain ⟨gt, hi, ht, hv⟩ := hc.global_lookup idx _ hi ht
    have hvt : Translate.valueType gt.valtype = t := (globaltype.mk_globaltype.inj hv).2
    have hm : gt.mutability = .Var :=
      Translate.mutability_injective (globaltype.mk_globaltype.inj hv).1
    obtain ⟨⟨_, s⟩, hread, hpost⟩ := WP.spec_imp_exists
      (code.read_global_set.complete st data env idx next gt (hb.read_u32 idx he) hi ht hm
        f.outer f.operands front f.vals f.base_eq (by simpa [f.poly_eq, hvt] using hr))
    obtain ⟨rfl, hp⟩ := hpost
    have result := finish f data env ctx code.OP_GLOBAL_SET front [] next idx s ⟨rfl, hp⟩
      (by simp) (by simp [hread, code.visit,
        code.OpVisitor.on_global_set.default, core.result.Result.Insts.CoreOpsTry.branch])
    simpa [code.OP_GLOBAL_SET] using result

theorem memorySize {st} (f : Frame st) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (C : context) (hc : EnvTranslation.Matches env ctx C)
    (next : Usize) (hb : Wasm1.BytesAt data st.pos [0#u8] next) (front ins outs : List valtype)
    (ht : Instr_ok C .MEMORY_SIZE (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins))
    (hsize : st.vals.val.length < Usize.max) :
    StepResult f data env ctx 0x3F#u8 next (front ++ outs) := by
  cases ht with
  | memory_size _ _ hm _ _ _ _ =>
    obtain ⟨⟨_, s⟩, hread, hpost⟩ := WP.spec_imp_exists
      (code.read_memory_size.complete st data env next hb.read_byte (hc.memory_exists hm)
        f.outer f.operands front f.vals hsize (by simpa [f.poly_eq] using hr))
    obtain ⟨rfl, hp⟩ := hpost
    have result := finish f data env ctx code.OP_MEMORY_SIZE front [.I32] next () s ⟨rfl, hp⟩
      (by simp) (by simp [hread, code.visit,
        code.OpVisitor.on_memory_size.default, core.result.Result.Insts.CoreOpsTry.branch])
    simpa [code.OP_MEMORY_SIZE, Translate.valueType] using result

theorem memoryGrow {st} (f : Frame st) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (C : context) (hc : EnvTranslation.Matches env ctx C)
    (next : Usize) (hb : Wasm1.BytesAt data st.pos [0#u8] next) (front ins outs : List valtype)
    (ht : Instr_ok C .MEMORY_GROW (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins))
    (hsize : st.vals.val.length < Usize.max) :
    StepResult f data env ctx 0x40#u8 next (front ++ outs) := by
  cases ht with
  | memory_grow _ _ hm _ _ _ _ =>
    obtain ⟨⟨_, s⟩, hread, hpost⟩ := WP.spec_imp_exists
      (code.read_memory_grow.complete st data env next hb.read_byte (hc.memory_exists hm)
        f.outer f.operands front f.vals f.base_eq hsize (by simpa [f.poly_eq] using hr))
    obtain ⟨rfl, hp⟩ := hpost
    have result := finish f data env ctx code.OP_MEMORY_GROW front [.I32] next () s ⟨rfl, hp⟩
      (by simp) (by simp [hread, code.visit,
        code.OpVisitor.on_memory_grow.default, core.result.Result.Insts.CoreOpsTry.branch])
    simpa [code.OP_MEMORY_GROW, Translate.valueType] using result

/-- Every independently described memory row executes successfully when its
principal generated typing rule applies to the realized operand stack. -/
theorem memory {st} (f : Frame st) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (C : context) (hc : EnvTranslation.Matches env ctx C)
    (opcode : U8) (operation : MemoryMeaning.Operation)
    (hrow : MemoryMeaning.opcodeMeaning opcode = some operation) (arg : code.MemArg)
    (alignment offset : List U8) (next : Usize)
    (ha : Leb128.Encoding alignment arg.align.val) (ho : Leb128.Encoding offset arg.offset.val)
    (hb : Wasm1.BytesAt data st.pos (alignment ++ offset) next) (front ins outs : List valtype)
    (ht : Instr_ok C (operation.op arg) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins))
    (hsize : st.vals.val.length < Usize.max) :
    StepResult f data env ctx opcode next (front ++ outs) := by
  obtain ⟨hm, halign, hins, houts⟩ := MemoryMeaning.opcodeMeaning_inverse opcode operation hrow C arg ins outs ht
  have hmem := hc.memory_exists hm
  have hd := hb.read_memarg st arg ha ho
  cases hstore : operation.store with
  | false =>
    obtain ⟨⟨_, s⟩, hread, hpost⟩ := WP.spec_imp_exists
      (code.read_load.complete st data env next arg operation.ty operation.naturalAlign hd hmem halign
        f.outer f.operands front f.vals f.base_eq hsize
        (by simpa [f.poly_eq, hins, MemoryMeaning.Operation.inputs, hstore, Translate.valueType] using hr))
    obtain ⟨rfl, hp⟩ := hpost
    have hstep := code.step_memory.dispatch code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      st data env ctx () opcode operation hrow
    have result := finish f data env ctx opcode front [operation.ty] next arg s ⟨rfl, hp⟩
      (by simp) (by simpa [hstore, hread, CoreVisitor.run, code.visit, VisitorErasure.visit_memory_empty,
        core.result.Result.Insts.CoreOpsTry.branch] using hstep)
    simpa [houts, MemoryMeaning.Operation.outputs, hstore] using result
  | true =>
    obtain ⟨⟨_, s⟩, hread, hpost⟩ := WP.spec_imp_exists
      (code.read_store.complete st data env next arg operation.ty operation.naturalAlign hd hmem halign
        f.outer f.operands front f.vals f.base_eq
        (by simpa [f.poly_eq, hins, MemoryMeaning.Operation.inputs, hstore, Translate.valueType] using hr))
    obtain ⟨rfl, hp⟩ := hpost
    have hstep := code.step_memory.dispatch code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      st data env ctx () opcode operation hrow
    have result := finish f data env ctx opcode front [] next arg s ⟨rfl, hp⟩
      (by simp) (by simpa [hstore, hread, CoreVisitor.run, code.visit, VisitorErasure.visit_memory_empty,
        core.result.Result.Insts.CoreOpsTry.branch] using hstep)
    simpa [houts, MemoryMeaning.Operation.outputs, hstore] using result

end Itasca.Wasm1.Completeness

end

/-! ## Scalar -/

section

/-!
# Wasm 1.0 scalar instruction completeness

`Numeric.signature` recovers the independent input and output types of a numeric opcode from its
generated typing. `Frame.step_numeric`, `step_drop`, `step_select` and the four `step_*Const`
theorems, together with `nop` and `unreachable`, show that `code.step` accepts these
instructions when the generated `Instr_ok` typing holds on the represented stack.
-/

open Aeneas Aeneas.Std

namespace Itasca.Numeric

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The principal generated typing of a mapped numeric opcode has exactly its independent effect. -/
theorem signature (opcode : U8) (op : Operation) (hmap : NumericOp opcode op)
    (C : context) (ins outs : List valtype)
    (ht : Instr_ok C op.instruction (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = op.inputs.map Translate.valueType ∧ outs = [Translate.valueType op.output] := by
  unfold NumericOp opcodeMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap <;> try contradiction
  all_goals subst op
  all_goals cases ht; simp [Operation.inputs, unary, binary, test, relation, conversion, valueType,
    Translate.valueType, valtype_numtype]

end Itasca.Numeric

namespace Itasca.Wasm1.Completeness

private theorem same_ctrls {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (opcode : U8) (next : Usize) (out : List valtype)
    (s : code.OpIterState) (after : List code.StackType)
    (hs : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx opcode () =
      .ok (.Ok (), s, ()))
    (hp : s.pos = next) (hc : s.ctrls = st.ctrls) (hv : s.vals.val = f.outer ++ after)
    (hl : after.length ≤ f.operands.length + 1)
    (ht : Sequence.Realizes (Control.polymorphic st) after out) :
    StepResult f data env ctx opcode next out := by
  refine ⟨s, hs, hp, f.output_of_same_ctrls hc hv ht, ?_⟩
  simp only [hv, f.vals, List.length_append]
  omega

/-- Numeric dispatch accepts its generated principal typing on the represented stack. -/
theorem Frame.step_numeric {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (opcode : U8) (op : Numeric.Operation) (next : Usize)
    (C : context) (front ins outs : List valtype)
    (hmap : Numeric.NumericOp opcode op) (hb : Wasm1.BytesAt data st.pos [] next)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Instr_ok C op.instruction (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx opcode next (front ++ outs) := by
  obtain ⟨rfl, rfl⟩ := Numeric.signature opcode op hmap C ins outs ht
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ := Numeric.read.complete op st f.outer f.operands front
    f.vals f.base_eq hsize (by simpa [f.poly_eq] using hr)
  apply same_ctrls f data env ctx opcode next _ s after _ (hp.trans hb.empty.symm) hc hv hl hout
  rw [code.step.numeric_dispatch _ _ _ _ _ _ _ hmap.bounds.1,
    code.step_numeric.dispatch _ _ _ _ _ hmap]
  simp [CoreVisitor.run, hs, VisitorErasure.visit_numeric_empty, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- Drop consumes the type supplied by its principal typing rule. -/
theorem Frame.step_drop {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (next : Usize) (C : context) (front ins outs : List valtype)
    (hb : Wasm1.BytesAt data st.pos [] next)
    (ht : Instr_ok C .DROP (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x1A#u8 next (front ++ outs) := by
  cases ht with
  | drop _ t _ _ =>
      obtain ⟨value, s, after, hs, hc, hp, hv, hl, _, hout⟩ :=
        code.read_drop.complete st f.outer f.operands front t f.vals f.base_eq
          (by simpa [f.poly_eq] using hr)
      apply same_ctrls f data env ctx 0x1A#u8 next _ s after _ (hp.trans hb.empty.symm) hc hv
        (by omega) (by simpa using hout)
      simp [global_simps, hs, code.OpVisitor.on_drop.default, code.visit,
        core.result.Result.Insts.CoreOpsTry.branch]

/-- Untyped `select` consumes the operands given by its principal typing rule. -/
theorem Frame.step_select {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (next : Usize) (C : context) (front ins outs : List valtype)
    (hb : Wasm1.BytesAt data st.pos [] next) (hsize : st.vals.val.length < Usize.max)
    (ht : Instr_ok C (.SELECT none) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x1B#u8 next (front ++ outs) := by
  cases ht with
  | select_impl _ t _ _ _ hsub htype _ _ =>
      obtain ⟨hfun, hext⟩ := StackSemantics.select_type_not_reference hsub htype
      obtain ⟨value, s, after, hs, hc, hp, hv, hl, _, hout⟩ :=
        code.read_select.complete st f.outer f.operands front t f.vals f.base_eq hsize hfun hext
          (by simpa [f.poly_eq] using hr)
      apply same_ctrls f data env ctx 0x1B#u8 next _ s after _ (hp.trans hb.empty.symm) hc hv hl hout
      simp [hs, code.OpVisitor.on_select.default, code.visit, core.result.Result.Insts.CoreOpsTry.branch]

/-- Exact scalar bytes and principal typing force successful constant dispatch. -/
theorem Frame.step_i32Const {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (value : I32) (bytes : List U8) (next : Usize)
    (C : context) (front ins outs : List valtype)
    (he : SignedLeb32.Encoding bytes value.val) (hbytes : Wasm1.BytesAt data st.pos bytes next)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Instr_ok C (Spec.i32Const value) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x41#u8 next (front ++ outs) := by
  have heffect : ins = [] ∧ outs = [.I32] := by cases ht; exact ⟨rfl, rfl⟩
  rcases heffect with ⟨rfl, rfl⟩
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ :=
    code.read_i32_const.complete st data value next f.outer f.operands front
      ⟨bytes, hbytes.suffix, hbytes.length, hbytes.bound, he⟩ f.vals hsize
      (by simpa [f.poly_eq] using hr)
  apply same_ctrls f data env ctx 0x41#u8 next _ s after _ hp hc hv (by omega) hout
  simp [global_simps, hs, code.OpVisitor.on_i32_const.default, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- Exact scalar bytes and principal typing force successful constant dispatch. -/
theorem Frame.step_i64Const {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (value : I64) (bytes : List U8) (next : Usize)
    (C : context) (front ins outs : List valtype)
    (he : SignedLeb64.Encoding bytes value.val) (hbytes : Wasm1.BytesAt data st.pos bytes next)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Instr_ok C (ScalarConst.i64 value) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x42#u8 next (front ++ outs) := by
  have heffect : ins = [] ∧ outs = [.I64] := by cases ht; exact ⟨rfl, rfl⟩
  rcases heffect with ⟨rfl, rfl⟩
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ :=
    code.read_i64_const.complete st data value next f.outer f.operands front
      ⟨bytes, hbytes.suffix, hbytes.length, hbytes.bound, he⟩ f.vals hsize
      (by simpa [f.poly_eq] using hr)
  apply same_ctrls f data env ctx 0x42#u8 next _ s after _ hp hc hv (by omega) hout
  simp [global_simps, hs, code.OpVisitor.on_i64_const.default, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- Exact scalar bytes and principal typing force successful constant dispatch. -/
theorem Frame.step_f32Const {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (value : U32) (bytes : List U8) (next : Usize)
    (C : context) (front ins outs : List valtype)
    (he : FloatBits.Encoding 4 bytes value.val) (hbytes : Wasm1.BytesAt data st.pos bytes next)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Instr_ok C (ScalarConst.f32 value) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x43#u8 next (front ++ outs) := by
  have heffect : ins = [] ∧ outs = [.F32] := by cases ht; exact ⟨rfl, rfl⟩
  rcases heffect with ⟨rfl, rfl⟩
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ :=
    code.read_f32_const.complete st data value next f.outer f.operands front
      ⟨bytes, hbytes.suffix, by simpa [he.1] using hbytes.length, hbytes.bound, he⟩ f.vals hsize
      (by simpa [f.poly_eq] using hr)
  apply same_ctrls f data env ctx 0x43#u8 next _ s after _ hp hc hv (by omega) hout
  simp [global_simps, hs, code.OpVisitor.on_f32_const.default, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- Exact scalar bytes and principal typing force successful constant dispatch. -/
theorem Frame.step_f64Const {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (value : U64) (bytes : List U8) (next : Usize)
    (C : context) (front ins outs : List valtype)
    (he : FloatBits.Encoding 8 bytes value.val) (hbytes : Wasm1.BytesAt data st.pos bytes next)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Instr_ok C (ScalarConst.f64 value) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x44#u8 next (front ++ outs) := by
  have heffect : ins = [] ∧ outs = [.F64] := by cases ht; exact ⟨rfl, rfl⟩
  rcases heffect with ⟨rfl, rfl⟩
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ :=
    code.read_f64_const.complete st data value next f.outer f.operands front
      ⟨bytes, hbytes.suffix, by simpa [he.1] using hbytes.length, hbytes.bound, he⟩ f.vals hsize
      (by simpa [f.poly_eq] using hr)
  apply same_ctrls f data env ctx 0x44#u8 next _ s after _ hp hc hv (by omega) hout
  simp [global_simps, hs, code.OpVisitor.on_f64_const.default, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.Wasm1.Completeness

open Aeneas Aeneas.Std

namespace Itasca.Wasm1.Completeness

/-- `code.step` accepts `nop` whenever its generated typing holds. -/
theorem nop {st data env ctx C next front ins outs}
    (f : Frame st) (hb : Wasm1.BytesAt data st.pos [] next)
    (hop : Instr_ok C .NOP (.mk_functype (.mk_list ins) (.mk_list outs)))
    (ht : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x01#u8 next (front ++ outs) := by
  cases hop
  have he : next = st.pos := hb.empty
  subst next
  refine ⟨st, ?_, rfl, f.output_self ht, by omega⟩
  simp [global_simps, code.OpVisitor.on_nop.default, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.step` accepts `unreachable` and marks the current frame polymorphic. -/
theorem unreachable {st data env ctx C next front ins outs}
    (f : Frame st) (hb : Wasm1.BytesAt data st.pos [] next)
    (_hop : Instr_ok C .UNREACHABLE (.mk_functype (.mk_list ins) (.mk_list outs))) :
    StepResult f data env ctx 0x00#u8 next (front ++ outs) := by
  have he : next = st.pos := hb.empty
  subst next
  obtain ⟨s, hr, hv, _, hc, hp⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec st f.parents f.current f.ctrls
      (by simp [f.base, f.vals]))
  have hv' : s.vals.val = f.outer := by simpa [f.vals, f.base] using hv
  refine ⟨s, ?_, hp, ⟨true, [], hc, by simpa using hv',
    Sequence.realizes_polymorphic_empty _⟩, ?_⟩
  · simp [global_simps, code.read_unreachable, hr,
      code.OpVisitor.on_unreachable.default, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch]
  · simp only [hv', f.vals, List.length_append]
    omega

end Itasca.Wasm1.Completeness

end
