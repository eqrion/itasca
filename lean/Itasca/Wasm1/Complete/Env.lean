import Itasca.Wasm1.Complete.Frame
import Itasca.Handler.EnvComplete
import Itasca.Support.EnvTranslation
import Itasca.Handler.EnvDispatch
import Itasca.Binary.Wasm1.MemoryTyping
import Itasca.Visitor.StepErasure

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
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (opcode : U8)
    (before : List valtype) (outputs : List types.ValueType) (next : Usize)
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

theorem localGet {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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

theorem localSet {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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

theorem localTee {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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

theorem globalGet {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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

theorem globalSet {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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

theorem memorySize {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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

theorem memoryGrow {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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
theorem memory {st} (f : Frame st) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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
