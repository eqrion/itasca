import Itasca.MultiValue.ScalarEnv

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.Scalar

def MemoryPost (inputs : List valtype) (data : Slice U8) (st : code.OpIterState)
    (outer segment : List code.StackType) (C : context) (ops : List instr)
    (op : code.MemArg → instr)
    (r : core.result.Result code.MemArg error.OpError × code.OpIterState) : Prop :=
  ∀ arg, r.1 = .Ok arg →
    (∃ middle, Leb128.Decoded data st.pos arg.align middle ∧
      Leb128.Decoded data middle arg.offset r.2.pos) ∧ r.2.ctrls = st.ctrls ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
        MultiValue.TypedPrefix C inputs (ops ++ [op arg]) (Control.polymorphic st) rest

def ReservedPost (inputs : List valtype) (data : Slice U8) (st : code.OpIterState)
    (outer segment : List code.StackType) (C : context) (ops : List instr)
    (op : instr) (r : core.result.Result Unit error.OpError × code.OpIterState) : Prop :=
  r.1 = .Ok () →
    (∃ hp : st.pos.val < data.length, data.val[st.pos.val] = 0#u8 ∧ r.2.pos.val = st.pos.val + 1) ∧
    r.2.ctrls = st.ctrls ∧ ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
      MultiValue.TypedPrefix C inputs (ops ++ [op]) (Control.polymorphic st) rest

end Itasca.MultiValue.Scalar

namespace Itasca

theorem code.read_load.multi_prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (C : context) (hC : EnvTranslation.Matches env ctx C) (ops : List instr)
    (htyped : MultiValue.TypedPrefix C inputs ops (Control.polymorphic st) segment)
    (opcode : U8) (operation : MemoryMeaning.Operation)
    (hrow : MemoryMeaning.opcodeMeaning opcode = some operation) (hload : operation.store = false) :
    code.read_load st data env operation.ty operation.naturalAlign ⦃
      MultiValue.Scalar.MemoryPost inputs data st outer segment C ops operation.op ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.read_memarg.spec st data)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_load, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.MemoryPost]
  | Ok arg =>
      obtain ⟨rcheck, hcheck, hcheckpost⟩ := WP.spec_imp_exists
        (code.check_memory_and_alignment.spec env arg operation.naturalAlign)
      cases rcheck with
      | Err e =>
          simp [code.read_load, hr, hcheck, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.MemoryPost]
      | Ok u =>
          obtain ⟨⟨r', s'⟩, hp, hc', hpos, rest, hv', hlen, hout'⟩ := WP.spec_imp_exists
            (code.pop_with_type.realizes s outer segment .I32 (by simpa [hv] using hvals)
              (by simpa [Control.base, hc] using hbase))
          dsimp only at hc' hpos hv' hlen hout'
          cases r' with
          | Err e =>
              simp [code.read_load, hr, hcheck, hp, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.MemoryPost]
          | Ok popped =>
              have hcap : s'.vals.val.length < Usize.max := by
                simp only [hv', hvals, List.length_append] at *
                omega
              obtain ⟨s'', hpush, hv'', hc'', hpos'⟩ := WP.spec_imp_exists
                (code.push_val.spec s' (.Val operation.ty) hcap)
              have hpop : ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
                  Sequence.Realizes (Control.polymorphic st) segment (ts ++ [.I32]) := by
                simpa [Control.polymorphic, hc, Translate.valueType] using hout'.2
              obtain ⟨hwf, hop⟩ := hC.memory_operation opcode operation hrow arg hcheckpost.1 hcheckpost.2
              have htyping := (MultiValue.ResumePrefix.after_pop htyped hpop).finish hC.wf
                (operation.op arg) [operation.ty] hwf
                (by simpa [MemoryMeaning.Operation.inputs, MemoryMeaning.Operation.outputs, hload,
                  Translate.valueType] using hop)
              rw [WP.spec_equiv_exists]
              refine ⟨(.Ok arg, s''), ?_, ?_⟩
              · simp [code.read_load, hr, hcheck, hp, hpush, core.result.Result.Insts.CoreOpsTry.branch]
              · intro a heq
                cases heq
                refine ⟨?_, hc''.trans (hc'.trans hc), rest ++ [.Val operation.ty],
                  ?_, by simpa using Nat.add_le_add_right hlen 1, by simpa using htyping⟩
                · simpa [hpos', hpos] using hout
                · simpa [hv', List.append_assoc] using hv''

theorem code.read_store.multi_prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (C : context) (hC : EnvTranslation.Matches env ctx C) (ops : List instr)
    (htyped : MultiValue.TypedPrefix C inputs ops (Control.polymorphic st) segment)
    (opcode : U8) (operation : MemoryMeaning.Operation)
    (hrow : MemoryMeaning.opcodeMeaning opcode = some operation) (hstore : operation.store = true) :
    code.read_store st data env operation.ty operation.naturalAlign ⦃
      MultiValue.Scalar.MemoryPost inputs data st outer segment C ops operation.op ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.read_memarg.spec st data)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_store, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.MemoryPost]
  | Ok arg =>
      obtain ⟨rcheck, hcheck, hcheckpost⟩ := WP.spec_imp_exists
        (code.check_memory_and_alignment.spec env arg operation.naturalAlign)
      cases rcheck with
      | Err e =>
          simp [code.read_store, hr, hcheck, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.MemoryPost]
      | Ok u =>
          obtain ⟨⟨r', s'⟩, hp, hc', hpos, rest, hv', hlen, hout'⟩ := WP.spec_imp_exists
            (code.pop_with_type.realizes s outer segment operation.ty (by simpa [hv] using hvals)
              (by simpa [Control.base, hc] using hbase))
          dsimp only at hc' hpos hv' hlen hout'
          cases r' with
          | Err e =>
              simp [code.read_store, hr, hcheck, hp, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.MemoryPost]
          | Ok popped =>
              obtain ⟨⟨r'', s''⟩, hp', hc'', hpos', rest', hv'', hlen', hout''⟩ := WP.spec_imp_exists
                (code.pop_with_type.realizes s' outer rest .I32 hv'
                  (by simpa [Control.base, hc', hc] using hbase))
              dsimp only at hc'' hpos' hv'' hlen' hout''
              cases r'' with
              | Err e =>
                  simp [code.read_store, hr, hcheck, hp, hp', core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.MemoryPost]
              | Ok popped =>
                  have hfirst : ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
                      Sequence.Realizes (Control.polymorphic st) segment (ts ++ [Translate.valueType operation.ty]) := by
                    simpa [Control.polymorphic, hc] using hout'.2
                  have hsecond : ∀ ts, Sequence.Realizes (Control.polymorphic st) rest' ts →
                      Sequence.Realizes (Control.polymorphic st) rest (ts ++ [.I32]) := by
                    simpa [Control.polymorphic, hc', hc, Translate.valueType] using hout''.2
                  have hpop : ∀ ts, Sequence.Realizes (Control.polymorphic st) rest' ts →
                      Sequence.Realizes (Control.polymorphic st) segment (ts ++ [.I32, Translate.valueType operation.ty]) := by
                    intro ts ht
                    simpa [List.append_assoc] using hfirst _ (hsecond ts ht)
                  obtain ⟨hwf, hop⟩ := hC.memory_operation opcode operation hrow arg hcheckpost.1 hcheckpost.2
                  have htyping := (MultiValue.ResumePrefix.after_pop htyped hpop).finish hC.wf
                    (operation.op arg) [] hwf
                    (by simpa [MemoryMeaning.Operation.inputs, MemoryMeaning.Operation.outputs, hstore,
                      Translate.valueType] using hop)
                  rw [WP.spec_equiv_exists]
                  refine ⟨(.Ok arg, s''), ?_, ?_⟩
                  · simp [code.read_store, hr, hcheck, hp, hp', core.result.Result.Insts.CoreOpsTry.branch]
                  · intro a heq
                    cases heq
                    exact ⟨by simpa [hpos', hpos] using hout, hc''.trans (hc'.trans hc),
                      rest', hv'', by omega, by simpa using htyping⟩

theorem code.read_memory_size.multi_prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hsize : st.vals.val.length < Usize.max)
    (C : context) (hC : EnvTranslation.Matches env ctx C) (ops : List instr)
    (htyped : MultiValue.TypedPrefix C inputs ops (Control.polymorphic st) segment) :
    code.read_memory_size st data env ⦃ MultiValue.Scalar.ReservedPost inputs data st outer segment C ops .MEMORY_SIZE ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.read_reserved_zero.spec st data)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_memory_size, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.ReservedPost]
  | Ok u =>
      obtain ⟨rmem, hmem, hmempost⟩ := WP.spec_imp_exists (code.require_memory.spec env)
      cases rmem with
      | Err e =>
          simp [code.read_memory_size, hr, hmem, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.ReservedPost]
      | Ok u =>
          obtain ⟨s', hp, hv', hc', hpos⟩ := WP.spec_imp_exists
            (code.push_val.spec s (.Val .I32) (by simpa [hv] using hsize))
          have htyping := (MultiValue.ResumePrefix.of_prefix htyped).finish hC.wf .MEMORY_SIZE [.I32]
            .instr_case_62 (hC.memory_size hmempost)
          rw [WP.spec_equiv_exists]
          refine ⟨(.Ok (), s'), ?_, ?_⟩
          · simp [code.read_memory_size, hr, hmem, hp, core.result.Result.Insts.CoreOpsTry.branch]
          · intro _
            refine ⟨?_, hc'.trans hc, segment ++ [.Val .I32], ?_, by simp, by simpa using htyping⟩
            · simpa [hpos] using hout
            · simpa [hv, hvals, List.append_assoc] using hv'

theorem code.read_memory_grow.multi_prefix {inputs : List valtype} (st : code.OpIterState) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (C : context) (hC : EnvTranslation.Matches env ctx C) (ops : List instr)
    (htyped : MultiValue.TypedPrefix C inputs ops (Control.polymorphic st) segment) :
    code.read_memory_grow st data env ⦃ MultiValue.Scalar.ReservedPost inputs data st outer segment C ops .MEMORY_GROW ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.read_reserved_zero.spec st data)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_memory_grow, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.ReservedPost]
  | Ok u =>
      obtain ⟨rmem, hmem, hmempost⟩ := WP.spec_imp_exists (code.require_memory.spec env)
      cases rmem with
      | Err e =>
          simp [code.read_memory_grow, hr, hmem, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.ReservedPost]
      | Ok u =>
          obtain ⟨⟨r', s'⟩, hp, hc', hpos, rest, hv', hlen, hout'⟩ := WP.spec_imp_exists
            (code.pop_with_type.realizes s outer segment .I32 (by simpa [hv] using hvals)
              (by simpa [Control.base, hc] using hbase))
          dsimp only at hc' hpos hv' hlen hout'
          cases r' with
          | Err e =>
              simp [code.read_memory_grow, hr, hmem, hp, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, MultiValue.Scalar.ReservedPost]
          | Ok popped =>
              have hcap : s'.vals.val.length < Usize.max := by
                simp only [hv', hvals, List.length_append] at *
                omega
              obtain ⟨s'', hpush, hv'', hc'', hpos'⟩ := WP.spec_imp_exists
                (code.push_val.spec s' (.Val .I32) hcap)
              have hpop : ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
                  Sequence.Realizes (Control.polymorphic st) segment (ts ++ [.I32]) := by
                simpa [Control.polymorphic, hc, Translate.valueType] using hout'.2
              have htyping := (MultiValue.ResumePrefix.after_pop htyped hpop).finish hC.wf .MEMORY_GROW [.I32]
                .instr_case_63 (hC.memory_grow hmempost)
              rw [WP.spec_equiv_exists]
              refine ⟨(.Ok (), s''), ?_, ?_⟩
              · simp [code.read_memory_grow, hr, hmem, hp, hpush, core.result.Result.Insts.CoreOpsTry.branch]
              · intro _
                exact ⟨by simpa [hpos', hpos] using hout, hc''.trans (hc'.trans hc), rest ++ [.Val .I32],
                  by simpa [hv', List.append_assoc] using hv'', by simpa using Nat.add_le_add_right hlen 1,
                  by simpa using htyping⟩

end Itasca
