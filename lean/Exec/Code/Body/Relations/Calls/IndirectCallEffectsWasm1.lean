import Exec.Code.Body.Reader.Calls.ReaderIndirectCallWasm1
import Exec.Code.Body.Reader.Calls.ReaderCallEffects
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The actual Wasm 1 indirect-call reader exposes its checked signature and
function-reference table zero together with the full stack transfer. -/
theorem indirect_call_effect_wasm1 (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment) (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_call_indirect st data env ⦃ r => ∀ idx, r.1 = .Ok idx →
      ∃ (ft : types.FuncType) (tt : types.TableType) (rest : List code.StackType),
        env.types.val[idx.val]? = some ft ∧ env.table_types.val[0]? = some tt ∧ tt.elem = .FuncRef ∧
        r.2.vals.val = outer ++ (rest ++ ft.results.val.map code.StackType.Val) ∧
        (∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
          Sequence.Realizes (Control.polymorphic st) segment
            (ts ++ (ft.params.val.map Translate.valueType ++ [.I32]))) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hout⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  dsimp only at hv hc hout
  cases r with
  | Err e =>
      simp [code.read_call_indirect, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok idx =>
      obtain ⟨⟨rz, sz⟩, hz, hvz, hcz, houtz⟩ := WP.spec_imp_exists (code.read_reserved_zero.spec s data)
      dsimp only at hvz hcz houtz
      cases rz with
      | Err e =>
          simp [code.read_call_indirect, hr, hz, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
          by_cases htable : env.table_types.val = []
          · simp [code.read_call_indirect, hr, hz, alloc.vec.Vec.is_empty, htable,
              core.result.Result.Insts.CoreOpsTry.branch]
          · have htablelen : 0 < env.table_types.val.length := List.length_pos_iff.mpr htable
            obtain ⟨tt, hget, hgeteq⟩ := WP.spec_imp_exists
              (alloc.vec.Vec.index_usize_spec env.table_types 0#usize (by simpa using htablelen))
            have htt : env.table_types.val[0] = tt := by simpa using hgeteq.symm
            cases helem : tt.elem with
            | ExternRef =>
                simp [code.read_call_indirect, hr, hz, alloc.vec.Vec.is_empty, htable,
                  hget, helem, Itasca.types.ElemType.value_type, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                  Itasca.types.ValueType.Insts.CoreCmpPartialEqValueType.eq,
                  core.result.Result.Insts.CoreOpsTry.branch]
            | FuncRef =>
                have hfun : env.table_types.val[0].elem = .FuncRef := by rw [htt]; exact helem
                by_cases hi : idx.val < env.types.val.length
                · have hix : (UScalar.cast .Usize idx).val < env.types.val.length := by simpa using hi
                  obtain ⟨ft, hft, heq⟩ := WP.spec_imp_exists
                    (alloc.vec.Vec.index_usize_spec env.types (UScalar.cast .Usize idx) hix)
                  have htype : env.types.val[idx.val] = ft := by simpa using heq.symm
                  have hsmall := Nat.not_le_of_gt hi
                  obtain ⟨rreq, hreq, hresults⟩ := WP.spec_imp_exists
                    (code.require_single_result.spec (alloc.vec.Vec.deref ft.results))
                  cases rreq with
                  | Err e =>
                      simp [code.read_call_indirect, hget, helem, Itasca.types.ElemType.value_type,
                      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, Itasca.types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hr, hz, alloc.vec.Vec.is_empty, htable,
                        lift, hsmall, hft, hreq, core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                  | Ok u =>
                      obtain ⟨⟨rc, sc⟩, hcond, hcc, hpc, condrest, hvc, hlc, houtc⟩ := WP.spec_imp_exists
                        (code.pop_with_type.realizes sz outer segment .I32
                          (by simpa [hvz, hv] using hvals)
                          (by simpa [Control.base, hcz, hc] using hbase))
                      dsimp only at hcc hpc hvc hlc houtc
                      cases rc with
                      | Err e =>
                          simp [code.read_call_indirect, hget, helem, Itasca.types.ElemType.value_type,
                      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, Itasca.types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hr, hz, alloc.vec.Vec.is_empty, htable,
                            lift, hsmall, hft, hreq, hcond, core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                      | Ok popped =>
                          obtain ⟨⟨r', s'⟩, hp, hc', hpos, rest, hv', hlen, hout'⟩ := WP.spec_imp_exists
                            (code.pop_types.realizes sc outer condrest (alloc.vec.Vec.deref ft.params)
                              hvc (by simpa [Control.base, hcc, hcz, hc] using hbase))
                          dsimp only at hc' hpos hv' hlen hout'
                          cases r' with
                          | Err e =>
                              simp [code.read_call_indirect, hget, helem, Itasca.types.ElemType.value_type,
                      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, Itasca.types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hr, hz, alloc.vec.Vec.is_empty, htable,
                                lift, hsmall, hft, hreq, hcond, hp, core.result.Result.Insts.CoreOpsTry.branch,
                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                          | Ok u =>
                              have hresultlen : ft.results.val.length ≤ 1 := by
                                simpa [alloc.vec.Vec.deref] using hresults
                              have hcap : s'.vals.val.length + (alloc.vec.Vec.deref ft.results).val.length ≤ Usize.max := by
                                simp only [hv', hvals, List.length_append, alloc.vec.Vec.deref] at *
                                omega
                              obtain ⟨s'', hpush, hv'', hc'', hpos'⟩ := WP.spec_imp_exists
                                (code.push_types.spec s' (alloc.vec.Vec.deref ft.results) hcap)
                              have hcondpop : ∀ ts, Sequence.Realizes (Control.polymorphic st) condrest ts →
                                  Sequence.Realizes (Control.polymorphic st) segment (ts ++ [.I32]) := by
                                simpa [Control.polymorphic, hcz, hc, Translate.valueType] using houtc.2
                              have hparampop : ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
                                  Sequence.Realizes (Control.polymorphic st) condrest
                                    (ts ++ ft.params.val.map Translate.valueType) := by
                                simpa [Control.polymorphic, hcc, hcz, hc, alloc.vec.Vec.deref] using hout'
                              have hpop : ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
                                  Sequence.Realizes (Control.polymorphic st) segment
                                    (ts ++ (ft.params.val.map Translate.valueType ++ [.I32])) := by
                                intro ts ht
                                simpa [List.append_assoc] using hcondpop _ (hparampop ts ht)
                              rw [WP.spec_equiv_exists]
                              refine ⟨(.Ok idx, s''), ?_, ?_⟩
                              · simp [code.read_call_indirect, hget, helem, Itasca.types.ElemType.value_type,
                      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, Itasca.types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hr, hz, alloc.vec.Vec.is_empty, htable,
                                  lift, hsmall, hft, hreq, hcond, hp, hpush, core.result.Result.Insts.CoreOpsTry.branch]
                              · intro ix heq
                                cases heq
                                refine ⟨ft,tt,rest,?_,?_,helem,?_,hpop⟩
                                · simpa [List.getElem?_eq_getElem hi] using congrArg some htype
                                · simpa [List.getElem?_eq_getElem htablelen] using congrArg some htt
                                · simpa [hv',List.append_assoc,alloc.vec.Vec.deref] using hv''
                · have hlarge := Nat.le_of_not_gt hi
                  simp [code.read_call_indirect, hget, helem, Itasca.types.ElemType.value_type,
                      core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, Itasca.types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hr, hz, alloc.vec.Vec.is_empty, htable,
                    lift, hlarge, core.result.Result.Insts.CoreOpsTry.branch]

/-- Live concrete stack suffixes come from the reader's parameter transfer. -/
theorem reader_indirect_call_stack_wasm1 (st out : code.OpIterState) (data : Slice U8) (env : module.Env)
    (index : U32) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (capacity : st.vals.val.length < Usize.max)
    (known : ConcreteStack st.vals.val) (monomorphic : Control.polymorphic st = false)
    (accepted : code.read_call_indirect st data env = .ok (.Ok index,out)) :
    ∃ (ft : types.FuncType) (tt : types.TableType) (front : List types.ValueType),
      env.types.val[index.val]? = some ft ∧ env.table_types.val[0]? = some tt ∧ tt.elem = .FuncRef ∧
      Sequence.stackTypes st.vals.val = (front.map Translate.valueType ++ ft.params.val.map Translate.valueType) ++ [.I32] ∧
      out.vals.val = (front ++ ft.results.val).map code.StackType.Val := by
  have effect := indirect_call_effect_wasm1 st data env outer segment values base capacity
  rw [accepted,WP.spec_ok] at effect
  obtain ⟨ft,tt,rest,typeFound,tableFound,elem,afterValues,transfer⟩ := effect index rfl
  dsimp only at afterValues
  rw [monomorphic] at transfer
  obtain ⟨front,beforeTypes,afterConcrete⟩ := call_full_stack_types (ft.params.val ++ [.I32]) ft.results.val known values afterValues
    (by simpa [List.map_append,Translate.valueType] using transfer)
  refine ⟨ft,tt,front,typeFound,tableFound,elem,?_,afterConcrete⟩
  simpa [List.map_append,Translate.valueType,List.append_assoc] using beforeTypes
end Exec.Code
