import Itasca.Runtime.Code.Body.Reader.Calls.ReaderIndirectCall
import Itasca.Runtime.Code.Body.Reader.Calls.ReaderCallEffects
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

/-- Successful indirect-call checking exposes the actual function/table metadata
and full parameter/result transfer, before any compiler callback. -/
theorem indirect_call_effect (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (outer segment : List code.StackType)
    (hvals : st.core.vals.val = outer ++ segment)
    (hbase : (Control.base st.core).val = outer.length) :
    code.call st data env .Wasm2 true ⦃ r => r.1 = .Ok () →
      ∃ (idx table : U32) (middle : Usize) (ft : types.FuncType) (tt : types.TableType) (rest : List code.StackType),
        Leb128.Decoded data st.core.pos idx middle ∧ Leb128.Decoded data middle table r.2.core.pos ∧
        env.types.val[idx.val]? = some ft ∧ env.table_types.val[table.val]? = some tt ∧ tt.elem = .FuncRef ∧
        r.2.core.vals.val = outer ++ (rest ++ ft.results.val.map code.StackType.Val) ∧
        (∀ ts, Sequence.Realizes (Control.polymorphic st.core) rest ts →
          Sequence.Realizes (Control.polymorphic st.core) segment
            (ts ++ (ft.params.val.map Translate.valueType ++ [.I32]))) ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases r with
  | Err e => simp [code.call, code.call_indirect_info, code.check_table_byte, code.take_index, hr,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨idx, middle⟩ := pair
    obtain ⟨rtable, hreadtable, hdtable⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data middle)
    cases rtable with
    | Err e => simp [code.call, code.call_indirect_info, code.check_table_byte, code.take_index, hr, hreadtable,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨table, next⟩ := pair
      by_cases htable : table.val < env.table_types.val.length
      · have htix : (UScalar.cast .Usize table).val < env.table_types.val.length := by simpa using htable
        obtain ⟨tt, hget, hgeteq⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec env.table_types (UScalar.cast .Usize table) htix)
        have htt : env.table_types.val[table.val] = tt := by simpa using hgeteq.symm
        have htablesmall := Nat.not_le_of_gt htable
        cases helem : tt.elem with
        | ExternRef =>
          simp [code.call, code.call_indirect_info, code.check_table_byte, code.take_index, hr, hreadtable, lift,
            htablesmall, hget, helem, Itasca.types.ElemType.value_type,
            core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
            Itasca.types.ValueType.Insts.CoreCmpPartialEqValueType.eq,
            core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | FuncRef =>
          have hfun : env.table_types.val[table.val].elem = .FuncRef := by rw [htt]; exact helem
          by_cases hi : idx.val < env.types.val.length
          · have hix : (UScalar.cast .Usize idx).val < env.types.val.length := by simpa using hi
            obtain ⟨ft, hft, heq⟩ := WP.spec_imp_exists
              (alloc.vec.Vec.index_usize_spec env.types (UScalar.cast .Usize idx) hix)
            have htype : env.types.val[idx.val] = ft := by simpa using heq.symm
            have hsmall := Nat.not_le_of_gt hi
            obtain ⟨⟨rc, sc⟩, hcond, hcc, hpc, condrest, hvc, _, htc⟩ := WP.spec_imp_exists
              (code.pop_with_type.realizes { st.core with pos := next } outer segment .I32 hvals hbase)
            dsimp only at hcc hpc hvc htc
            cases rc with
            | Err e =>
              simp [code.call, code.call_indirect_info, code.check_table_byte, code.take_index, hr, hreadtable, lift,
                htablesmall, hget, helem, Itasca.types.ElemType.value_type,
                core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                Itasca.types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok popped =>
              obtain ⟨⟨res, s⟩, hs, hout⟩ := WP.spec_imp_exists
                (code.apply_func_type.realizes sc ft outer condrest hvc
                  (by simpa [Control.base, hcc] using hbase))
              cases res with
              | Err e =>
                simp [code.call, code.call_indirect_info, code.check_table_byte, code.take_index, hr, hreadtable, lift,
                  htablesmall, hget, helem, Itasca.types.ElemType.value_type,
                  core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                  Itasca.types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond, hft, hs,
                  core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok u =>
                obtain ⟨hc, hp, _, _, rest, hv, _, ht⟩ := hout rfl
                dsimp only at hc hp hv ht
                have htransfer : ∀ ts, Sequence.Realizes (Control.polymorphic st.core) rest ts →
                    Sequence.Realizes (Control.polymorphic st.core) segment
                      (ts ++ (ft.params.val.map Translate.valueType ++ [.I32])) := by
                  intro ts hts
                  have hparam := ht ts (by simpa [Control.polymorphic, hcc] using hts)
                  have hargs := htc.2 _ (by simpa [Control.polymorphic, hcc] using hparam)
                  simpa [Translate.valueType, List.append_assoc, Control.polymorphic] using hargs
                rw [WP.spec_equiv_exists]
                refine ⟨(.Ok (), ⟨s⟩), ?_, fun _ => ?_⟩
                · simp [code.call, code.call_indirect_info, code.check_table_byte, code.take_index, hr, hreadtable, lift,
                    htablesmall, hget, helem, Itasca.types.ElemType.value_type,
                    core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
                    Itasca.types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hsmall, hcond, hft, hs,
                    core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                · refine ⟨idx,table,middle,ft,tt,rest,hd,?_,?_,?_,helem,hv,htransfer⟩
                  · simpa [Leb128.Post,hp,hpc] using hdtable
                  · simpa [List.getElem?_eq_getElem hi] using congrArg some htype
                  · simpa [List.getElem?_eq_getElem htable] using congrArg some htt
          · have hlarge := Nat.le_of_not_gt hi
            simp [code.call, code.call_indirect_info, code.check_table_byte, code.take_index, hr, hreadtable, lift,
              htablesmall, hget, helem, Itasca.types.ElemType.value_type,
              core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
              Itasca.types.ValueType.Insts.CoreCmpPartialEqValueType.eq, hlarge,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · have hlarge := Nat.le_of_not_gt htable
        simp [code.call, code.call_indirect_info, code.check_table_byte, code.take_index, hr, hreadtable, lift,
          hlarge, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Concrete live stacks and the actual reader determine the complete indirect
call signature and operand/result suffixes. -/
theorem reader_indirect_call_stack_wasm2 (st out : code.BodyState) (data : Slice U8) (env : module.Env)
    (index table : U32) (outer segment : List code.StackType)
    (values : st.core.vals.val = outer ++ segment) (base : (Control.base st.core).val = outer.length)
    (known : ConcreteStack st.core.vals.val) (monomorphic : Control.polymorphic st.core = false)
    (shape : Control.Shape st.core)
    (accepted : code.call_indirect_info st data env .Wasm2 = .ok (.Ok (index,table),out)) :
    ∃ (ft : types.FuncType) (tt : types.TableType) (front : List types.ValueType),
      env.types.val[index.val]? = some ft ∧ env.table_types.val[table.val]? = some tt ∧ tt.elem = .FuncRef ∧
      Sequence.stackTypes st.core.vals.val = (front.map Translate.valueType ++ ft.params.val.map Translate.valueType) ++ [.I32] ∧
      out.core.vals.val = (front ++ ft.results.val).map code.StackType.Val := by
  have erased : code.call st data env .Wasm2 true = .ok (.Ok (),out) := by
    simp [code.call,accepted,core.result.Result.Insts.CoreOpsTry.branch]
  have effect := indirect_call_effect st data env outer segment values base
  rw [erased,WP.spec_ok] at effect
  obtain ⟨idx,tab,middle,ft,tt,rest,decoded,decodedTable,typeFound,tableFound,elem,afterValues,transfer⟩ := effect rfl
  dsimp only at decoded decodedTable afterValues
  have info := code.call_indirect_info.bytes st data env .Wasm2 shape
  rw [accepted,WP.spec_ok] at info
  obtain ⟨middle',indexBytes,tableBytes⟩ := info index table rfl
  obtain ⟨rfl,rfl⟩ := Leb128.Decoded.deterministic data st.core.pos index idx middle' middle indexBytes decoded
  obtain ⟨rfl,_⟩ := Leb128.Decoded.deterministic data middle' table tab out.core.pos out.core.pos tableBytes decodedTable
  rw [monomorphic] at transfer
  obtain ⟨front,beforeTypes,afterConcrete⟩ := call_full_stack_types (ft.params.val ++ [.I32]) ft.results.val known values afterValues
    (by simpa [List.map_append,Translate.valueType] using transfer)
  refine ⟨ft,tt,front,typeFound,tableFound,elem,?_,afterConcrete⟩
  simpa [List.map_append,Translate.valueType,List.append_assoc] using beforeTypes
end Itasca.Runtime.Code
