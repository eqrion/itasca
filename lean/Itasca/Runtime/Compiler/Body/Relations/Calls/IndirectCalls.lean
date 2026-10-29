import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallEffects
import Itasca.Runtime.Compiler.Body.Relations.Entry.EntrySignatures
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallOperands
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallEmission

/-!
Indirect-call signature selection, callback effects and lowering certificates used by reader replay.
-/

/-! ## Indirect Call Effects -/

section

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

end

/-! ## Indirect Call Signature -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- The captured table supplies an actual readable signature at every canonical
source type index; its parameter width is derived from the captured sequence. -/
theorem SignatureSequence.indirect_call {signatures : Slice runtime.compiler.Signature}
    {types : List Itasca.types.FuncType} (sequence : SignatureSequence signatures.val types)
    (index : U32) (params results : List valtype)
    (source : (types.map Itasca.EnvTranslation.funcType)[index.val]? = some ⟨.mk_list params,.mk_list results⟩) :
    ∃ signature, Slice.index_usize signatures (UScalar.cast .Usize index) = .ok signature ∧
      SignatureMatches signature params results := by
  have inBounds : index.val < types.length := by
    have found := (List.getElem?_eq_some_iff.mp source).1
    simpa using found
  have signatureBound : index.val < signatures.val.length := by
    rw [List.Forall₂.length_eq sequence]; exact inBounds
  let signature := signatures.val[index.val]
  have found : signatures.val[index.val]? = some signature := List.getElem?_eq_getElem signatureBound
  obtain ⟨input,output,lookup,matched⟩ := sequence.table index.val signature found
  have same : params = input ∧ results = output := by
    rw [source] at lookup
    simpa only [Option.some.injEq,functype.mk_functype.injEq,list.mk_list.injEq] using lookup
  obtain ⟨r,read,result⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec signatures (UScalar.cast .Usize index) (by simpa using signatureBound))
  refine ⟨signature,?_,?_⟩
  · have equal : r = signature := by simpa [signature] using result
    simpa only [equal] using read
  · simpa only [same.1,same.2] using matched
end Itasca.Runtime.Code

end

/-! ## Indirect Call Lowered -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Successful indirect-call lowering appends the exact table/type pair and
emits the source-determined selector and argument coordinates. -/
theorem compiler_indirect_call_emission {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (C : context) (front params results : List valtype) (typeIndex tableIndex : U32)
    (bounds : limits) (signature : runtime.compiler.Signature)
    (signatureFound : C.TYPES[typeIndex.val]? = some ⟨.mk_list params,.mk_list results⟩)
    (tableFound : C.TABLES[tableIndex.val]? = some (.mk_tabletype bounds .FUNCREF))
    (read : Slice.index_usize before.signatures (UScalar.cast .Usize typeIndex) = .ok signature)
    (parameterWidth : signature.param_slots.val = slots params)
    (locals : C.LOCALS = compilerLocals before)
    (layout : CompilerLayout before ((front ++ params) ++ [.I32]))
    (reachable : before.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ results)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 typeIndex tableIndex 0#u128 = .ok (.Ok (),after)) :
    after.function.indirect.val = before.function.indirect.val ++ [(tableIndex,typeIndex)] ∧
    ∃ instruction, Lowered before after instruction (front ++ results) ∧
      IndirectCallEmission after.function.indirect.val C ((front ++ params) ++ [.I32])
        (.CALL_INDIRECT (.mk_uN tableIndex.val) (.mk_uN typeIndex.val)) [instruction] (front ++ results) := by
  obtain ⟨total,base,added,subtracted,basePosition⟩ := indirect_call_arithmetic before front params signature layout parameterWidth
  obtain ⟨entry,paired,pairRun⟩ := lower_indirect_call_pair_success ops before after state typeIndex tableIndex total base
    signature reachable read added subtracted accepted
  obtain ⟨budget,pairs,pairedEq,pairsEq,indexEq⟩ := compiler_pair_success ops law before paired tableIndex typeIndex entry pairRun
  subst paired
  let paired := {before with budget, function := {before.function with indirect := pairs}}
  have pairedLayout : CompilerLayout paired ((front ++ params) ++ [.I32]) :=
    ⟨layout.localSlots,layout.localOffsets,layout.operandOffsets,layout.height,layout.capacity⟩
  obtain ⟨index,operand,indexPosition⟩ := indirect_call_operand ops paired front params pairedLayout
  rw [lower_indirect_call_eq ops before paired state typeIndex tableIndex total base entry index signature
    reachable read added subtracted pairRun operand] at accepted
  have lowered := finish_op ops law paired state types (.CallIndirect entry index base)
    _ pairedLayout concrete codeFits sourceFits coordinateFits
  rw [accepted,WP.spec_ok] at lowered
  have kept := compiler_finish_indirect ops law paired after state _ accepted
  have afterPairs : after.function.indirect.val = before.function.indirect.val ++ [(tableIndex,typeIndex)] := by
    rw [kept]; exact pairsEq
  refine ⟨afterPairs,.CallIndirect entry index base,?_,?_⟩
  · simpa only [typed,Lowered,paired,compilerLocals] using lowered rfl
  · apply IndirectCallEmission.call front params results typeIndex tableIndex entry index base bounds
      signatureFound tableFound
    · rw [afterPairs,indexEq]; simp
    · simpa only [locals] using basePosition
    · simp only [paired,compilerLocals] at indexPosition basePosition
      omega
/-- The public compiler-side constructor reads signature metadata from the actual
captured source sequence, rather than assuming a width or a successful lookup. -/
theorem compiler_indirect_call_emission_captured {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (sourceTypes : List Itasca.types.FuncType) (sequence : SignatureSequence before.signatures.val sourceTypes)
    (C : context) (contextTypes : C.TYPES = sourceTypes.map Itasca.EnvTranslation.funcType)
    (front params results : List valtype) (typeIndex tableIndex : U32) (bounds : limits)
    (signatureFound : C.TYPES[typeIndex.val]? = some ⟨.mk_list params,.mk_list results⟩)
    (tableFound : C.TABLES[tableIndex.val]? = some (.mk_tabletype bounds .FUNCREF))
    (locals : C.LOCALS = compilerLocals before)
    (layout : CompilerLayout before ((front ++ params) ++ [.I32]))
    (reachable : before.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ results)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 typeIndex tableIndex 0#u128 = .ok (.Ok (),after)) :
    after.function.indirect.val = before.function.indirect.val ++ [(tableIndex,typeIndex)] ∧
    ∃ instruction, Lowered before after instruction (front ++ results) ∧
      IndirectCallEmission after.function.indirect.val C ((front ++ params) ++ [.I32])
        (.CALL_INDIRECT (.mk_uN tableIndex.val) (.mk_uN typeIndex.val)) [instruction] (front ++ results) := by
  obtain ⟨signature,read,matched⟩ := sequence.indirect_call typeIndex params results (by simpa only [contextTypes] using signatureFound)
  exact compiler_indirect_call_emission ops law before after state types C front params results typeIndex tableIndex bounds
    signature signatureFound tableFound read matched.paramWords locals layout reachable concrete typed
    codeFits sourceFits coordinateFits accepted
end Itasca.Runtime.Code

end
