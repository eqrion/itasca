import Itasca.Generated.FunsInstantiate
import Itasca.Runtime.Store.Initialization.ElementLoop
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Module.Const.Parser
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Store.Preparation.Staging
import Itasca.Runtime.Compiler.Local.Initializer

/-!
Sections, each formerly its own module: InitializerSource, InitializerSourceContext, Data.
-/

/-! ## InitializerSource -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

private theorem eval_literal (s : _root_.store) (f : frame) (instruction : instr) (value : val)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (valueWf : wf_val value) (same : admininstr_instr instruction = admininstr_val value) :
    Eval_expr ⟨s, f⟩ [instruction] ⟨s, f⟩ [value] := by
  have wf := Itasca.Runtime.Spec.wf_config_vals (vs := [value]) storeWf frameWf (by simpa [Forall] using valueWf)
  simp only [SpecExt.vals, List.map_cons, List.map_nil] at wf
  apply Eval_expr.mk_Eval_expr
  · simpa only [Map, List.map_cons, List.map_nil, same] using Steps.refl _ _ wf
  · simpa only [Map, List.map_cons, List.map_nil, same] using wf
  · exact wf

private theorem eval_read (s : _root_.store) (f : frame) (instruction : instr) (value : val)
    (storeWf : wf_store s) (frameWf : wf_frame f)
    (instructionWf : wf_instr instruction) (valueWf : wf_val value)
    (read : Step_read ⟨⟨s, f⟩, [admininstr_instr instruction]⟩ [admininstr_val value]) :
    Eval_expr ⟨s, f⟩ [instruction] ⟨s, f⟩ [value] := by
  have before := Itasca.Runtime.Spec.wf_config_make storeWf frameWf
    (show Forall wf_admininstr [admininstr_instr instruction] by
      simpa [Forall] using Itasca.Runtime.Spec.wf_admininstr_instr instructionWf)
  have after := Itasca.Runtime.Spec.wf_config_make storeWf frameWf
    (show Forall wf_admininstr [admininstr_val value] by
      simpa [Forall] using Itasca.Runtime.Spec.wf_admininstr_val valueWf)
  exact .mk_Eval_expr _ _ _ _
    (.trans _ _ _ _ _ _ (.read _ _ _ read before after) (.refl _ _ after) before after after) before after

private theorem float_value_32 (bits : U32) :
    SpecExt.Builtins.floatOfBits 32 bits.val = ScalarConst.floatValue 23 8 bits.val := by
  have bound : bits.val < 2^32 := by scalar_tac
  have sign : (bits.val / 2^31) % 2 = 0 ↔ bits.val < 2^31 := by omega
  norm_num at sign
  simp [SpecExt.Builtins.floatOfBits, ScalarConst.floatValue, fun_M, E, signif, expon,
    SpecExt.Builtins.floatBias, sign]

private theorem float_value_64 (bits : U64) :
    SpecExt.Builtins.floatOfBits 64 bits.val = ScalarConst.floatValue 52 11 bits.val := by
  have bound : bits.val < 2^64 := by scalar_tac
  have sign : (bits.val / 2^63) % 2 = 0 ↔ bits.val < 2^63 := by omega
  norm_num at sign
  simp [SpecExt.Builtins.floatOfBits, ScalarConst.floatValue, fun_M, E, signif, expon,
    SpecExt.Builtins.floatBias, sign]

/-- Resolved initializer operands evaluate under the generated source rules.
This connects the runtime's exact literal/global/reference words to Eval_expr,
without a source execution premise. -/
theorem initializer_resolution_source_in_state {M : Type}
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (expression : wasm_types.ConstExpr) (ty : wasm_types.ValueType) (words : List U64)
    (resolved : Interp.InitializerResolution store inst expression ty words)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (functions : sourceInstance.FUNCS = inst.funcs.val.map (fun address => address.index.val))
    (globals : ∀ index address global, expression = .GlobalGet index →
      inst.globals.val[index.val]? = some address → store.globals.val[address.index.val]? = some global →
      fun_global ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (.mk_uN index.val) = decodeGlobal global)
    (storeWf : wf_store sourceStore)
    (frameWf : wf_frame ⟨[], sourceInstance⟩) :
    Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩
      (ModuleConstants.expression expression)
      ⟨sourceStore, ⟨[], sourceInstance⟩⟩
      [decodeWords ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)] := by
  have outputWf := decode_words_wf ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)
  have inputWf := ModuleConstants.instruction_wf expression
  cases resolved with
  | i32 value =>
    apply eval_literal _ _ _ _ storeWf frameWf outputWf
    simp only [ModuleConstants.instruction, Spec.i32Const, admininstr_instr, admininstr_val,
      decodeWords, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.getD_some, Option.getD_none]
    congr 3
    have modulus : (value.val % 4294967296).toNat < 4294967296 := by
      have bound := Int.emod_lt_of_pos value.val (by decide : (0 : Int) < 4294967296)
      omega
    simp [UScalar.cast_val_eq, IScalar.hcast_val_eq, Nat.mod_eq_of_lt modulus]
  | i64 value =>
    apply eval_literal _ _ _ _ storeWf frameWf outputWf
    simp [ModuleConstants.instruction, ScalarConst.i64, admininstr_instr, admininstr_val,
      decodeWords, IScalar.hcast_val_eq]
  | f32 bits =>
    apply eval_literal _ _ _ _ storeWf frameWf outputWf
    have exactBits : (UScalar.cast .U64 bits).val % 2^32 = bits.val := by scalar_tac
    simp [ModuleConstants.instruction, ScalarConst.f32, admininstr_instr, admininstr_val,
      decodeWords, exactBits, float_value_32]
  | f64 bits =>
    apply eval_literal _ _ _ _ storeWf frameWf outputWf
    simp [ModuleConstants.instruction, ScalarConst.f64, admininstr_instr, admininstr_val,
      decodeWords, float_value_64]
  | vector lo hi =>
    apply eval_literal _ _ _ _ storeWf frameWf outputWf
    simp [ModuleConstants.instruction, admininstr_instr, admininstr_val, decodeWords, Nat.mul_comm]
  | nullFunc =>
    apply eval_literal _ _ _ _ storeWf frameWf outputWf
    rfl
  | nullExtern =>
    apply eval_literal _ _ _ _ storeWf frameWf outputWf
    rfl
  | func index address reference lookup encoded =>
    have value : decodeWords .FuncRef reference 0#u64 = .REF_FUNC_ADDR address.index.val := by
      simp [decodeWords, decodeRef, encoded, refVal]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.getD_some, Option.getD_none] at outputWf ⊢
    rw [value] at outputWf ⊢
    apply eval_read _ _ _ _ storeWf frameWf inputWf outputWf
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    have fetched : (fun_funcaddr ⟨sourceStore, ⟨[], sourceInstance⟩⟩)[index.val]! = address.index.val := by
      simp [fun_funcaddr, functions, List.getElem!_eq_getElem?_getD, List.getElem?_map, lookup]
    simpa only [ModuleConstants.instruction, admininstr_instr, admininstr_val, proj_uN_0, fetched] using
      (Step_read.ref_func ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (.mk_uN index.val)
        (by simpa [fun_funcaddr, functions, proj_uN_0] using bound)
        (Itasca.Runtime.Spec.wf_config_make storeWf frameWf (by
          simpa [Forall, ModuleConstants.instruction, admininstr_instr] using Itasca.Runtime.Spec.wf_admininstr_instr inputWf))
        (by simp only [proj_uN_0, fetched]; constructor))
  | global ty index address global lookup found typed scalar =>
    have value : decodeWords ty global.lo 0#u64 = (decodeGlobal global).VALUE := by
      cases ty <;> simp_all [decodeGlobal, decodeWords]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.getD_some, Option.getD_none] at outputWf ⊢
    rw [value] at outputWf ⊢
    apply eval_read _ _ _ _ storeWf frameWf inputWf outputWf
    have fetched : fun_global ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (.mk_uN index.val) = decodeGlobal global := by
      exact globals index address global rfl lookup found
    simpa only [ModuleConstants.instruction, admininstr_instr, fetched] using
      (Step_read.global_get ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (.mk_uN index.val)
        (Itasca.Runtime.Spec.wf_config_make storeWf frameWf (by simpa [Forall, ModuleConstants.instruction, admininstr_instr] using Itasca.Runtime.Spec.wf_admininstr_instr inputWf)))
  | global2 index address global lookup found typed =>
    have value : decodeWords .V128 global.lo global.hi = (decodeGlobal global).VALUE := by
      simp [decodeGlobal, typed]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at outputWf ⊢
    rw [value] at outputWf ⊢
    apply eval_read _ _ _ _ storeWf frameWf inputWf outputWf
    have fetched : fun_global ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (.mk_uN index.val) = decodeGlobal global := by
      exact globals index address global rfl lookup found
    simpa only [ModuleConstants.instruction, admininstr_instr, fetched] using
      (Step_read.global_get ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (.mk_uN index.val)
        (Itasca.Runtime.Spec.wf_config_make storeWf frameWf (by simpa [Forall, ModuleConstants.instruction, admininstr_instr] using Itasca.Runtime.Spec.wf_admininstr_instr inputWf)))

/-- The ordinary runtime state is a direct instance of the source-state bridge. -/
theorem initializer_resolution_source {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (expression : wasm_types.ConstExpr) (ty : wasm_types.ValueType) (words : List U64)
    (resolved : Interp.InitializerResolution store inst expression ty words)
    (storeWf : wf_store (decodeStore view code store))
    (frameWf : wf_frame ⟨[], decodeInstance store inst⟩) :
    Eval_expr ⟨decodeStore view code store, ⟨[], decodeInstance store inst⟩⟩
      (ModuleConstants.expression expression)
      ⟨decodeStore view code store, ⟨[], decodeInstance store inst⟩⟩
      [decodeWords ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)] := by
  apply initializer_resolution_source_in_state store inst expression ty words resolved
    (decodeStore view code store) (decodeInstance store inst) rfl ?_ storeWf frameWf
  intro index address global _ lookup found
  simp [fun_global, proj_uN_0, decodeStore, decodeInstance, List.getElem!_eq_getElem?_getD,
    List.getElem?_map, lookup, found]
end Itasca.Runtime.Store

end

/-! ## InitializerSourceContext -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

/-- The source initial frame reads the same imported globals and function
addresses as the staged runtime instance. Defined globals are not in the
constant-expression typing context. -/
structure InitializerSourceContext {M : Type} (sourceStore : _root_.store)
    (sourceInstance : moduleinst) (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) : Prop where
  functions : sourceInstance.FUNCS = inst.funcs.val.map (fun address => address.index.val)
  globals : ∀ (index : U32) address global,
    index.val < inst.module.module.env.global_types.val.length →
    index.val < inst.module.module.env.num_imported_globals.val →
    inst.globals.val[index.val]? = some address →
    store.globals.val[address.index.val]? = some global →
    fun_global ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (.mk_uN index.val) = decodeGlobal global

theorem InitializerSourceContext.expression {M : Type} {sourceStore sourceInstance}
    {store : runtime.store.Store M} {inst expr ty words}
    (context : InitializerSourceContext sourceStore sourceInstance store inst)
    (valid : ModuleConstants.Valid inst.module.module.env expr ty)
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩) :
    Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (ModuleConstants.expression expr)
      ⟨sourceStore, ⟨[], sourceInstance⟩⟩
      [decodeWords ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)] := by
  apply initializer_resolution_source_in_state store inst expr ty words resolved
    sourceStore sourceInstance context.functions ?_ storeWf frameWf
  intro index address global equal mapped found
  subst expr
  cases valid with
  | globalGet _ _ typedBound _ imported _ => exact context.globals index address global typedBound imported mapped found

/-- Earlier source lookups are unchanged when only defined globals append. -/
theorem InitializerSourceContext.extend {M : Type} {sourceStore sourceInstance}
    {before after : runtime.store.Store M} {old next : runtime.store.ModuleInst}
    (context : InitializerSourceContext sourceStore sourceInstance before old)
    (imports : InitializerImports before old)
    (source : next.module = old.module) (functions : next.funcs = old.funcs)
    (globalMap : next.globals.val.take old.globals.length = old.globals.val)
    (globals : after.globals.val.take before.globals.length = before.globals.val) :
    InitializerSourceContext sourceStore sourceInstance after next := by
  refine ⟨by simpa [functions] using context.functions, ?_⟩
  intro index address global typedBound imported mapped found
  rw [source] at typedBound imported
  obtain ⟨oldAddress, oldGlobal, oldMapped, oldFound, _⟩ := imports.globals index
    old.module.module.env.global_types.val[index.val] (List.getElem?_eq_getElem typedBound) imported
  have mapBound := (List.getElem?_eq_some_iff.mp oldMapped).1
  have mapRetained := oldMapped
  rw [← globalMap, List.getElem?_take, if_pos mapBound] at mapRetained
  have sameAddress : oldAddress = address := Option.some.inj (mapRetained.symm.trans mapped)
  subst oldAddress
  have globalBound := (List.getElem?_eq_some_iff.mp oldFound).1
  have globalRetained := oldFound
  rw [← globals, List.getElem?_take, if_pos globalBound] at globalRetained
  have sameGlobal : oldGlobal = global := Option.some.inj (globalRetained.symm.trans found)
  subst oldGlobal
  exact context.globals index address global typedBound imported oldMapped oldFound

/-- Preparation has not changed global contents; its imported address map is
exactly the initial source frame's global namespace. -/
theorem InitializerSourceContext.of_maps {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (before store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (sourceInstance : moduleinst)
    (functions : sourceInstance.FUNCS = inst.funcs.val.map (fun address => address.index.val))
    (addresses : sourceInstance.GLOBALS = inst.globals.val.map (fun address => address.index.val))
    (globals : store.globals = before.globals) :
    InitializerSourceContext (decodeStore view code before) sourceInstance store inst := by
  refine ⟨functions, ?_⟩
  intro index address global _ _ mapped found
  rw [globals] at found
  simp [fun_global, decodeStore, addresses, proj_uN_0,
    List.getElem!_eq_getElem?_getD, List.getElem?_map, mapped, found]
end Itasca.Runtime.Store

end

/-! ## Data -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

@[step] theorem copy_bytes_loop (source : Slice U8) (bytes : alloc.vec.Vec U8)
    (i : Usize) (hi : i.val ≤ source.length) (hprefix : bytes.val = source.val.take i.val) :
    runtime.store.copy_bytes_loop source bytes i ⦃ after => after.val = source.val ⦄ := by
  unfold runtime.store.copy_bytes_loop
  apply loop.spec_decr_nat (fun pair => source.length - pair.2.val)
    (fun pair => pair.2.val ≤ source.length ∧ pair.1.val = source.val.take pair.2.val)
  · intro pair hinv
    rcases pair with ⟨bytes, i⟩
    rcases hinv with ⟨hi, hbytes⟩
    unfold runtime.store.copy_bytes_loop.body
    dsimp only at hi hbytes ⊢
    split
    · rename_i hmore
      have hib : i.val < source.length := by scalar_tac
      have hlen : bytes.length = i.val := by simp [hbytes, Nat.min_eq_left hi]
      have hmax : bytes.length < Usize.max := by scalar_tac
      step as ⟨value, hvalue⟩
      step as ⟨after, hafter⟩
      step as ⟨next, hnext⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hafter, hbytes, hnext, List.take_succ_eq_append_getElem hib, hvalue]
    · rename_i hstop
      have heq : i.val = source.length := by scalar_tac
      simpa [heq] using hbytes
  · exact ⟨hi, hprefix⟩

@[step] theorem copy_bytes_spec {A : Type} (allocator : runtime.platform.Alloc A)
    (ha : Platform.AllocCorrect allocator) (source : Slice U8) :
    runtime.store.copy_bytes allocator source ⦃ answer =>
      answer = .Err (.Exhausted .Allocation) ∨ ∃ bytes, answer = .Ok bytes ∧ bytes.val = source.val ⦄ := by
  unfold runtime.store.copy_bytes
  dsimp only
  obtain ⟨reserved, hr⟩ := reserve_wrapper_eq allocator ha (alloc.vec.Vec.new U8) (Slice.len source)
  rw [hr]
  cases reserved
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch]
    step with copy_bytes_loop source (alloc.vec.Vec.new U8) 0#usize (by scalar_tac) (by simp) as ⟨bytes, hbytes⟩
    simp [hbytes]

/-- A data segment is copied byte for byte and receives its current store index.
Failures do not change the store; success changes only that data vector and the
selected provisional instance's data-address map. -/
theorem add_instance_data_effect {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (instanceIndex i : Usize)
    (hinstance : instanceIndex.val < s.instances.length)
    (hi : i.val < (s.instances.val[instanceIndex.val]).module.module.tail.data.length)
    (hroom : s.datas.length < Usize.max)
    (hmaproom : (s.instances.val[instanceIndex.val]).datas.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_data ops allocator s instanceIndex i ⦃ result =>
      (∃ error, result = (.Err error, s)) ∨
      ∃ bytes : alloc.vec.Vec U8, ∃ datas : alloc.vec.Vec runtime.store.DataInst,
      ∃ addresses : alloc.vec.Vec Usize,
        bytes.val = (s.instances.val[instanceIndex.val]).module.module.tail.data.val[i.val].init.val ∧
        datas.val = s.datas.val ++ [⟨bytes⟩] ∧
        addresses.val = (s.instances.val[instanceIndex.val]).datas.val ++ [alloc.vec.Vec.len s.datas] ∧
        result = (.Ok (), {s with datas := datas, instances := s.instances.set instanceIndex {(s.instances.val[instanceIndex.val]) with datas := addresses}}) ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_data
  step as ⟨inst, hinst⟩
  simp only [runtime.compiler.ExecutableModule.tail.eq,
    Itasca.metadata.Module.impl.tail, bind_ok]
  have hd : i.val < inst.module.module.tail.data.length := by simpa [hinst] using hi
  step as ⟨data, hdata⟩
  step with copy_bytes_spec allocator ha data.init.deref as ⟨copied, hcopied⟩
  rcases hcopied with herr | ⟨bytes, hok, hbytes⟩
  · simp [herr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · rw [hok]
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨reserved, hr⟩ := reserve_wrapper_eq allocator ha s.datas 1#usize
    rw [hr]
    cases reserved
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · simp [core.result.Result.Insts.CoreOpsTry.branch]
      step as ⟨datas, hdatas⟩
      step as ⟨inst', back, hinst', hback⟩
      have hm : inst'.datas.length < Usize.max := by simpa [hinst'] using hmaproom
      step as ⟨addresses, haddresses⟩
      right
      refine ⟨bytes, ?_, datas, hdatas, addresses, ?_, ?_⟩
      · simpa [hdata, hinst, alloc.vec.Vec.deref] using hbytes
      · simpa [hinst'] using haddresses
      · simp [hback, hinst']

end Itasca.Runtime.Store

end
