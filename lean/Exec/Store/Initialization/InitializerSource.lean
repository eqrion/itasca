import Exec.Store.Initialization.Initializer
import Exec.Store.Invariant.Syntax
import Itasca.Module.Const.Syntax
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
    (expression : types.ConstExpr) (ty : types.ValueType) (words : List U64)
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
  have outputWf := decodeWords_wf ty ((words[0]?).getD 0#u64) ((words[1]?).getD 0#u64)
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
    (expression : types.ConstExpr) (ty : types.ValueType) (words : List U64)
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
